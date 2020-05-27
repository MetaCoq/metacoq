(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8
  ZArith Lia Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
     PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction PCUICSubstitution
     PCUICReflect PCUICClosed PCUICParallelReduction.

(* Type-valued relations. *)
Require Import CRelationClasses.
From Equations Require Import Equations.

Derive Signature for pred1 All2_local_env.

Local Set Keyed Unification.
Set Asymmetric Patterns.

Ltac solve_discr := (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  try discriminate.

Lemma simpl_pred Σ Γ Γ' t t' u u' : t = t' -> u = u' -> pred1 Σ Γ Γ' t' u' -> pred1 Σ Γ Γ' t u.
Proof. now intros -> ->. Qed.

Ltac simpl_pred :=
  eapply simpl_pred;
  rewrite ?up_Upn;
  unfold Upn, Up, idsn;
  [autorewrite with sigma; reflexivity|
    autorewrite with sigma; reflexivity|].

Lemma pred_atom_inst t σ : pred_atom t -> t.[σ] = t.
Proof.
  destruct t; simpl; intros; try discriminate; auto.
Qed.

Equations map_In {A B : Type} (l : list A) (f : ∀ (x : A), In x l → B) : list B :=
map_In nil _ := nil;
map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A → B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g); rewrite ?H; trivial.
Qed.

Section list_size.
  Context {A : Type} (f : A → nat).

  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size f xs).
  Proof.
    intros. induction xs.
    destruct H.
    * destruct H. simpl; subst. lia.
    specialize (IHxs H). simpl. lia.
  Qed.

End list_size.
Lemma size_mkApps f l : size (mkApps f l) = size f + list_size size l.
Proof.
  induction l in f |- *; simpl; try lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma list_size_app (l l' : list term) : list_size size (l ++ l') = list_size size l + list_size size l'.
Proof.
  induction l; simpl; auto.
  rewrite IHl. lia.
Qed.

Lemma mfixpoint_size_In {mfix d} :
  In d mfix ->
  size (dbody d) < mfixpoint_size size mfix /\
  size (dtype d) < mfixpoint_size size mfix.
Proof.
  induction mfix in d |- *; simpl; auto. intros [].
  move=> [->|H]. unfold def_size. split; lia.
  destruct (IHmfix d H). split; lia.
Qed.

Lemma mfixpoint_size_nth_error {mfix i d} :
  nth_error mfix i = Some d ->
  size (dbody d) < mfixpoint_size size mfix.
Proof.
  induction mfix in i, d |- *; destruct i; simpl; try congruence.
  move=> [] ->. unfold def_size. lia.
  move/IHmfix. lia.
Qed.

Section FoldFix.
  Context (rho : context -> term -> term).
  Context (Γ : context).

  Fixpoint fold_fix_context acc m :=
    match m with
  | [] => acc
    | def :: fixd =>
      fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
    end.  
End FoldFix.

Lemma fold_fix_context_length f Γ l m : #|fold_fix_context f Γ l m| = #|m| + #|l|.
Proof.
  induction m in l |- *; simpl; auto. rewrite IHm. simpl. auto with arith.
Qed.

Fixpoint isFixLambda_app (t : term) : bool :=
match t with
| tApp (tFix _ _) _ => true
| tApp (tLambda _ _ _) _ => true 
| tApp f _ => isFixLambda_app f
| _ => false
end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
  induction t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_lambda na t1 t2 [] u).
  destruct IHt1.
  pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
  change (tApp (mkApps (tFix mfix i) l) t2) with (mkApps (mkApps (tFix mfix i) l) [t2]).
  now rewrite mkApps_nested.
  pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
  change (tApp (mkApps (tLambda na ty b) l) t2) with (mkApps (mkApps (tLambda na ty b) l) [t2]).
  now rewrite mkApps_nested.
  destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_fix mfix idx [] u).
Defined.

Lemma eq_pair_transport {A B} (x y : A) (t : B y) (eq : x = y) : 
  (x; eq_rect_r (fun x => B x) t eq) = (y; t) :> ∑ x, B x. 
Proof.
  destruct eq. unfold eq_rect_r. now simpl.
Qed.

Lemma view_lambda_fix_app_fix_app_sigma mfix idx l a : 
  ((mkApps (tFix mfix idx) l); view_lambda_fix_app (mkApps (tFix mfix idx) l) a) =   
  ((mkApps (tFix mfix idx) l); fix_lambda_app_fix mfix idx l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tFix mfix idx) l) x) with (mkApps (mkApps (tFix mfix idx) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Lemma view_lambda_fix_app_lambda_app_sigma na ty b l a : 
  ((mkApps (tLambda na ty b) l); view_lambda_fix_app (mkApps (tLambda na ty b) l) a) =   
  ((mkApps (tLambda na ty b) l); fix_lambda_app_lambda na ty b l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tLambda na ty b) l) x) with (mkApps (mkApps (tLambda na ty b) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Set Equations With UIP.

Lemma view_lambda_fix_app_fix_app mfix idx l a : 
  view_lambda_fix_app (mkApps (tFix mfix idx) l) a =   
  fix_lambda_app_fix mfix idx l a.
Proof.
  pose proof (view_lambda_fix_app_fix_app_sigma mfix idx l a).
  now noconf H.
Qed.

Lemma view_lambda_fix_app_lambda_app na ty b l a : 
  view_lambda_fix_app (mkApps (tLambda na ty b) l) a =   
  fix_lambda_app_lambda na ty b l a.
Proof.
  pose proof (view_lambda_fix_app_lambda_app_sigma na ty b l a).
  now noconf H.
Qed.

Hint Rewrite view_lambda_fix_app_fix_app view_lambda_fix_app_lambda_app : rho.

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

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct c u i : construct_cofix_view (tConstruct c u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

(** This induction principle gives a general induction hypothesis for applications,
    allowing to apply the induction to their head. *)  
Lemma term_ind_size_app : 
  forall (P : term -> Type),
    (forall (n : nat), P (tRel n)) ->
    (forall (i : ident), P (tVar i)) ->
    (forall (n : nat) (l : list term), All (P) l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 ->
                                                   P (tLetIn n t t0 t1)) ->
    (forall (t u : term),
        (forall t', size t' < size (tApp t u) -> P t') ->
        P t -> P u -> P (tApp t u)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp (P) l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp (P) P m -> P (tCoFix m n)) ->
    forall (t : term), P t.
Proof.
  intros.
  revert t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (precompose lt size). simpl. clear H0.
  assert (auxl : forall {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr1 ->
                                                            All (fun x => P (f x)) l).
  { induction l; constructor. eapply aux. red. simpl in H. lia. apply IHl. simpl in H. lia. }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top.

  !destruct pr1; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  eapply X12; try (apply aux; red; simpl; lia).
  red. apply All_pair. split; apply auxl; simpl; auto.

  eapply X13; try (apply aux; red; simpl; lia).
  red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

Lemma fix_context_gen_assumption_context k Γ : assumption_context (fix_context_gen k Γ).
Proof.
  rewrite /fix_context_gen. revert k.
  induction Γ using rev_ind.
  constructor. intros.
  rewrite mapi_rec_app /= List.rev_app_distr /=. constructor.
  apply IHΓ.
Qed.

Lemma fix_context_assumption_context m : assumption_context (fix_context m).
Proof. apply fix_context_gen_assumption_context. Qed.

Lemma nth_error_assumption_context Γ n d :
  assumption_context Γ -> nth_error Γ n = Some d ->
  decl_body d = None.
Proof.
  intros H; induction H in n, d |- * ; destruct n; simpl; try congruence; eauto.
  now move=> [<-] //.
Qed.

Lemma decompose_app_rec_rename r t l :
  forall hd args, 
  decompose_app_rec t l = (hd, args) ->
  decompose_app_rec (rename r t) (map (rename r) l) = (rename r hd, map (rename r) args).
Proof.
  induction t in l |- *; simpl; try intros hd args [= <- <-]; auto.
  intros hd args e. now apply (IHt1 _ _ _ e).
Qed.

Lemma decompose_app_rename {r t hd args} :
  decompose_app t = (hd, args) ->
  decompose_app (rename r t) = (rename r hd, map (rename r) args).
Proof. apply decompose_app_rec_rename. Qed.

Lemma mkApps_eq_decompose_app {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  decompose_app_rec t l = decompose_app_rec t' l'.
Proof.
  induction l in t, t', l' |- *; simpl.
  - intros ->. rewrite !decompose_app_rec_mkApps.
    now rewrite app_nil_r.
  - intros H. apply (IHl _ _ _ H).
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
  repeat PCUICAstUtils.finish_discr ||
         match goal with
         | [ H : atom (mkApps _ _) |- _ ] => apply atom_mkApps in H; intuition subst
         | [ H : pred_atom (mkApps _ _) |- _ ] => apply pred_atom_mkApps in H; intuition subst
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

Ltac solve_discr ::=
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

Lemma is_constructor_app_ge n l l' : is_constructor n l -> is_constructor n (l ++ l').
Proof.
  unfold is_constructor. destruct nth_error eqn:Heq.
  rewrite nth_error_app_lt ?Heq //; eauto using nth_error_Some_length.
  discriminate.
Qed.

Lemma is_constructor_prefix n args args' : 
  ~~ is_constructor n (args ++ args') ->
  ~~ is_constructor n args.
Proof.
  rewrite /is_constructor.
  elim: nth_error_spec. rewrite app_length.
  move=> i hi harg. elim: nth_error_spec.
  move=> i' hi' hrarg'.
  rewrite nth_error_app_lt in hi; eauto. congruence.
  auto.
  rewrite app_length. move=> ge _.
  elim: nth_error_spec; intros; try lia. auto.
Qed.
    

Section Pred1_inversion.
  
  Lemma pred_snd_nth:
    ∀ (Σ : global_env) (Γ Δ : context) (c : nat) (brs1 brs' : list (nat * term)),
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

  Lemma pred_mkApps Σ Γ Δ M0 M1 N0 N1 :
    pred1 Σ Γ Δ M0 M1 ->
    All2 (pred1 Σ Γ Δ) N0 N1 ->
    pred1 Σ Γ Δ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma pred1_mkApps_tConstruct (Σ : global_env) (Γ Δ : context)
        ind pars k (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... simpl in H; noconf H. solve_discr.
    prepare_discr. apply mkApps_eq_decompose_app in H.
    rewrite !decompose_app_rec_mkApps in H. noconf H.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1])%list.
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_refl_tConstruct (Σ : global_env) Γ Δ i k u l l' :
    pred1 Σ Γ Δ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u) l') ->
    All2 (pred1 Σ Γ Δ) l l'.
  Proof.
    intros.
    eapply pred1_mkApps_tConstruct in X. destruct X.
    destruct p. now eapply mkApps_eq_inj in e as [_ <-].
  Qed.

  Lemma pred1_mkApps_tInd (Σ : global_env) (Γ Δ : context)
        ind u (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tInd ind u) args) c ->
    {args' : list term & (c = mkApps (tInd ind u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... simpl in H; noconf H. solve_discr.
    prepare_discr. apply mkApps_eq_decompose_app in H.
    rewrite !decompose_app_rec_mkApps in H. noconf H.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1])%list.
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tConst_axiom (Σ : global_env) (Γ Δ : context)
        cst u (args : list term) cb c :
    declared_constant Σ cst cb -> cst_body cb = None ->
    pred1 Σ Γ Δ (mkApps (tConst cst u) args) c ->
    {args' : list term & (c = mkApps (tConst cst u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X...
    - red in H, isdecl. rewrite isdecl in H; noconf H.
      simpl in H. injection H. intros. subst. congruence.
    - exists []. intuition auto.
    - rewrite <- mkApps_nested in X.
      depelim X...
      * simpl in H1; noconf H1. solve_discr.
      * prepare_discr. apply mkApps_eq_decompose_app in H1.
        rewrite !decompose_app_rec_mkApps in H1. noconf H1.
      * destruct (IHargs _ H H0 X1) as [args' [-> Hargs']].
        exists (args' ++ [N1])%list.
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tFix_inv Σ (Γ Δ : context)
        mfix0 idx (args0 : list term) c d :
    nth_error mfix0 idx = Some d ->
    ~~ is_constructor (rarg d) args0 ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                                       dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ Δ) ) args0 args1 } }%type).
  Proof with solve_discr.
    intros hnth isc pred. remember (mkApps _ _) as fixt.
    revert mfix0 idx args0 Heqfixt hnth isc.
    induction pred; intros; solve_discr.
    - unfold unfold_fix in e.
      red in a1.
      eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [ht' [hds [hr [= eqna eqrarg]]]]].
      rewrite ht' in e => //. noconf e. rewrite -eqrarg in e0.
      rewrite e0 in isc => //.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      specialize (IHpred1 hnth). apply is_constructor_prefix in isc.
      specialize (IHpred1 isc).
      destruct IHpred1 as [? [? [[? ?] ?]]].
      eexists _. eexists (_ ++ [N1])%list. rewrite <- mkApps_nested.
      intuition eauto. simpl. subst M1. reflexivity.
      eapply All2_app; eauto.
    - exists mfix1, []. intuition auto.
    - subst t. solve_discr.
  Qed.

  Lemma pred1_mkApps_tFix_refl_inv (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx0 idx1 (args0 args1 : list term) d :
    nth_error mfix0 idx0 = Some d ->
    is_constructor (rarg d) args0 = false ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx0) args0) (mkApps (tFix mfix1 idx1) args1) ->
    (All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                   dtype dbody
                   (fun x => (dname x, rarg x))
                   (pred1 Σ) mfix0 mfix1 *
     (All2 (pred1 Σ Γ Δ) ) args0 args1).
  Proof with solve_discr.
    intros Hnth Hisc.
    remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    intros pred. revert mfix0 mfix1 idx0 args0 d Hnth Hisc idx1 args1 Heqfixt Heqfixt'.
    induction pred; intros; solve_discr.
    - (* Not reducible *)
      red in a1. eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [Hnth' [Hty [Hpred Hann]]]].
      unfold unfold_fix in e. destruct (nth_error mfix1 idx) eqn:hfix1.
      noconf e. noconf Hnth'.
      move: Hann => [=] Hname Hrarg.
      all:congruence. 

    - destruct args0 using rev_ind; noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      destruct args1 using rev_ind; noconf Heqfixt'. clear IHargs1.
      rewrite <- mkApps_nested in Heqfixt'. noconf Heqfixt'.
      clear IHpred2.
      assert (is_constructor (rarg d) args0 = false).
      { move: Hisc. rewrite /is_constructor.
        elim: nth_error_spec. rewrite app_length.
        move=> i hi harg. elim: nth_error_spec.
        move=> i' hi' hrarg'.
        rewrite nth_error_app_lt in hi; eauto. congruence.
        auto.
        rewrite app_length. move=> ge _.
        elim: nth_error_spec; intros; try lia. auto.
      }
      specialize (IHpred1 _ _ _ _ _ Hnth H _ _ eq_refl eq_refl).
      destruct IHpred1 as [? ?]. red in a.
      unfold All2_prop2_eq. split. apply a. apply All2_app; auto.
    - constructor; auto.
    - subst. solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv (Σ : global_env) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) c ->
    ∑ mfix1 args1,
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

  Lemma pred1_mkApps_tCoFix_refl_inv (Σ : global_env) (Γ Δ : context)
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

End Pred1_inversion.

Hint Constructors pred1 : pcuic.

Section Rho.
  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

  #[program] Definition map_fix_rho {t} (rho : context -> forall x, size x < size t -> term) Γ mfixctx (mfix : mfixpoint term)
    (H : mfixpoint_size size mfix < size t) :=
    (map_In mfix (fun d (H : In d mfix) => {| dname := dname d; 
        dtype := rho Γ (dtype d) _;
        dbody := rho (Γ ,,, mfixctx) (dbody d) _; rarg := (rarg d) |})).
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    unfold def_size. lia.
    unfold mfixpoint_size in H0.
    lia.
  Qed.
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    unfold def_size. lia.
    unfold mfixpoint_size in H0.
    lia.
  Qed.

  Equations? fold_fix_context_wf mfix 
      (rho : context -> forall x, size x < (mfixpoint_size size mfix) -> term) 
      (Γ acc : context) : context :=
  fold_fix_context_wf [] rho Γ acc => acc ;
  fold_fix_context_wf (d :: mfix) rho Γ acc => 
    fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x _) Γ (vass (dname d) (lift0 #|acc| (rho Γ (dtype d) _)) :: acc).
  Proof.
    lia. unfold def_size. lia.        
  Qed.
  Transparent fold_fix_context_wf.

  #[program] Definition map_terms {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list term)
    (H : list_size size l < size t) :=
    (map_In l (fun t (H : In t l) => rho Γ t _)).
  Next Obligation.
    eapply (In_list_size size) in H. lia.
  Qed.

  #[program] Definition map_brs {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list (nat * term))
    (H : list_size (fun x : nat * term => size x.2) l < size t) :=
  (map_In l (fun x (H : In x l) => (x.1, rho Γ x.2 _))).
  Next Obligation.
    eapply (In_list_size (fun x => size x.2)) in H. simpl in *. lia.
  Qed.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Equations? rho (Γ : context) (t : term) : term by wf (size t) := 
  rho Γ (tApp t u) with view_lambda_fix_app t u := 
    { | fix_lambda_app_lambda na T b [] u' := 
        (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u'};
      | fix_lambda_app_lambda na T b (a :: l) u' :=
        mkApps ((rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ a})
          (map_terms rho Γ (l ++ [u']) _);
      | fix_lambda_app_fix mfix idx l a :=
        let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
        let mfix' := map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _ in
        let args := map_terms rho Γ (l ++ [a]) _ in
        match unfold_fix mfix' idx with 
        | Some (rarg, fn) =>
          if is_constructor rarg (l ++ [a]) then
            mkApps fn args
          else mkApps (tFix mfix' idx) args
        | None => mkApps (tFix mfix' idx) args
        end ;
      | fix_lambda_app_other t' u' nisfixlam := tApp (rho Γ t') (rho Γ u') } ; 
  rho Γ (tLetIn na d t b) => (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b)); 
  rho Γ (tRel i) with option_map decl_body (nth_error Γ i) := { 
    | Some (Some body) => (lift0 (S i) body); 
    | Some None => tRel i; 
    | None => tRel i }; 

  rho Γ (tCase (ind, pars) p x brs) with inspect (decompose_app x) :=
  { | exist (f, args) eqx with view_construct_cofix f := 
  { | construct_cofix_construct ind' c u with eq_inductive ind ind' := 
    { | true => 
        let p' := rho Γ p in 
        let args' := map_terms rho Γ args _ in 
        let brs' := map_brs rho Γ brs _ in 
        iota_red pars c args' brs'; 
      | false => 
        let p' := rho Γ p in 
        let x' := rho Γ x in 
        let brs' := map_brs rho Γ brs _ in 
        tCase (ind, pars) p' x' brs' }; 
    | construct_cofix_cofix mfix idx :=
      let p' := rho Γ p in 
      let args' := map_terms rho Γ args _ in 
      let brs' := map_brs rho Γ brs _ in 
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tCase (ind, pars) p x brs) rho Γ mfixctx mfix _ in
        match nth_error mfix' idx with
        | Some d =>
          tCase (ind, pars) p' (mkApps (subst0 (cofix_subst mfix') (dbody d)) args') brs'
        | None => tCase (ind, pars) p' (rho Γ x) brs'
        end; 
    | construct_cofix_other t nconscof => 
      let p' := rho Γ p in 
      let x' := rho Γ x in 
      let brs' := map_brs rho Γ brs _ in 
        tCase (ind, pars) p' x' brs' } };

  rho Γ (tProj (i, pars, narg) x) with inspect (decompose_app x) := {
    | exist (f, args) eqx with view_construct_cofix f :=
    | construct_cofix_construct ind c u with inspect (nth_error (map_terms rho Γ args _) (pars + narg)) := { 
      | exist (Some arg1) eq => 
        if eq_inductive i ind then arg1
        else tProj (i, pars, narg) (rho Γ x);
      | exist None neq => tProj (i, pars, narg) (rho Γ x) }; 
    | construct_cofix_cofix mfix idx := 
      let args' := map_terms rho Γ args _ in
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tProj (i, pars, narg) x) rho Γ mfixctx mfix _ in
      match nth_error mfix' idx with
      | Some d => tProj (i, pars, narg) (mkApps (subst0 (cofix_subst mfix') (dbody d)) args')
      | None =>  tProj (i, pars, narg) (rho Γ x)
      end;
    | construct_cofix_other t nconscof => tProj (i, pars, narg) (rho Γ x) } ;
  rho Γ (tConst c u) with lookup_env Σ c := { 
    | Some (ConstantDecl decl) with decl.(cst_body) := { 
      | Some body => subst_instance_constr u body; 
      | None => tConst c u }; 
    | _ => tConst c u }; 
  rho Γ (tLambda na t u) => tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tProd na t u) => tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tVar i) => tVar i; 
  rho Γ (tEvar n l) => tEvar n (map_terms rho Γ l _); 
  rho Γ (tSort s) => tSort s; 
  rho Γ (tFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tFix (map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _) idx; 
  rho Γ (tCoFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tCoFix (map_fix_rho (t:=tCoFix mfix idx) rho Γ mfixctx mfix _) idx; 
  rho Γ x => x.
  Proof.
    all:try abstract lia.
    - abstract (rewrite size_mkApps ?list_size_app /=; lia).
    - simpl in Hx. abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x. 
      abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x. 
      abstract (rewrite size_mkApps /=; lia).
    - clear. abstract lia.      
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia). 
  Defined.
  
  Definition rho_fix_context Γ mfix :=
    fold_fix_context rho Γ [] mfix.

  Lemma rho_fix_context_length Γ mfix : #|rho_fix_context Γ mfix| = #|mfix|.
  Proof. now rewrite fold_fix_context_length Nat.add_0_r. Qed.

  Lemma map_terms_map t Γ l H : @map_terms t (fun Γ x Hx => rho Γ x) Γ l H = map (rho Γ) l. 
  Proof. 
    unfold map_terms. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_terms_map : rho.

  Lemma map_brs_map t Γ l H : @map_brs t (fun Γ x Hx => rho Γ x) Γ l H = map (fun x => (x.1, rho Γ x.2)) l. 
  Proof. 
    unfold map_brs. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_brs_map : rho.

  Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
    (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

  Lemma map_fix_rho_map t Γ mfix ctx H : 
    @map_fix_rho t (fun Γ x Hx => rho Γ x) Γ ctx mfix H = 
    map_fix rho Γ ctx mfix.
  Proof. 
    unfold map_fix_rho. now rewrite map_In_spec.
  Qed.

  Lemma fold_fix_context_wf_fold mfix Γ ctx :
    fold_fix_context_wf mfix (fun Γ x _ => rho Γ x) Γ ctx = 
    fold_fix_context rho Γ ctx mfix.
  Proof.
    induction mfix in ctx |- *; simpl; auto. 
  Qed.

  Hint Rewrite map_fix_rho_map fold_fix_context_wf_fold : rho.

  Lemma mkApps_tApp f a l : mkApps (tApp f a) l = mkApps f (a :: l).
  Proof. reflexivity. Qed.

  Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
  Proof. reflexivity. Qed.

  Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
  Proof. 
    induction l using rev_ind; simpl; auto.
    rewrite -mkApps_nested. 
    intros isf. specialize (IHl isf).
    simpl. rewrite IHl. destruct (mkApps t l); auto.
  Qed.
  Definition isFixLambda (t : term) : bool :=
  match t with
  | tFix _ _ => true
  | tLambda _ _ _ => true
  | _ => false
  end.

  Inductive fix_lambda_view : term -> Type :=
  | fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
  | fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
  | fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

  Lemma view_fix_lambda (t : term) : fix_lambda_view t.
  Proof.
    destruct t; repeat constructor.
  Qed.
  
  Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
  Proof. 
    induction l using rev_ind; simpl; auto.
    destruct t; auto.
    intros isl. specialize (IHl isl).
    simpl in IHl.
    now rewrite -mkApps_nested /=. 
  Qed.

  Ltac discr_mkApps H := 
    let Hf := fresh in let Hargs := fresh in
    rewrite ?tApp_mkApps ?mkApps_nested in H;
      (eapply mkApps_nApp_inj in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ []) in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ _ []) in H as [Hf Hargs]);
        [noconf Hf|reflexivity].

  Set Equations With UIP. (* This allows to use decidable equality on terms. *)

  (* Most of this is discrimination, we should have a more robust tactic to  
    solve this. *)
  Lemma rho_app_lambda Γ na ty b a l :
    rho Γ (mkApps (tApp (tLambda na ty b) a) l) =  
    mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho.
    - simpl. reflexivity.
    - simpl. rewrite -mkApps_nested. autorewrite with rho.
      change (mkApps (tApp (tLambda na ty b) a) l) with
        (mkApps (tLambda na ty b) (a :: l)).
      now simp rho.
  Qed.
  
  Lemma bool_pirr (b b' : bool) (p q : b = b') : p = q.
  Proof. noconf p. now noconf q. Qed.

  Lemma view_lambda_fix_app_other t u (H : ~~ isFixLambda_app (tApp t u)) :
    view_lambda_fix_app t u = fix_lambda_app_other t u H.
  Proof.
    induction t; simpl; f_equal; try apply bool_pirr.
    simpl in H => //.
    specialize (IHt1 H).
    rewrite IHt1. destruct t1; auto.
    simpl in H => //.
  Qed.

  Lemma rho_app_lambda' Γ na ty b l :
    rho Γ (mkApps (tLambda na ty b) l) =
    match l with 
    | [] => rho Γ (tLambda na ty b)
    | a :: l => 
      mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l)
    end.
  Proof.
    destruct l using rev_case; autorewrite with rho; auto.
    simpl. rewrite -mkApps_nested. simp rho.
    destruct l; simpl; auto. now simp rho.
  Qed.

  Lemma rho_app_construct Γ c u i l :
    rho Γ (mkApps (tConstruct c u i) l) =
    mkApps (tConstruct c u i) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    simpl. rewrite -mkApps_nested. simp rho.
    unshelve erewrite view_lambda_fix_app_other. simpl.
    clear; induction l using rev_ind; simpl; auto. 
    rewrite -mkApps_nested. simpl. apply IHl.
    simp rho. rewrite IHl. now rewrite map_app -mkApps_nested.
  Qed.
  Hint Rewrite rho_app_construct : rho.

  Lemma rho_app_cofix Γ mfix idx l :
    rho Γ (mkApps (tCoFix mfix idx) l) =
    mkApps (tCoFix (map_fix rho Γ (rho_fix_context Γ mfix) mfix) idx) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    simpl. now simp rho. rewrite -mkApps_nested. simp rho.
    unshelve erewrite view_lambda_fix_app_other. simpl.
    clear; induction l using rev_ind; simpl; auto. 
    rewrite -mkApps_nested. simpl. apply IHl.
    simp rho. rewrite IHl. now rewrite map_app -mkApps_nested.
  Qed.

  Hint Rewrite rho_app_cofix : rho.

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

  Lemma map_cofix_subst' f g mfix :
    (forall n, tCoFix (map (map_def f g) mfix) n = f (tCoFix mfix n)) ->
    cofix_subst (map (map_def f g) mfix) =
    map f (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f g mfix :
    (forall n, tFix (map (map_def f g) mfix) n = f (tFix mfix n)) ->
    fix_subst (map (map_def f g) mfix) =
    map f (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma rho_app_fix Γ mfix idx args :
    let rhoargs := map (rho Γ) args in
    rho Γ (mkApps (tFix mfix idx) args) = 
      match nth_error mfix idx with
      | Some d => 
        if is_constructor (rarg d) args then 
          let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
          mkApps fn rhoargs
        else mkApps (rho Γ (tFix mfix idx)) rhoargs
      | None => mkApps (rho Γ (tFix mfix idx)) rhoargs
      end.
  Proof.
    induction args using rev_ind; autorewrite with rho.
    - intros rhoargs.
      destruct nth_error as [d|] eqn:eqfix => //.
      rewrite /is_constructor nth_error_nil //.
    - simpl. rewrite map_app /=.
      destruct nth_error as [d|] eqn:eqfix => //.
      destruct (is_constructor (rarg d) (args ++ [x])) eqn:isc; simp rho.
      * rewrite -mkApps_nested /=.
        autorewrite with rho.
        simpl. simp rho. rewrite /unfold_fix.
        rewrite /map_fix nth_error_map eqfix /= isc map_fix_subst ?map_app //.
        intros n; simp rho. simpl. f_equal; now simp rho.
      * rewrite -mkApps_nested /=.
        simp rho. simpl. simp rho.
        now rewrite /unfold_fix /map_fix nth_error_map eqfix /= isc map_app.
      * rewrite -mkApps_nested /=. simp rho.
        simpl. simp rho.
        now  rewrite /unfold_fix /map_fix nth_error_map eqfix /= map_app.
  Qed.

  (* Helps factors proofs: only two cases to consider: the fixpoint unfolds or is stuck. *)
  Inductive rho_fix_spec Γ mfix i l : term -> Type :=
  | rho_fix_red d :
      let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
      nth_error mfix i = Some d ->
      is_constructor (rarg d) l ->
      rho_fix_spec Γ mfix i l (mkApps fn (map (rho Γ) l))
  | rho_fix_stuck :
      (match nth_error mfix i with
       | None => true
       | Some d => ~~ is_constructor (rarg d) l
       end) ->
      rho_fix_spec Γ mfix i l (mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)).

  Lemma rho_fix_elim Γ mfix i l :
    rho_fix_spec Γ mfix i l (rho Γ (mkApps (tFix mfix i) l)).
  Proof.
    rewrite rho_app_fix /= /unfold_fix.
    case e: nth_error => [d|] /=.
    case isc: is_constructor => /=.
    - eapply (rho_fix_red Γ mfix i l d) => //.
    - apply rho_fix_stuck.
      now rewrite e isc.
    - apply rho_fix_stuck. now rewrite e /=.
  Qed.

  Lemma rho_app_case Γ ind pars p x brs :
    rho Γ (tCase (ind, pars) p x brs) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u => 
      if eq_inductive ind ind' then
        let p' := rho Γ p in 
        let args' := map (rho Γ) args in 
        let brs' := map (on_snd (rho Γ)) brs in 
        iota_red pars c args' brs'
      else tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tCase (ind, pars) (rho Γ p) (mkApps fn (map (rho Γ) args)) (map (on_snd (rho Γ)) brs)
      | None => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
      end
    | _ => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho.
    destruct view_construct_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    destruct unfold_cofix as [[rarg fn]|]; simp rho => //.
    simpl. autorewrite with rho. rewrite /map_fix nth_error_map.
    destruct nth_error => /=. f_equal.
    f_equal. rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    reflexivity.
    simpl.
    autorewrite with rho.
    rewrite /map_fix nth_error_map.
    destruct nth_error => /= //.
    rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros; simp rho; simpl; now simp rho.
    simpl. eapply symmetry, decompose_app_inv in eqapp.
    subst x. destruct t; simpl in d => //.
  Qed.

  Lemma rho_app_proj Γ ind pars arg x :
    rho Γ (tProj (ind, pars, arg) x) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u => 
      if eq_inductive ind ind' then
        match nth_error args (pars + arg) with
        | Some arg1 => rho Γ arg1
        | None => tProj (ind, pars, arg) (rho Γ x)
        end
      else tProj (ind, pars, arg) (rho Γ x)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tProj (ind, pars, arg) (mkApps fn (map (rho Γ) args))
      | None => tProj (ind, pars, arg) (rho Γ x)
      end
    | _ => tProj (ind, pars, arg) (rho Γ x)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho.
    destruct view_construct_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    set (arg' := inspect _). clearbody arg'.
    destruct arg' as [[arg'|] eqarg'];
    autorewrite with rho. rewrite eqi.
    simp rho in eqarg'. rewrite nth_error_map in eqarg'.
    destruct nth_error => //. now simpl in eqarg'.
    simp rho in eqarg'; rewrite nth_error_map in eqarg'.
    destruct nth_error => //.
    destruct inspect as [[arg'|] eqarg'] => //; simp rho.
    now rewrite eqi.
    simpl. autorewrite with rho.
    rewrite /map_fix nth_error_map.
    destruct nth_error eqn:nth => /= //.
    f_equal. f_equal. f_equal.
    rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    simpl. eapply symmetry, decompose_app_inv in eqapp.
    subst x. destruct t; simpl in d => //.
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

  Lemma fold_fix_context_app Γ l acc acc' :
    fold_fix_context rho Γ l (acc ++ acc') =
    fold_fix_context rho Γ (fold_fix_context rho Γ l acc) acc'.
  Proof.
    induction acc in l, acc' |- *. simpl. auto.
    simpl. rewrite IHacc. reflexivity.
  Qed.

  Section All2i.
    (** A special notion of All2 just for this proof *)

    Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
      All2i_nil : All2i R [] []
    | All2i_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
            R (List.length l) x y -> All2i R l l' -> All2i R (x :: l) (y :: l').
    Hint Constructors All2i : core pcuic.

    Lemma All2i_app {A B} (P : nat -> A -> B -> Type) l0 l0' l1 l1' :
      All2i P l0' l1' ->
      All2i (fun n => P (n + #|l0'|)) l0 l1 ->
      All2i P (l0 ++ l0') (l1 ++ l1').
    Proof.
      intros H. induction 1; simpl. apply H.
      constructor. now rewrite app_length. apply IHX.
    Qed.

    Lemma All2i_length {A B} (P : nat -> A -> B -> Type) l l' :
      All2i P l l' -> #|l| = #|l'|.
    Proof. induction 1; simpl; auto. Qed.

    Lemma All2i_impl {A B} (P Q : nat -> A -> B -> Type) l l' :
      All2i P l l' -> (forall n x y, P n x y -> Q n x y) -> All2i Q l l'.
    Proof. induction 1; simpl; auto. Qed.

    Lemma All2i_rev {A B} (P : nat -> A -> B -> Type) l l' :
      All2i P l l' ->
      All2i (fun n => P (#|l| - S n)) (List.rev l) (List.rev l').
    Proof.
      induction 1. constructor. simpl List.rev.
      apply All2i_app. repeat constructor. simpl. rewrite Nat.sub_0_r. auto.
      simpl. eapply All2i_impl; eauto. intros. simpl in X0. now rewrite Nat.add_1_r.
    Qed.

    Inductive All2i_ctx {A B : Type} (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
      All2i_ctx_nil : All2i_ctx R n [] []
    | All2i_ctx_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
        R n x y -> All2i_ctx R (S n) l l' -> All2i_ctx R n (x :: l) (y :: l').
    Hint Constructors All2i_ctx : core pcuic.

    Lemma All2i_ctx_app {A B} (P : nat -> A -> B -> Type) n l0 l0' l1 l1' :
      All2i_ctx P (n + #|l0|) l0' l1' ->
      All2i_ctx P n l0 l1 ->
      All2i_ctx P n (l0 ++ l0') (l1 ++ l1').
    Proof.
      intros H.
      induction 1. simpl. now rewrite Nat.add_0_r in H.
      simpl. rewrite Nat.add_succ_comm in IHX. specialize (IHX H).
      now constructor.
    Qed.

    Lemma All2i_rev_ctx {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i R l l' -> All2i_ctx R 0 (List.rev l) (List.rev l').
    Proof.
      induction 1. simpl. constructor.
      simpl. apply All2i_ctx_app. simpl. rewrite List.rev_length. auto.
      auto.
    Qed.

    Lemma All2i_rev_ctx_gen {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i_ctx R n l l' -> All2i (fun m => R (n + m)) (List.rev l) (List.rev l').
    Proof.
      induction 1. simpl. constructor.
      simpl. eapply All2i_app. constructor. now rewrite Nat.add_0_r. constructor.
      eapply All2i_impl; eauto. intros.
      simpl in *. rewrite [S _]Nat.add_succ_comm in X0. now rewrite Nat.add_1_r.
    Qed.

    Lemma All2i_rev_ctx_inv {A B} (R : nat -> A -> B -> Type) (l : list A) (l' : list B) :
      All2i_ctx R 0 l l' -> All2i R (List.rev l) (List.rev l').
    Proof.
      intros. eapply All2i_rev_ctx_gen in X. simpl in X. apply X.
    Qed.

    Lemma All2i_ctx_mapi {A B C D} (R : nat -> A -> B -> Type)
          (l : list C) (l' : list D) (f : nat -> C -> A) (g : nat -> D -> B) n :
      All2i_ctx (fun n x y => R n (f n x) (g n y)) n l l' ->
      All2i_ctx R n (mapi_rec f l n) (mapi_rec g l' n).
    Proof.
      induction 1; constructor; auto.
    Qed.

    Lemma All2i_ctx_trivial {A B} (R : nat -> A -> B -> Type) (H : forall n x y, R n x y) n l l' :
      #|l| = #|l'| -> All2i_ctx R n l l'.
    Proof.
      induction l in n, l' |- *; destruct l'; simpl; try discriminate; intros; constructor; auto.
    Qed.
  End All2i.

  Definition pres_bodies Γ Δ σ :=
    All2i (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[⇑^n σ]) (decl_body decl)))
        Γ Δ.

  Lemma pres_bodies_inst_context Γ σ : pres_bodies Γ (inst_context σ Γ) σ.
  Proof.
    red; induction Γ. constructor.
    rewrite inst_context_snoc. constructor. simpl. reflexivity.
    apply IHΓ.
  Qed.
  Hint Resolve pres_bodies_inst_context : pcuic.
      
  Definition ctxmap (Γ Δ : context) (s : nat -> term) :=
    forall x d, nth_error Γ x = Some d ->
                match decl_body d return Type with
                | Some b =>
                  ∑ i b', s x = tRel i /\
                          option_map decl_body (nth_error Δ i) = Some (Some b') /\
                          b'.[↑^(S i)] = b.[↑^(S x) ∘s s]
                | None => True
                end.

  Lemma All2_prop2_eq_split (Γ Γ' Γ2 Γ2' : context) (A B : Type) (f g : A → term)
        (h : A → B) (rel : context → context → term → term → Type) x y :
    All2_prop2_eq Γ Γ' Γ2 Γ2' f g h rel x y ->
    All2 (on_Trel (rel Γ Γ') f) x y *
    All2 (on_Trel (rel Γ2 Γ2') g) x y *
    All2 (on_Trel eq h) x y.
  Proof.
    induction 1; intuition.
  Qed.

  Lemma refine_pred Γ Δ t u u' : u = u' -> pred1 Σ Γ Δ t u' -> pred1 Σ Γ Δ t u.
  Proof. now intros ->. Qed.

  Lemma ctxmap_ext Γ Δ : CMorphisms.Proper (CMorphisms.respectful (pointwise_relation _ eq) isEquiv) (ctxmap Γ Δ).
  Proof.
    red. red. intros.
    split; intros X.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite -H. split; auto.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite H. split; auto.
  Qed.

  Lemma Up_ctxmap Γ Δ c c' σ :
    ctxmap Γ Δ σ ->
    (decl_body c' = option_map (fun x => x.[σ]) (decl_body c)) ->
    ctxmap (Γ ,, c) (Δ ,, c') (⇑ σ).
  Proof.
    intros.
    intros x d Hnth.
    destruct x; simpl in *; noconf Hnth.
    destruct c as [na [b|] ty]; simpl; auto.
    exists 0. eexists. repeat split; eauto. simpl in H. simpl. now rewrite H.
    now autorewrite with sigma.
    specialize (X _ _ Hnth). destruct decl_body; auto.
    destruct X as [i [b' [? [? ?]]]]; auto.
    exists (S i), b'. simpl. repeat split; auto.
    unfold subst_compose. now rewrite H0.
    autorewrite with sigma in H2 |- *.
    rewrite -subst_compose_assoc.
    rewrite -subst_compose_assoc.
    rewrite -subst_compose_assoc.
    rewrite -inst_assoc. rewrite H2.
    now autorewrite with sigma.
  Qed.

  Lemma Upn_ctxmap Γ Δ Γ' Δ' σ :
    pres_bodies Γ' Δ' σ ->
    ctxmap Γ Δ σ ->
    ctxmap (Γ ,,, Γ') (Δ ,,, Δ') (⇑^#|Γ'| σ).
  Proof.
    induction 1. simpl. intros.
    eapply ctxmap_ext. rewrite Upn_0. reflexivity. apply X.
    simpl. intros Hσ.
    eapply ctxmap_ext. now sigma.
    eapply Up_ctxmap; eauto.
  Qed.
  Hint Resolve Upn_ctxmap : pcuic.

  (** Untyped renamings *)
  Definition renaming Γ Δ r :=
    forall x, match nth_error Γ x with
              | Some d =>
                match decl_body d return Prop with
                | Some b =>
                  exists b', option_map decl_body (nth_error Δ (r x)) = Some (Some b') /\
                             b'.[↑^(S (r x))] = b.[↑^(S x) ∘s ren r]
                (* whose body is b substituted with the previous variables *)
                | None => option_map decl_body (nth_error Δ (r x)) = Some None
                end
              | None => nth_error Δ (r x) = None
              end.

  Instance renaming_ext Γ Δ : Morphisms.Proper (`=1` ==> iff)%signature (renaming Γ Δ).
  Proof.
    red. red. intros.
    split; intros.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      destruct c as [na [b|] ty]; simpl in *; auto.
      destruct H0 as [b' [Heq Heq']]; auto. exists b'. rewrite -(H n).
      intuition auto. now rewrite Heq' H. now rewrite -H.
      now rewrite -H.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      destruct c as [na [b|] ty]; simpl in *; auto.
      destruct H0 as [b' [Heq Heq']]; auto. exists b'. rewrite (H n).
      intuition auto. now rewrite Heq' H. now rewrite H.
      now rewrite H.
  Qed.

  Lemma shiftn1_renaming Γ Δ c c' r :
    renaming Γ Δ r ->
    (decl_body c' = option_map (fun x => x.[ren r]) (decl_body c)) ->
    renaming (c :: Γ) (c' :: Δ) (shiftn 1 r).
  Proof.
    intros.
    red.
    destruct x. simpl.
    destruct (decl_body c) eqn:Heq; rewrite H0; auto. eexists. simpl. split; eauto.
    sigma. rewrite -ren_shiftn. now sigma.

    simpl.
    rewrite Nat.sub_0_r. specialize (H x).
    destruct nth_error eqn:Heq.
    destruct c0 as [na [b|] ty]; cbn in *.
    destruct H as [b' [Hb Heq']].
    exists b'; intuition auto.
    rewrite -ren_shiftn. autorewrite with sigma in Heq' |- *.
    rewrite Nat.sub_0_r.
    rewrite -?subst_compose_assoc -inst_assoc.
    rewrite -[b.[_]]inst_assoc. rewrite Heq'.
    now sigma.
    auto. auto.
  Qed.
  
  Lemma shift_renaming Γ Δ ctx ctx' r :
    All2i (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[ren (shiftn n r)]) (decl_body decl)))
          ctx ctx' ->
    renaming Γ Δ r ->
    renaming (Γ ,,, ctx) (Δ ,,, ctx') (shiftn #|ctx| r).
  Proof.
    induction 1.
    intros. rewrite shiftn0. apply H.
    intros. simpl.
    rewrite shiftnS. apply shiftn1_renaming. apply IHX; try lia. auto.
    apply r0.
  Qed.

  Lemma renaming_shift_rho_fix_context:
    ∀ (mfix : mfixpoint term) (Γ Δ : list context_decl) (r : nat → nat),
      renaming Γ Δ r ->
      renaming (Γ ,,, rho_fix_context Γ mfix)
               (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
               (shiftn #|mfix| r).
  Proof.
    intros mfix Γ Δ r Hr.
    rewrite -{2}(rho_fix_context_length Γ mfix).
    eapply shift_renaming; auto.
    rewrite /rho_fix_context !fold_fix_context_rev.
    apply All2i_rev_ctx_inv, All2i_ctx_mapi.
    simpl. apply All2i_ctx_trivial; auto. now rewrite map_length.
  Qed.
  
  Lemma map_fix_rho_rename:
    ∀ (mfix : mfixpoint term) (i : nat) (l : list term),
      (∀ t' : term, size t' < size (mkApps (tFix mfix i) l)
                    → ∀ (Γ Δ : list context_decl) (r : nat → nat),
            renaming Γ Δ r
            → rename r (rho Γ t') = rho Δ (rename r t'))
      → ∀ (Γ Δ : list context_decl) (r : nat → nat),
        renaming Γ Δ r
        → map (map_def (rename r) (rename (shiftn #|mfix| r)))
              (map_fix rho Γ (fold_fix_context rho Γ [] mfix) mfix) =
          map_fix rho Δ (fold_fix_context rho Δ [] (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                  (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix).
  Proof.
    intros mfix i l H Γ Δ r H2.
    rewrite /map_fix !map_map_compose !compose_map_def.
    apply map_ext_in => d /mfixpoint_size_In dsize.
    apply map_def_eq_spec.
    - specialize (H (dtype d)).
      forward H. rewrite mkApps_size. simpl. lia.
      now apply H.
    - specialize (H (dbody d)).
      forward H. rewrite mkApps_size. simpl. lia.
      apply (H).  eapply renaming_shift_rho_fix_context; tea.
  Qed.

  Lemma All_IH {A size} (l : list A) k (P : A -> Type) :
    list_size size l <= k ->
    (forall x, size x < k -> P x) -> 
    All P l.
  Proof.
    induction l in k |- *. constructor.
    simpl. intros Hk IH.
    constructor. apply IH. lia.
    eapply (IHl k). lia. intros x sx.
    apply IH. lia.
  Qed.

  Lemma All_IH' {A size B size'} (f : A -> B) (l : list A) k (P : B -> Type) :
    list_size size l <= k ->
    (forall x, size' (f x) <= size x) ->
    (forall x, size' x < k -> P x) -> 
    All (fun x => P (f x)) l.
  Proof.
    induction l in k |- *. constructor.
    simpl. intros Hk Hs IH.
    constructor. apply IH. specialize (Hs a). lia.
    eapply (IHl k). lia. apply Hs.
    apply IH.
  Qed.

  Lemma isConstruct_app_rename r t :
    isConstruct_app t = isConstruct_app (rename r t).
  Proof.
    unfold isConstruct_app. unfold decompose_app. generalize (nil term) at 1.
    change (nil term) with (map (rename r) []). generalize (nil term).
    induction t; simpl; auto.
    intros l l0. specialize (IHt1 (t2 :: l) (t2 :: l0)).
    now rewrite IHt1.
  Qed.

  Lemma is_constructor_rename x l r : is_constructor x l = is_constructor x (map (rename r) l).
  Proof.
    rewrite /is_constructor nth_error_map.
    elim: nth_error_spec => //.
    move=> n hnth xl /=.
    now apply isConstruct_app_rename.
  Qed.

  Lemma isFixLambda_app_rename r t : ~~ isFixLambda_app t -> ~~ isFixLambda_app (rename r t).
  Proof.
    induction t; simpl; auto.
    destruct t1; simpl in *; auto.
  Qed.

  Lemma construct_cofix_rename r t : discr_construct_cofix t -> discr_construct_cofix (rename r t).
  Proof.
    destruct t; simpl; try congruence.
  Qed.

  Lemma rho_rename Γ Δ r t :
    renaming Γ Δ r ->
    rename r (rho Γ t) = rho Δ (rename r t).
  Proof.
    revert t Γ Δ r.
    refine (term_ind_size_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      intros; try subst Γ; try rename Γ0 into Γ(* ; rename_all_hyps *).
    all:auto 2.

    - red in H. simpl.
      specialize (H n).
      destruct (nth_error Γ n) as [c|] eqn:Heq.
      -- simp rho. rewrite Heq /=.
         destruct decl_body eqn:Heq''.
         simp rho. rewrite lift0_inst.
         destruct H as [b' [-> Hb']] => /=.
         rewrite lift0_inst.
         sigma. autorewrite with sigma in *. now rewrite <- Hb'.
         simpl.
         rewrite H. simpl. reflexivity.

      -- simp rho. rewrite Heq H //.

    - simpl; simp rho. simpl. f_equal; rewrite !map_map_compose. solve_all.

    - simpl; simp rho; simpl. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl; simp rho; simpl. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl; simp rho; simpl. rewrite /subst1 subst_inst.
      specialize (H _ _ _ H2). specialize (H0 _ _ _ H2).
      autorewrite with sigma in H, H0, H1. erewrite <- (H1 ((vdef n (rho Γ t) (rho Γ t0) :: Γ))).
      2:{ eapply (shift_renaming _ _ [_] [_]). repeat constructor. simpl.
          sigma. now rewrite -H shiftn0. auto. }
      sigma. apply inst_ext. rewrite H.
      rewrite -ren_shiftn. sigma. unfold Up. now sigma.

    - rewrite rho_equation_8.
      destruct (view_lambda_fix_app t u).

      + (* Fixpoint application *)
        simpl; simp rho. rewrite rename_mkApps. cbn [rename].
        assert (eqargs : map (rename r) (map (rho Γ) (l ++ [a])) =
                map (rho Δ) (map (rename r) (l ++ [a]))).
        { rewrite !map_map_compose !map_app. f_equal => /= //.
          2:{ f_equal. now apply H1. }
          unshelve epose proof (All_IH l _ _ _ H); simpl; eauto.
          rewrite size_mkApps. lia. solve_all. }
        destruct (rho_fix_elim Γ mfix i (l ++ [a])).
        simpl. simp rho.
        rewrite /unfold_fix /map_fix nth_error_map e /= i0.
        simp rho; rewrite /map_fix !nth_error_map /= e /=.
        move: i0; rewrite /is_constructor -(map_app (rename r) l [a]) nth_error_map.
        destruct (nth_error_spec (l ++ [a]) (rarg d)) => /= //.
        rewrite -isConstruct_app_rename => -> //.
        rewrite rename_mkApps.
        f_equal; auto.
        assert (Hbod: ∀ (Γ Δ : list context_decl) (r : nat → nat),
                   renaming Γ Δ r → rename r (rho Γ (dbody d)) = rho Δ (rename r (dbody d))).
        { pose proof (H (dbody d)) as Hbod.
          forward Hbod.
          { simpl; rewrite mkApps_size. simpl.
            eapply mfixpoint_size_nth_error in e. lia. }
          auto. }
        assert (Hren : renaming (Γ ,,, rho_fix_context Γ mfix)
                           (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                           (shiftn #|mfix| r)).
        now apply renaming_shift_rho_fix_context.
        specialize (Hbod _ _ _ Hren).
        rewrite -Hbod.
        rewrite !subst_inst.
        { sigma. eapply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          rewrite map_fix_subst //.
          intros n. simp rho. simpl. simp rho.
          reflexivity.
          clear -H H2 Hren.
          unfold fix_subst. autorewrite with len. generalize #|mfix| at 1 4.
          induction n; simpl; auto.
          rewrite IHn. clear IHn. f_equal; auto.
          specialize (H (tFix mfix n)) as Hbod.
          forward Hbod.
          { simpl; rewrite mkApps_size. simpl. lia. }
          simp rho. simpl. simp rho.
          specialize (Hbod _ _ _ H2).
          simpl in Hbod. simp rho in Hbod.
          simpl in Hbod; simp rho in Hbod.
          rewrite -Hbod.
          rewrite map_length. f_equal.
          rewrite !map_map_compose. apply map_ext.
          intros []; unfold map_def; cbn.
          rewrite !rename_inst. f_equal. apply inst_ext.
          apply ren_shiftn. }

        simp rho; simpl; simp rho.
        rewrite /unfold_fix /map_fix !nth_error_map.
        destruct (nth_error mfix i) eqn:hfix => /=.
        assert(is_constructor (rarg d) (l ++ [a]) = false).
        red in i0; unfold negb in i0.
        destruct is_constructor; auto.
        rewrite H3.
        rewrite -(map_app (rename r) l [a]) -is_constructor_rename H3 //.
        rewrite rename_mkApps.
        f_equal. simpl. f_equal.
        autorewrite with len. 
        eapply (map_fix_rho_rename mfix i l); eauto.
        intros. eapply H. rewrite /=. lia. auto.
        apply eqargs.
        rewrite rename_mkApps. f_equal; auto.
        2:{ now rewrite -(map_app (rename r) _ [_]). }
        simpl. f_equal. autorewrite with len.
        apply (map_fix_rho_rename mfix i l); eauto.
        intros; eapply H; simpl; try lia. auto.

      + (* Lambda abstraction *)
        pose proof (rho_app_lambda' Γ na ty b (l ++ [a])).
        simp rho in H3. rewrite -mkApps_nested in H3.
        simpl in H3. simp rho in H3. rewrite {}H3.
        simpl. 
        rewrite rename_mkApps. simpl.
        rewrite tApp_mkApps mkApps_nested.
        rewrite -(map_app (rename r) _ [_]). 
        rewrite rho_app_lambda'.
        simpl.
        assert (All (fun x => rename r (rho Γ x) = rho Δ (rename r x)) (l ++ [a])).
        { apply All_app_inv. 2:constructor; auto.
          unshelve epose proof (All_IH l _ _ _ H); simpl; eauto.
          rewrite size_mkApps. lia. solve_all. }
        remember (l ++ [a]) as args.
        destruct args; simpl; simp rho.
        { apply (f_equal (@length _)) in Heqargs. simpl in Heqargs.
         autorewrite with len in Heqargs. simpl in Heqargs. lia. }
        rewrite rename_inst /subst1 subst_inst.
        simpl in H.
        specialize (H b).
        forward H. rewrite size_mkApps /=. lia.
        rewrite inst_mkApps. 
        specialize (H (vass na (rho Γ ty) :: Γ) (vass na (rho Δ ty.[ren r]) :: Δ) (shiftn 1 r)).
        forward H. eapply shiftn1_renaming; auto.
        sigma. depelim X.
        autorewrite with sigma in H, e, X.                
        f_equal.
        rewrite -H. sigma. apply inst_ext.
        rewrite e.
        rewrite -ren_shiftn. sigma.
        unfold Up. now sigma.
        rewrite !map_map_compose. solve_all.
        now autorewrite with sigma in H3.
      + simpl.
        simp rho. pose proof (isFixLambda_app_rename r _ i).
        simpl in H3. rewrite (view_lambda_fix_app_other (rename r t) (rename r a) H3). simpl.
        erewrite H0, H1; eauto.

    - (* Constant unfolding *)
      simpl; simp rho; simpl.
      case e: lookup_env => [[decl|decl]|] //; simp rho.
      case eb: cst_body => [b|] //; simp rho.
      rewrite rename_inst inst_closed0 //.
      apply declared_decl_closed in e => //.
      hnf in e. rewrite eb in e. rewrite closedn_subst_instance_constr; auto.
      now move/andP: e => [-> _].

    - (* construct/cofix iota reduction *)
      simpl; simp rho. destruct p. simp rho.
      destruct inspect as [[f a] decapp].
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry decapp)).
      rewrite <- decapp' in H2. noconf H2.
      assert (map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) l) =
              (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) l))).
      { red in X. rewrite !map_map_compose /on_snd. solve_all. }

      simpl. destruct view_construct_cofix; simpl; simp rho.

      * destruct (eq_inductive i c) eqn:eqi.
        simp rho. simpl. rewrite -H2. 
        (* Reduction *)
        rewrite /iota_red /= -map_skipn rename_mkApps !nth_map //.
        f_equal. simpl. rewrite !map_skipn.
        apply symmetry, decompose_app_inv in decapp. subst t0.
        specialize (H0 _ _ _ H1).
        rewrite !rho_app_construct !rename_mkApps in H0.
        simpl in H0. rewrite rho_app_construct in H0.
        apply mkApps_eq_inj in H0 as [_ Heq] => //. congruence.

        simp rho. simpl.
        erewrite H, H0; eauto.
        now rewrite -H2.

      * simpl; simp rho.
        rewrite /map_fix !map_map_compose.
        red in X.
        rewrite /unfold_cofix !nth_error_map.
        apply symmetry, decompose_app_inv in decapp. subst t0.
        specialize (H0 _ _ _ H1).
        simp rho in H0.
        rewrite !rename_mkApps in H0.
        simpl in H0. simp rho in H0.
        apply mkApps_eq_inj in H0 as [Heqcof Heq] => //.
        noconf Heqcof. simpl in H0. noconf H0.
        autorewrite with len in H0.
        rewrite /map_fix !map_map_compose in H0.

        case efix: (nth_error mfix idx) => [d|] /= //.
        + rewrite rename_mkApps !map_map_compose compose_map_def /on_snd.
          f_equal. erewrite H; eauto. f_equal => //.
          rewrite !subst_inst. sigma.
          apply map_eq_inj in H0.
          epose proof (nth_error_all efix H0).
          simpl in H3. apply (f_equal dbody) in H3.
          simpl in H3. autorewrite with sigma in H3.
          rewrite -H3. sigma.
          apply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          2:now autorewrite with len.
          rewrite map_cofix_subst' //. 
          intros n'; simp rho. simpl; f_equal. now simp rho.
          rewrite map_cofix_subst' //.
          simpl. move=> n'; f_equal. simp rho; simpl; simp rho.
          f_equal. rewrite /map_fix.
          rewrite !map_map_compose !compose_map_def.
          apply map_ext => x; apply map_def_eq_spec => //.
          rewrite !map_map_compose.
          unfold cofix_subst. generalize #|mfix|.
          clear -H0.
          induction n; simpl; auto. f_equal; auto.
          simp rho. simpl. simp rho. f_equal.
          rewrite /map_fix !map_map_compose.  autorewrite with len.
          solve_all.
          rewrite -H.
          apply map_def_eq_spec; simpl. now sigma. sigma.
          rewrite -ren_shiftn. rewrite up_Upn. reflexivity.
          now rewrite !map_map_compose in Heq. simpl.
          solve_all.

        + rewrite map_map_compose /on_snd. f_equal; auto.
          simp rho.
          rewrite !rename_mkApps /= !map_map_compose !compose_map_def /=.
          simp rho.
          f_equal. f_equal.
          rewrite /map_fix map_map_compose. rewrite -H0.
          autorewrite with len. reflexivity.
          now rewrite -Heq !map_map_compose.
          simpl. solve_all.
      * pose proof (construct_cofix_rename r t1 d).
        destruct (view_construct_cofix (rename r t1)); simpl in H3 => //.
        simp rho. simpl. rewrite -H2. erewrite H, H0; eauto.

    - (* Proj construct/cofix reduction *)
      simpl; simp rho. destruct s as [[ind pars] n]. 
      rewrite !rho_app_proj.
      destruct decompose_app as [f a] eqn:decapp.
      erewrite (decompose_app_rename decapp).
      erewrite <-H; eauto.
      apply decompose_app_inv in decapp. subst t.
      specialize (H _ _ _ H0).
      rewrite rename_mkApps in H.

      destruct f; simpl; auto.
      * destruct eq_inductive eqn:eqi; simpl; auto.
        rewrite nth_error_map.
        destruct nth_error eqn:hnth; simpl; auto.
        simp rho in H. rewrite rename_mkApps in H.
        eapply mkApps_eq_inj in H as [_ Hargs] => //.
        rewrite !map_map_compose in Hargs.
        eapply map_eq_inj in Hargs.  
        apply (nth_error_all hnth Hargs).
      * rewrite nth_error_map.
        destruct nth_error eqn:hnth; auto.
        simpl. rewrite rename_mkApps.
        f_equal; auto.
        simpl in H; simp rho in H. rewrite rename_mkApps in H.
        eapply mkApps_eq_inj in H as [Hcof Hargs] => //.
        f_equal; auto. simpl in Hcof. noconf Hcof. simpl in H.
        noconf H.
        rewrite /map_fix !map_map_compose in H.
        apply map_eq_inj in H.
        epose proof (nth_error_all hnth H).
        simpl in H1. apply (f_equal dbody) in H1.
        simpl in H1. autorewrite with sigma in H1.
        sigma. autorewrite with len in H, H1.
        rewrite -H1. sigma.
        apply inst_ext.
        rewrite -ren_shiftn. sigma.
        rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
        rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
        2:now autorewrite with len.
        rewrite map_cofix_subst' //. 
        rewrite !map_map_compose.
        unfold cofix_subst. generalize #|mfix|.
        clear -H.
        induction n; simpl; auto. f_equal; auto.
        simp rho. simpl. simp rho. f_equal.
        rewrite /map_fix !map_map_compose.  autorewrite with len.
        solve_all.
        rewrite -H.
        apply map_def_eq_spec; simpl. now sigma. sigma.
        rewrite -ren_shiftn. rewrite up_Upn. reflexivity.  

    - (* Fix *)
      simpl; simp rho; simpl; simp rho.
      f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X. solve_all.
      rewrite !map_def_map_def.
      eapply map_def_eq_spec. eapply a. auto.
      erewrite b; auto.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      rewrite {2}H0.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.

    - (* CoFix *)
      simpl; simp rho; simpl; simp rho.
      f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X. solve_all.
      rewrite !map_def_map_def.
      eapply map_def_eq_spec. eapply a. auto.
      erewrite b; auto.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      rewrite {2}H0.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.
  Qed.

  Lemma rho_lift0 Γ Δ t : lift0 #|Δ| (rho Γ t) = rho (Γ ,,, Δ) (lift0 #|Δ| t).
  Proof.
    rewrite !lift_rename. apply rho_rename.
    red. intros x. destruct nth_error eqn:Heq.
    unfold lift_renaming. simpl. rewrite Nat.add_comm.
    rewrite nth_error_app_ge. lia. rewrite Nat.add_sub Heq.
    destruct c as [na [b|] ty]; simpl in *; auto.
    exists b. split; eauto.
    rewrite -ren_shiftk. rewrite shiftk_compose. reflexivity.
    unfold lift_renaming. simpl. rewrite Nat.add_comm.
    rewrite nth_error_app_ge. lia. now rewrite Nat.add_sub Heq.
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
    f_equal. f_equal. rewrite rho_lift0. auto.
    repeat f_equal. rewrite rho_lift0; auto.
  Qed.

  Lemma fold_fix_context_rho_ctx Γ m :
    rho_ctx_over (rho_ctx Γ) (fix_context m) =
    fold_fix_context rho (rho_ctx Γ) [] m.
  Proof.
    rewrite <- fold_fix_context_over_acc; now rewrite ?app_nil_r.
  Qed.

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

  Lemma rho_cofix_subst Γ mfix :
    cofix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (cofix_subst mfix)).
  Proof.
    unfold cofix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. reflexivity. simpl. simp rho. simpl.
    simp rho.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
  Qed.

  Lemma rho_fix_subst Γ mfix :
    fix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (fix_subst mfix)).
  Proof.
    unfold fix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. reflexivity. simpl. simp rho; simpl; simp rho.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
  Qed.

  Lemma nth_error_cofix_subst mfix n b :
    nth_error (cofix_subst mfix) n = Some b ->
    b = tCoFix mfix (#|mfix| - S n).
  Proof.
    unfold cofix_subst.
    generalize #|mfix|. induction n0 in n, b |- *. simpl.
    destruct n; simpl; congruence.
    destruct n; simpl. intros [= <-]. f_equal.
    destruct n0; simpl; try reflexivity.
    intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma nth_error_fix_subst mfix n b :
    nth_error (fix_subst mfix) n = Some b ->
    b = tFix mfix (#|mfix| - S n).
  Proof.
    unfold fix_subst.
    generalize #|mfix|. induction n0 in n, b |- *. simpl.
    destruct n; simpl; congruence.
    destruct n; simpl. intros [= <-]. f_equal.
    destruct n0; simpl; try reflexivity.
    intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma ctxmap_cofix_subst:
    ∀ (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (cofix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    rewrite nth_error_app_ge // in Hnth.
    rewrite fix_context_length in l Hnth.
    destruct d' as [na [b'|] ty]; simpl; auto.
    rewrite subst_consn_ge cofix_subst_length //.
    unfold ids. eexists _, _; split; eauto.
    rewrite Hnth. split; simpl; eauto.
    apply inst_ext.
    rewrite /subst_compose. simpl. intros v.
    rewrite subst_consn_ge ?cofix_subst_length. lia.
    unfold shiftk. f_equal. lia.
    rewrite nth_error_app_lt in Hnth => //.
    pose proof (fix_context_assumption_context mfix1).
    destruct d' as [na [b'|] ty]; simpl; auto.
    elimtype False. eapply nth_error_assumption_context in H; eauto.
    simpl in H; discriminate.
  Qed.

  Lemma ctxmap_fix_subst:
    ∀ (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (fix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    rewrite nth_error_app_ge // in Hnth.
    rewrite fix_context_length in l Hnth.
    destruct d' as [na [b'|] ty]; simpl; auto.
    rewrite subst_consn_ge fix_subst_length //.
    unfold ids. eexists _, _; split; eauto.
    rewrite Hnth. split; simpl; eauto.
    apply inst_ext.
    rewrite /subst_compose. simpl. intros v.
    rewrite subst_consn_ge ?fix_subst_length. lia.
    unfold shiftk. f_equal. lia.
    rewrite nth_error_app_lt in Hnth => //.
    pose proof (fix_context_assumption_context mfix1).
    destruct d' as [na [b'|] ty]; simpl; auto.
    elimtype False. eapply nth_error_assumption_context in H; eauto.
    simpl in H; discriminate.
  Qed.

  Lemma rho_triangle_All_All2_ind:
    ∀ (Γ : context) (brs : list (nat * term)),
    pred1_ctx Σ Γ (rho_ctx Γ) →
    All (λ x : nat * term, pred1_ctx Σ Γ (rho_ctx Γ) → pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x)))
        brs →
    All2 (on_Trel_eq (pred1 Σ Γ (rho_ctx Γ)) snd fst) brs
         (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs).
  Proof.
    intros. rewrite - {1}(map_id brs). eapply All2_map, All_All2; eauto.
  Qed.

  Lemma rho_triangle_All_All2_ind_noeq:
    ∀ (Γ Γ' : context) (brs0 brs1 : list (nat * term)),
      pred1_ctx Σ Γ Γ' →
      All2 (on_Trel_eq (λ x y : term, (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type) snd
                       fst) brs0 brs1 ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) snd) brs1 (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0).
  Proof.
    intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; pcuic.
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
  
   Lemma All2_local_env_sym P Γ Γ' Δ Δ' :
    All2_local_env (on_decl (on_decl_over (fun Γ Γ' t t' => P Γ' Γ t' t) Γ' Γ)) Δ' Δ ->
    All2_local_env (on_decl (on_decl_over P Γ Γ')) Δ Δ'.
  Proof.
    induction 1; constructor; eauto.
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
    psubst Σ Γ' (rho_ctx Γ) (fix_subst mfix1) (map (rho (rho_ctx Γ)) (fix_subst mfix0))
           (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
  Proof.
    intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
    pose proof a0 as a0'. apply All2_rev in a0'.
    revert Hctxs.
    unfold fix_subst, fix_context. simpl.
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
    intros. depelim Hctxs. red in o. simpl in H2, H3. noconf H2; noconf H3.
    red in o. noconf Heqlen. simpl in H.
    rewrite -H.
    econstructor. unfold mapi in IHAll2.
    forward IHAll2 by lia.
    forward IHAll2 by lia.
    forward IHAll2 by lia. rewrite -H in IHAll2.
    rewrite -Hlen in IHAll2.
    apply IHAll2; clear IHAll2.
    rewrite -H in Hctxs.
    apply Hctxs; clear Hctxs.
    clear IHAll2 Hctxs.
    rdestruct r.
    simpl in *. rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
    simp rho; simpl; simp rho.
    econstructor. eauto. clear Hctxs o IHAll2.
    rewrite -fold_fix_context_rho_ctx.
    eapply All2_local_env_pred_fix_ctx. eapply Hctxs'.
    eapply All2_mix. rewrite -fold_fix_context_rho_ctx.
    all:clear IHAll2 Hctxs H o r.
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
    simpl in H2. noconf H2.
  Qed.

(* TODO generalize fix/cofix subst by tFix/tCofix constructor! *)

  Lemma wf_rho_cofix_subst Γ Γ' mfix0 mfix1 :
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
    intros. depelim Hctxs. red in o.
    simpl in H2. noconf H2.
    simpl in H3. noconf H3.
    constructor. unfold mapi in IHAll2.
    forward IHAll2 by lia.
    forward IHAll2 by lia.
    forward IHAll2 by lia. rewrite -Hlen in IHAll2.
    apply IHAll2; clear IHAll2. apply Hctxs; clear Hctxs.
    clear IHAll2 Hctxs. rdestruct r.
    red in o. simpl in *. noconf Heqlen. simpl in H.
    rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
    simp rho; simpl; simp rho.
    econstructor. eauto. clear Hctxs o IHAll2.
    rewrite -fold_fix_context_rho_ctx.
    eapply All2_local_env_pred_fix_ctx. eapply Hctxs'.
    eapply All2_mix. rewrite -fold_fix_context_rho_ctx.
    all:clear IHAll2 Hctxs H o r.
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
    hnf in H2. noconf H2.
  Qed.

  Definition pred1_subst Γ Δ Δ' σ τ :=
  forall x, pred1 Σ Δ Δ' (σ x) (τ x) *
            match option_map decl_body (nth_error Γ x) return Type with
            | Some (Some b) => σ x = τ x
            | _ => True
            end.

  Lemma pred_subst_rho_cofix (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) :
    pred1_ctx Σ Γ Γ' → pred1_ctx Σ Γ' (rho_ctx Γ)
    → All2_local_env
        (on_decl
           (on_decl_over
              (λ (Γ0 Γ'0 : context) (t t0 : term),
               pred1 Σ Γ'0 (rho_ctx Γ0) t0
                     (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
    → All2 (on_Trel eq (λ x : def term, (dname x, rarg x)))
           mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ'
                                (rho_ctx Γ) y
                                (rho (rho_ctx Γ) x)) dtype)
        mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rho_ctx
                                   (Γ ,,, fix_context mfix0)) y
                                (rho
                                   (rho_ctx
                                      (Γ ,,, fix_context mfix0)) x))
           dbody) mfix0 mfix1
    → pred1_subst  (Γ' ,,, fix_context mfix1) Γ'
                  (rho_ctx Γ) (cofix_subst mfix1 ⋅n ids)
                  (cofix_subst
                     (map_fix rho (rho_ctx Γ)
                              (rho_ctx_over
                                 (rho_ctx Γ)
                                 (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros predΓ predΓ' fctx eqf redr redl.
    intros x.
    destruct (leb_spec_Set (S x) #|cofix_subst mfix1|).
    destruct (subst_consn_lt l) as [? [Hb Hb']].
    rewrite Hb'.
    eapply nth_error_cofix_subst in Hb. subst.
    rewrite cofix_subst_length in l.
    rewrite -(All2_length _ _ eqf) in l.
    rewrite -(cofix_subst_length mfix0) in l.
    destruct (subst_consn_lt l) as [b' [Hb0 Hb0']].
    rewrite rho_cofix_subst.
    pose proof (nth_error_map (rho (rho_ctx Γ)) x (cofix_subst mfix0)).
    rewrite Hb0 in H. simpl in H.
    rewrite /subst_consn H.
    eapply nth_error_cofix_subst in Hb0. subst b'.
    cbn. rewrite (All2_length _ _ eqf). constructor; auto.
    simp rho; simpl; simp  rho.
    rewrite -fold_fix_context_rho_ctx. constructor; auto.
    + eapply All2_local_env_pred_fix_ctx. apply fctx.
    + red. clear -wfΣ eqf redr redl.
      eapply All2_sym. apply All2_map_left.
      pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
      eapply All2_impl; eauto. clear X.
      unfold on_Trel in *. simpl. intros x y.
      rewrite fix_context_map_fix rho_ctx_app. intuition auto.
    + pose proof (fix_context_assumption_context mfix1).
      rewrite cofix_subst_length (All2_length _ _ eqf) -(fix_context_length mfix1) in l.
      rewrite nth_error_app_lt //.
      destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
      destruct c as [na [?|] ty] => //.
      move: (nth_error_assumption_context _ _ _ H0 Heq) => //.
    + rewrite cofix_subst_length in l.
      rewrite !subst_consn_ge; try rewrite ?cofix_subst_length ?map_length; try lia.
      now rewrite (All2_length _ _ eqf).
      split. rewrite (All2_length _ _ eqf); pcuic.
      rewrite nth_error_app_ge ?fix_context_length //; try lia.
      destruct option_map as [[o|]|]; auto. now rewrite (All2_length _ _ eqf).
  Qed.

  Lemma pred_subst_rho_fix (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) :
    pred1_ctx Σ Γ Γ' → pred1_ctx Σ Γ' (rho_ctx Γ)
    → All2_local_env
        (on_decl
           (on_decl_over
              (λ (Γ0 Γ'0 : context) (t t0 : term),
               pred1 Σ Γ'0 (rho_ctx Γ0) t0
                     (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
    → All2 (on_Trel eq (λ x : def term, (dname x, rarg x)))
           mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ'
                                (rho_ctx Γ) y
                                (rho (rho_ctx Γ) x)) dtype)
        mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rho_ctx
                                   (Γ ,,, fix_context mfix0)) y
                                (rho
                                   (rho_ctx
                                      (Γ ,,, fix_context mfix0)) x))
           dbody) mfix0 mfix1
    → pred1_subst (Γ' ,,, fix_context mfix1) Γ'
                  (rho_ctx Γ) (fix_subst mfix1 ⋅n ids)
                  (fix_subst
                     (map_fix rho (rho_ctx Γ)
                              (rho_ctx_over
                                 (rho_ctx Γ)
                                 (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros predΓ predΓ' fctx eqf redr redl.
    intros x.
    destruct (leb_spec_Set (S x) #|fix_subst mfix1|).
    destruct (subst_consn_lt l) as [? [Hb Hb']].
    rewrite Hb'.
    eapply nth_error_fix_subst in Hb. subst.
    rewrite fix_subst_length in l.
    rewrite -(All2_length _ _ eqf) in l.
    rewrite -(fix_subst_length mfix0) in l.
    destruct (subst_consn_lt l) as [b' [Hb0 Hb0']].
    rewrite rho_fix_subst.
    pose proof (nth_error_map (rho (rho_ctx Γ)) x (fix_subst mfix0)).
    rewrite Hb0 in H. simpl in H.
    rewrite /subst_consn H.
    eapply nth_error_fix_subst in Hb0. subst b'.
    cbn. rewrite (All2_length _ _ eqf). constructor; auto.
    simp rho; simpl; simp rho.
    rewrite -fold_fix_context_rho_ctx. constructor; auto.
    + eapply All2_local_env_pred_fix_ctx. apply fctx.
    + red. clear -wfΣ eqf redr redl.
      eapply All2_sym. apply All2_map_left.
      pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
      eapply All2_impl; eauto. clear X.
      unfold on_Trel in *. simpl. intros x y.
      rewrite fix_context_map_fix rho_ctx_app. intuition auto.
    + pose proof (fix_context_assumption_context mfix1).
      rewrite fix_subst_length (All2_length _ _ eqf) -(fix_context_length mfix1) in l.
      rewrite nth_error_app_lt //.
      destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
      destruct c as [na [?|] ty] => //.
      move: (nth_error_assumption_context _ _ _ H0 Heq) => //.
    + rewrite fix_subst_length in l.
      rewrite !subst_consn_ge; try rewrite ?fix_subst_length ?map_length; try lia.
      now rewrite (All2_length _ _ eqf).
      split. rewrite (All2_length _ _ eqf); pcuic.
      rewrite nth_error_app_ge ?fix_context_length //; try lia.
      destruct option_map as [[o|]|]; auto. now rewrite (All2_length _ _ eqf).
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
    rewrite - (rho_lift0 (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) Δ')). simpl.
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
    intros. induction Δ in Δ', X0 |- *. depelim X0. destruct Δ'; noconf H. constructor.
    cbn in H. destruct c as [? [?|] ?]; noconf H.
    depelim X0.
    - destruct Δ'. noconf H. destruct c as [? [?|] ?]; noconf H.
      simpl in H. noconf H. simpl in H. noconf H.
      constructor. eapply IHΔ. auto. red. red in o. intros.
      red in o. rewrite !rho_ctx_app. eapply o.
    - destruct Δ'. noconf H. destruct c as [? [?|] ?]; noconf H.
      simpl in H. noconf H. red in o. destruct o.
      constructor. eapply IHΔ. auto. red. red in o, o0. intros.
      rewrite !rho_ctx_app. split; eauto.
      simpl in H. noconf H.
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
    eapply All2_map_right' in a.
    rewrite - fold_fix_context_rho_ctx.
    unfold fix_context. unfold map_fix.
    eapply local_env_telescope.
    cbn.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (dtype def))
                 (fun n decl => lift_decl n 0 decl)).
    rewrite mapi_map. simpl.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (rho (rho_ctx Γ) (dtype def)))
                 (fun n decl => lift_decl n 0 decl)).
    eapply All2_telescope_mapi.
    rewrite !mapi_cst_map.
    eapply All_All2_telescopei; eauto.
  Qed.
  
  Lemma isConstruct_app_pred1 {Γ Δ a b} : pred1 Σ Γ Δ a b -> isConstruct_app a -> isConstruct_app b.
  Proof.
    move=> pr; rewrite /isConstruct_app.
    move e: (decompose_app a) => [hd args].
    apply decompose_app_inv in e. subst a. simpl.
    case: hd pr => // ind n ui.
    move/pred1_mkApps_tConstruct => [args' [-> Hargs']] _.
    rewrite decompose_app_mkApps //.
  Qed.

  Lemma is_constructor_pred1 Γ Γ' n l l' : 
    All2 (pred1 Σ Γ Γ') l l' ->
    is_constructor n l -> is_constructor n l'.
  Proof.
    induction 1 in n |- *.
    - now rewrite /is_constructor nth_error_nil.
    - destruct n; rewrite /is_constructor /=.
      now eapply isConstruct_app_pred1.
      eapply IHX.
  Qed.

  Lemma pred1_subst_pred1_ctx {Γ Δ Δ' σ τ} :
    pred1_subst Γ Δ Δ' σ τ ->
    pred1_ctx Σ Δ Δ'.
  Proof. intros Hrel. destruct (Hrel 0). pcuic. Qed.

  Hint Extern 4 (pred1_ctx ?Σ ?Δ ?Δ') =>
  match goal with
    H : pred1_subst _ Δ Δ' _ _ |- _ =>
    apply (pred1_subst_pred1_ctx H)
  end : pcuic.

  Lemma pred1_subst_Up:
    ∀ (Γ : context) (na : name) (t0 t1 : term) (Δ Δ' : context) (σ τ : nat → term),
      pred1 Σ Δ Δ' t0.[σ] t1.[τ] →
      pred1_subst Γ Δ Δ' σ τ →
      pred1_subst (Γ,, vass na t0) (Δ,, vass na t0.[σ]) (Δ',, vass na t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros Γ na t0 t1 Δ Δ' σ τ X2 Hrel.
    intros x. destruct x; simpl. split; auto. eapply pred1_refl_gen. constructor; eauto with pcuic.
    unfold subst_compose. rewrite - !(lift0_inst 1).
    split. eapply (weakening_pred1_pred1 Σ _ _ [_] [_]); auto.
    constructor. constructor. red. red. eapply X2. eapply Hrel.
    destruct (Hrel x). destruct option_map as [[o|]|]; now rewrite ?y.
  Qed.

  Lemma pred1_subst_vdef_Up:
    ∀ (Γ : context) (na : name) (b0 b1 t0 t1 : term) (Δ Δ' : context) (σ τ : nat → term),
      pred1 Σ Δ Δ' t0.[σ] t1.[τ] →
      pred1 Σ Δ Δ' b0.[σ] b1.[τ] →
      pred1_subst Γ Δ Δ' σ τ →
      pred1_subst (Γ,, vdef na b0 t0) (Δ,, vdef na b0.[σ] t0.[σ]) (Δ',, vdef na b1.[τ] t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros Γ na b0 b1 t0 t1 Δ Δ' σ τ Xt Xb Hrel.
    intros x. destruct x; simpl. split; auto. eapply pred1_refl_gen. constructor; eauto with pcuic.
    unfold subst_compose. rewrite - !(lift0_inst 1).
    split. eapply (weakening_pred1_pred1 Σ _ _ [_] [_]); auto.
    constructor. constructor. red. split; red. eapply Xb. apply Xt.
    eapply Hrel.
    destruct (Hrel x). destruct option_map as [[o|]|]; now rewrite ?y.
  Qed.

  Lemma pred1_subst_Upn:
    ∀ (Γ : context) (Δ Δ' : context) (σ τ : nat → term) (Γ' Δ0 Δ1 : context) n,
      #|Γ'| = #|Δ0| -> #|Δ0| = #|Δ1| -> n = #|Δ0| ->
                                                  pred1_subst Γ Δ Δ' σ τ →
                                                  All2_local_env_over (pred1 Σ) Δ Δ' Δ0 Δ1 ->
                                                  pred1_subst (Γ ,,, Γ') (Δ ,,, Δ0) (Δ' ,,, Δ1) (⇑^n σ) (⇑^n τ).
  Proof.
    intros * len0 len1 -> Hrel.
    red. intros H x.
    destruct (leb_spec_Set (S x) #|idsn #|Δ0| |).
    unfold Upn.
    specialize (subst_consn_lt l).
    intros [tx [Hdecl Heq]].
    rewrite !Heq. split. eapply pred1_refl_gen. auto.
    eapply All2_local_env_over_app; auto. destruct (Hrel 0). pcuic.
    destruct option_map as [[o|]|]; auto.
    unfold Upn.
    rewrite !subst_consn_ge. lia. lia.
    rewrite idsn_length. specialize (Hrel (x - #|Δ0|)).
    destruct Hrel.
    split. unfold subst_compose. rewrite - !(lift0_inst _).
    rewrite {3}len1.
    eapply weakening_pred1_pred1; auto.
    rewrite nth_error_app_ge. rewrite idsn_length in l. lia.
    rewrite len0.
    destruct option_map as [[o|]|]; auto.
    unfold subst_compose. simpl. rewrite y. reflexivity.
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
  
  Lemma inst_iota_red s pars c args brs :
    inst s (iota_red pars c args brs) =
    iota_red pars c (List.map (inst s) args) (List.map (on_snd (inst s)) brs).
  Proof.
    unfold iota_red. rewrite !inst_mkApps. f_equal; auto using map_skipn.
    rewrite nth_map; simpl; auto.
  Qed.

  Lemma All2_local_env_fold_context P f g Γ Δ :
    All2_local_env (fun Γ Δ p T U => P (fold_context f Γ) (fold_context g Δ)
                                        (option_map (fun '(b, b') => (f #|Γ| b, g #|Δ| b')) p)
                                        (f #|Γ| T) (g #|Δ| U)) Γ Δ ->
    All2_local_env P (fold_context f Γ) (fold_context g Δ).
  Proof.
    induction 1; rewrite ?fold_context_snoc0; constructor; auto.
  Qed.

  Lemma All2_local_env_fix_context P σ τ Γ Δ :
    All2_local_env (fun Γ Δ p T U => P (inst_context σ Γ) (inst_context τ Δ)
                                        (option_map (fun '(b, b') => (b.[⇑^#|Γ| σ], b'.[⇑^#|Δ| τ])) p)
                                        (T.[⇑^#|Γ| σ]) (U.[⇑^#|Δ| τ])) Γ Δ ->
    All2_local_env P (inst_context σ Γ) (inst_context τ Δ).
  Proof.
    eapply All2_local_env_fold_context.
  Qed.

  Lemma All2_local_env_impl P Q Γ Δ :
    All2_local_env P Γ Δ ->
    (forall Γ Δ t T U, #|Γ| = #|Δ| -> P Γ Δ t T U -> Q Γ Δ t T U) ->
    All2_local_env Q Γ Δ.
  Proof.
    intros H HP. pose proof (All2_local_env_length H).
    induction H; constructor; simpl; eauto.
  Qed.

  Lemma decompose_app_rec_inst s t l :
    let (f, a) := decompose_app_rec t l in
    inst s f = f ->
    decompose_app_rec (inst s t) (map (inst s) l)  = (f, map (inst s) a).
  Proof.
    induction t in s, l |- *; simpl; auto; try congruence.

    intros ->. simpl. reflexivity.
    specialize (IHt1 s (t2 :: l)).
    destruct decompose_app_rec. intros H. rewrite IHt1; auto.
  Qed.

  Lemma decompose_app_inst s t f a :
    decompose_app t = (f, a) -> inst s f = f ->
    decompose_app (inst s t) = (inst s f, map (inst s) a).
  Proof.
    generalize (decompose_app_rec_inst s t []).
    unfold decompose_app. destruct decompose_app_rec.
    move=> Heq [= <- <-] Heq'. now rewrite Heq' (Heq Heq').
  Qed.
  Hint Rewrite decompose_app_inst using auto : lift.

  Lemma inst_is_constructor:
    forall (args : list term) (narg : nat) s,
      is_constructor narg args = true -> is_constructor narg (map (inst s) args) = true.
  Proof.
    intros args narg.
    unfold is_constructor; intros.
    rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
    unfold isConstruct_app in *.
    destruct (decompose_app t) eqn:Heq. eapply decompose_app_inst in Heq as ->.
    destruct t0; try discriminate || reflexivity.
    destruct t0; try discriminate || reflexivity.
  Qed.
  Hint Resolve inst_is_constructor : core.

  Lemma strong_substitutivity Γ Γ' Δ Δ' s t σ τ :
    pred1 Σ Γ Γ' s t ->
    ctxmap Γ Δ σ ->
    ctxmap Γ' Δ' τ ->
    pred1_subst Γ Δ Δ' σ τ ->
    pred1 Σ Δ Δ' s.[σ] t.[τ].
  Proof.
    intros redst.
    revert Δ Δ' σ τ.
    revert Γ Γ' s t redst.
    set (P' := fun Γ Γ' => pred1_ctx Σ Γ Γ').
    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); subst P';
      try (intros until Δ; intros Δ' σ τ Hσ Hτ Hrel); trivial.

    (* induction redst using ; sigma; intros Δ Δ' σ τ Hσ Hτ Hrel. *)
    all:eauto 2 with pcuic.

    (** Beta case *)
    1:{ eapply simpl_pred; simpl; rewrite ?up_Upn; sigma; try reflexivity.
        specialize (X2 _ _ _ _ Hσ Hτ Hrel).
        specialize (X0 (Δ ,, vass na t0.[σ]) (Δ' ,, vass na t1.[τ]) (⇑ σ) (⇑ τ)).
        forward X0. eapply Up_ctxmap; eauto.
        forward X0. eapply Up_ctxmap; eauto.
        forward X0. eapply pred1_subst_Up; auto.
        specialize (X4 _ _ _ _ Hσ Hτ Hrel).
        eapply (pred_beta _ _ _ _ _ _ _ _ _ _ X2 X0 X4). }
        

    (** Let-in delta case *)
    2:{ rewrite lift_rename rename_inst.
        simpl. rewrite lift_renaming_0. clear X0.
        destruct (nth_error_pred1_ctx _ _ X H) as [bodyΓ [? ?]]; eauto.
        move e after H.
        pose proof (pred1_pred1_ctx _ (fst (Hrel i))).
        destruct (nth_error Γ' i) eqn:HΓ'i; noconf H. hnf in H.
        destruct (nth_error Γ i) eqn:HΓi; noconf e. hnf in H.
        pose proof (Hσ _ _ HΓi) as Hc. rewrite H in Hc.
        destruct Hc as [σi [b' [eqi' [Hnth Hb']]]].
        pose proof (Hτ _ _ HΓ'i) as Hc'. rewrite H0 in Hc'.
        destruct Hc' as [τi [b'' [eqi'' [Hnth' Hb'']]]].
        destruct (nth_error_pred1_ctx _ _ X0 Hnth') as [bodyΔ [? ?]].
        destruct (Hrel i) as [_ Hi]. rewrite HΓi in Hi. simpl in Hi. rewrite H in Hi.
        rewrite Hi in eqi'. rewrite eqi' in eqi''. noconf eqi''.
        simpl_pred.
        eapply refine_pred.
        now rewrite -ren_shiftk -Hb''.
        rewrite Hi eqi'. rewrite -lift0_inst. constructor. auto. auto. }

    (** Zeta *)
    1:{ sigma.
        econstructor; eauto.
        eapply X4; try apply Up_ctxmap; auto.
        apply pred1_subst_vdef_Up; auto. }

    - simpl. eapply Hrel.

    - simpl. rewrite inst_iota_red.
      sigma. econstructor.
      now eapply pred1_subst_pred1_ctx.
      solve_all. solve_all.
      red in X2. solve_all.

    - sigma.
      unfold unfold_fix in *.
      destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic. }
      econstructor; eauto with pcuic.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_fix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_fix_subst. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?fix_subst_length //.
        rewrite subst_consn_compose. now sigma.
      + solve_all.

    - (* CoFix Case *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic. }
      econstructor. eapply pred1_subst_pred1_ctx; eauto.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X8 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?cofix_subst_length //.
        rewrite subst_consn_compose. now sigma.
      + solve_all. (* args *)
      + eauto.
      + red in X7. solve_all.

    - (* Proj Cofix *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic. }
      econstructor. eapply pred1_subst_pred1_ctx; eauto.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?cofix_subst_length //.
        rewrite subst_consn_compose. now sigma.
      + solve_all. (* args *)

    - simpl. rewrite inst_closed0.
      rewrite closedn_subst_instance_constr; auto.
      eapply declared_decl_closed in H; auto. hnf in H. rewrite H0 in H.
      rtoProp; auto.
      econstructor; eauto with pcuic.

    - (* Proj-Construct *)
      simpl. sigma. econstructor. pcuic. eapply All2_map. solve_all.
      rewrite nth_error_map. now rewrite H.

    - (* Lambda congruence *)
      sigma. econstructor. pcuic. eapply X2. eapply Up_ctxmap; pcuic.
      eapply Up_ctxmap; pcuic. now eapply pred1_subst_Up.

    - (* App congruence *)
      sigma; auto with pcuic.

    - (* Let congruence *)
      sigma. econstructor; eauto. eapply X4; try apply Up_ctxmap; auto.
      eapply pred1_subst_vdef_Up; eauto.

    - (* Case congruence *)
      simpl. econstructor; eauto. red in X3. solve_all.

    - (* Proj congruence *)
      sigma; pcuic.

    - (* Fix congruence *)
      sigma.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { eapply All2_local_env_fix_context.
        pose proof (pred1_subst_pred1_ctx Hrel). apply All2_local_env_length in X4.
        clear -wfΣ X4 X2 Hσ Hτ Hrel.
        induction X2; constructor; simpl in *; auto.
        + hnf in p |- *. simpl. eapply p; auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
           apply (All2_local_env_length X2).
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic.
        + hnf in p |- *. simpl. split; eapply p; auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
           apply (All2_local_env_length X2).
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto. auto with pcuic.
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic. }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length _ _ X3).
      solve_all.
      unfold on_Trel in *. simpl. intuition auto.
      unfold on_Trel in *. simpl. intuition auto.
      eapply b; auto with pcuic.
      rewrite -{1}(fix_context_length mfix0). auto with pcuic.
      rewrite -{1}(fix_context_length mfix1). auto with pcuic.
      rewrite -H. apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* CoFix congruence *)
      sigma.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { eapply All2_local_env_fix_context.
        pose proof (pred1_subst_pred1_ctx Hrel). apply All2_local_env_length in X4.
        clear -wfΣ X4 X2 Hσ Hτ Hrel.
        induction X2; constructor; simpl in *; auto.
        + hnf in p |- *. simpl. eapply p; auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
           apply (All2_local_env_length X2).
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic.
        + hnf in p |- *. simpl. split; eapply p; auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
           apply (All2_local_env_length X2).
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto. auto with pcuic.
           apply All2_local_env_app. apply All2_local_env_app_inv. pcuic.
           now eapply All2_local_env_fold_context. destruct (Hrel 0); auto with pcuic. }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length _ _ X3).
      solve_all.
      unfold on_Trel in *. simpl. intuition auto.
      unfold on_Trel in *. simpl. intuition auto.
      eapply b; auto with pcuic.
      rewrite -{1}(fix_context_length mfix0). auto with pcuic.
      rewrite -{1}(fix_context_length mfix1). auto with pcuic.
      rewrite -H. apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* Prod Congruence *)
      sigma. constructor; auto with pcuic;
      eapply X2; auto with pcuic; try eapply Up_ctxmap; auto with pcuic.
      apply pred1_subst_Up; auto.

    - sigma. simpl. constructor; auto with pcuic. solve_all.

    - rewrite !pred_atom_inst; auto. eapply pred1_refl_gen; auto with pcuic.
  Qed.


  Lemma triangle Γ Δ t u :
  let Pctx :=
      fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Γ) in
  pred1 Σ Γ Δ t u -> pred1 Σ Δ (rho_ctx Γ) u (rho (rho_ctx Γ) t).
  Proof with solve_discr.
    intros Pctx H. revert Γ Δ t u H.
    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      subst Pctx; intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [simpl; econstructor; simpl; eauto].

    simpl.
    - induction X0; simpl; depelim predΓ'; constructor; rewrite ?app_context_nil_l; eauto.
      all:simpl NoConfusion in *; noconf H; noconf H0; auto.

    - simpl.
      rewrite (rho_app_lambda _ _ _ _ _ []).
      eapply (substitution0_pred1); simpl in *. eauto. eauto.
      rewrite app_context_nil_l in X0.
      eapply X0.

    - simp rho.
      eapply (substitution0_let_pred1); simpl in *. eauto. eauto.
      rewrite app_context_nil_l in X4.
      eapply X4.

    - simp rho.
      destruct nth_error eqn:Heq. simpl in X0.
      pose proof Heq. apply nth_error_Some_length in Heq.
      destruct c as [na [?|] ?]; noconf heq_option_map.
      simpl in X0.
      eapply (f_equal (option_map decl_body)) in H.
      eapply nth_error_pred1_ctx_l in H; eauto.
      destruct H. intuition. rewrite a. simp rho.
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

    - simp rho. simpl in *.
      destruct option_map eqn:Heq.
      destruct o. constructor; auto.
      constructor. auto.
      constructor. auto.

    - simpl in X0. cbn.
      rewrite rho_app_case.
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec ind ind); try discriminate.
      2:{ congruence. }
      unfold iota_red. eapply pred_mkApps; eauto.
      eapply pred_snd_nth. red in X2.
      now eapply rho_triangle_All_All2_ind_noeq. auto.
      eapply All2_skipn. eapply All2_sym.
      rewrite - {1} (map_id args1). eapply All2_map, All2_impl; eauto. simpl. intuition.

    - (* Fix reduction *)
      unfold unfold_fix in heq_unfold_fix |- *.
      rewrite rho_app_fix.
      destruct nth_error eqn:Heq; noconf heq_unfold_fix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]].
      destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      rewrite Hnth. simpl.
      destruct args0. depelim X4. unfold is_constructor in heq_is_constructor.
      rewrite nth_error_nil in heq_is_constructor => //.
      pose proof Hnth.
      eapply All2_nth_error_Some in H; eauto.
      destruct H as [fn' [Hnth' [? ?]]].
      destruct t', d.
      simpl in * |-. noconf Heq. destruct o, p as [[ol ol'] or].
      simpl in * |-. noconf or.
      move: heq_is_constructor.
      revert X4. generalize (t :: args0). simpl.
      clear t args0. intros args0 Hargs isc.
      simpl. rewrite isc.
      eapply pred_mkApps.
      rewrite rho_ctx_app in Hreleq1.
      rewrite !subst_inst. simpl_pred.
      rewrite /rho_fix_context -fold_fix_context_rho_ctx.
      eapply strong_substitutivity; eauto.
      apply ctxmap_fix_subst.
      rewrite -rho_fix_subst -{1}fix_context_map_fix.
      apply ctxmap_fix_subst.
      rewrite -rho_fix_subst.
      eapply All2_prop2_eq_split in X3.
      apply pred_subst_rho_fix; intuition auto.
      eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel in *.
      intuition eauto.

    - (* Case-CoFix reduction *)
      destruct ip.
      rewrite rho_app_case.
      rewrite decompose_app_mkApps; auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix. simpl.
      eapply All2_prop2_eq_split in X3. intuition.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Ht' Hrel]]. rewrite Ht'. simpl.
      eapply pred_case. eauto. eapply pred_mkApps.
      red in Hrel. destruct Hrel.
      rewrite rho_ctx_app in p2.
      rewrite - fold_fix_context_rho_ctx.
      set (rhoΓ := rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) in *.
      rewrite !subst_inst. eapply simpl_pred; try now sigma.
      eapply strong_substitutivity; eauto. apply ctxmap_cofix_subst.
      unfold rhoΓ.
      rewrite -{1}fix_context_map_fix.
      rewrite -rho_cofix_subst.
      now eapply ctxmap_cofix_subst.
      rewrite -rho_cofix_subst.
      now eapply pred_subst_rho_cofix; auto.
      eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
      eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel in *.
      intuition eauto.

    - (* Proj-Cofix reduction *)
      simpl.
      destruct p as [[ind pars] arg].
      rewrite rho_app_proj.
      rewrite decompose_app_mkApps. auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      unfold map_fix. rewrite Hnth /=.
      econstructor. eapply pred_mkApps; eauto.
      rewrite - fold_fix_context_rho_ctx.
      rewrite rho_ctx_app in Hreleq1.
      eapply substitution_pred1; eauto.
      { eapply wf_rho_cofix_subst; eauto.
        now eapply All2_length in X3. }
      eapply All2_sym, All2_map_left, All2_impl; eauto; simpl; intuition eauto.

    - simpl; simp rho; simpl.
      simpl in X0. red in H. rewrite H /= heq_cst_body /=.
      now eapply pred1_refl_gen.

    - simpl in *. simp rho; simpl.
      destruct (lookup_env Σ c) eqn:Heq; pcuic. destruct g; pcuic.
      destruct cst_body eqn:Heq'; pcuic.
      
    - simpl in *. rewrite rho_app_proj.
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec i i) => //.
      eapply All2_nth_error_Some_right in heq_nth_error as [t' [? ?]]; eauto.
      simpl in y. rewrite e0. simpl.
      auto.

    - simpl; simp rho. eapply pred_abs; auto. unfold snoc in *. simpl in X2.
      rewrite app_context_nil_l in X2. apply X2.

    - (** Application *)
      simp rho.
      destruct view_lambda_fix_app. simpl; simp rho; simpl.
      + (* Fix at head *)
        destruct (rho_fix_elim (rho_ctx Γ) mfix i l).
        * rewrite /unfold_fix {1}/map_fix nth_error_map e /=. 
          eapply (is_constructor_app_ge (rarg d) _ _) in i0 => //.
          rewrite -> i0.
          rewrite map_app - !mkApps_nested.
          eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
          rewrite - fold_fix_context_rho_ctx.
          rewrite rho_fix_subst. subst fn.
          rewrite /rho_fix_context in X0.
          rewrite fold_fix_context_rho_ctx.
          auto.
          repeat constructor; auto.
        * simp rho in X0.
          simpl in X0. simp rho in X0.
          destruct (rho_fix_elim (rho_ctx Γ) mfix i (l ++ [a])).
          (* Shorter application does not reduce *)
          ** (* Longer application reduces *)
            rewrite e in i0.
            rewrite /unfold_fix nth_error_map e /= i1.
            simpl.
            destruct (pred1_mkApps_tFix_inv _ _ _ _ _ _ _ _ e i0 X) as
              [mfix1 [args1 [[HM1 Hmfix] Hargs]]].
            subst M1.
            rewrite [tApp _ _](mkApps_nested _ _ [N1]).
            red in Hmfix.
            eapply All2_nth_error_Some in Hmfix; eauto.
            destruct Hmfix as [d' [Hd' [eqd' [pred' eqsd']]]].
            eapply (pred1_mkApps_tFix_refl_inv _ _ _ mfix1) in X0; eauto.
            2:{ noconf eqsd'. simpl in H; noconf H.
                rewrite -H0.
                pose proof (All2_length _ _ Hargs).
                unfold is_constructor in i1.
                move: i1 i0.
                elim: nth_error_spec => //.
                rewrite app_length; intros x hnth. simpl.
                unfold is_constructor.
                elim: nth_error_spec => // x' hnth' rargl rargsl.
                destruct (eq_dec (rarg d) #|l|). lia.
                rewrite nth_error_app_lt in hnth. lia. rewrite hnth in hnth'.
                noconf hnth'. intros. rewrite i1 in i0 => //.
                destruct (nth_error args1 (rarg d)) eqn:hnth'' => //.
                eapply nth_error_Some_length in hnth''. lia. }
            move: X0 => [redo redargs].
            rewrite map_app.
            eapply pred_fix; eauto with pcuic.
            eapply pred1_rho_fix_context_2; auto with pcuic.
            red in redo.
            solve_all.
            unfold on_Trel in *. intuition auto. now noconf b0.
            unfold unfold_fix. rewrite nth_error_map e /=.
            rewrite map_fix_subst /= //.
            intros n.  simp rho; simpl; now simp rho.
            move: i1.
            eapply is_constructor_pred1.
            eapply All2_app; eauto.
            eapply All2_app => //. repeat constructor; auto. 

          ** (* None reduce *)
            simpl. rewrite map_app.
            rewrite /unfold_fix nth_error_map.
            destruct nth_error eqn:hnth => /=.
            destruct (is_constructor (rarg d) (l ++ [a])) => //.
            rewrite -mkApps_nested.
            apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
            repeat constructor; auto.
            rewrite -mkApps_nested.
            apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
            repeat constructor; auto.

      + (* Beta at top *)
        rewrite rho_app_lambda' in X0.
        destruct l. simpl in X.
        depelim X. solve_discr.
        simp rho in X4. 
        depelim X4... econstructor; eauto.
        discriminate.
        simpl. simp rho.
        rewrite map_app -mkApps_nested.
        constructor; eauto.
      
      + (* No head redex *)
        simpl. constructor; auto.

    - simpl; simp rho; simpl. eapply pred_zeta; eauto.
      now simpl in X4; rewrite app_context_nil_l in X4.

    - (* Case reduction *)
      destruct ind.
      rewrite rho_app_case.
      destruct (decompose_app c0) eqn:Heq. simpl.
      destruct (construct_cofix_discr t) eqn:Heq'.
      destruct t; noconf Heq'.
      + (* Iota *)
        apply decompose_app_inv in Heq.
        subst c0. simpl.
        simp rho.
        simpl. simp rho in X2.
        change eq_inductive with (@eqb inductive _).
        destruct (eqb_spec i ind). subst ind.
        eapply pred1_mkApps_tConstruct in X1 as [args' [? ?]]. subst c1.
        eapply pred1_mkApps_refl_tConstruct in X2.
        econstructor; eauto. pcuic.
        eapply All2_sym, All2_map_left, All2_impl; eauto.
        intros. hnf in X1. destruct X1. unfold on_Trel in *.
        intuition pcuic.
        econstructor; pcuic.
        eapply All2_sym, All2_map_left, All2_impl; eauto.
        intros. unfold on_Trel in *. intuition pcuic.

      + (* CoFix *)
        apply decompose_app_inv in Heq.
        subst c0. simpl. simp rho.
        simpl. simp rho in X2.
        eapply pred1_mkApps_tCoFix_inv in X1 as [mfix' [idx' [[? ?] ?]]].
        subst c1.
        simpl in X2. eapply pred1_mkApps_tCoFix_refl_inv in X2.
        intuition.
        eapply All2_prop2_eq_split in a1. intuition.
        unfold unfold_cofix.
        assert (All2 (on_Trel eq dname) mfix'
                    (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
        { eapply All2_impl; [eapply b0|]; pcuic. }
        pose proof (All2_mix a1 X1).
        eapply pred1_rho_fix_context_2 in X2; pcuic.
        rewrite - fold_fix_context_rho_ctx in X2.
        rewrite fix_context_map_fix in X2.
        eapply rho_All_All2_local_env_inv in X2; pcuic.
        rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.

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
              rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
              eapply All2_mix. eauto.
              now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
          --- unfold unfold_cofix.
              rewrite nth_error_map.
              rewrite H. simpl. f_equal. f_equal.
              unfold map_fix.
              rewrite fold_fix_context_rho_ctx.
              rewrite (map_cofix_subst _ (fun Γ Γ' => rho (Γ ,,,  Γ'))) //.
              intros. simp rho; simpl; simp rho. reflexivity.
          --- apply All2_sym. eapply All2_map_left. eapply All2_impl; eauto.
              unfold on_Trel in *.
              intros. intuition pcuic.

        * eapply pred_case; eauto.
          eapply pred_mkApps. constructor. pcuic.
          --- rewrite /rho_fix_context - fold_fix_context_rho_ctx.
              eapply All2_local_env_pred_fix_ctx.
              eapply All2_prop2_eq_split in a. intuition auto.
              eapply All2_local_env_sym.
              pcuic.

          --- eapply All2_mix; pcuic.
              rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
              now rewrite /rho_fix_context - fold_fix_context_rho_ctx.
              eapply All2_mix; pcuic.
          --- pcuic.
          --- eapply All2_sym, All2_map_left, All2_impl; eauto.
              unfold on_Trel in *.
              intros. intuition pcuic.

      + apply decompose_app_inv in Heq. subst c0.
        assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) snd fst) brs1
                    (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0)).
        { eapply All2_sym, All2_map_left, All2_impl; eauto.
          unfold on_Trel in *.
          intros. intuition pcuic. }
        destruct t; try discriminate; simpl; pcuic.

    - (* Proj *)
      simpl.
      destruct p as [[ind pars] arg].
      rewrite rho_app_proj.
      destruct decompose_app eqn:Heq.
      destruct (view_construct_cofix t).
      + apply decompose_app_inv in Heq.
        subst c. simpl. simp rho in X0 |- *.
        pose proof (pred1_pred1_ctx _ X0).
        eapply pred1_mkApps_tConstruct in X as [args' [? ?]]; subst.
        eapply pred1_mkApps_refl_tConstruct in X0.
        destruct nth_error eqn:Heq.
        change eq_inductive with (@eqb inductive _).
        destruct (eqb_spec ind c0); subst.
        econstructor; eauto.
        now rewrite nth_error_map Heq.
        eapply pred_proj_congr, pred_mkApps; auto with pcuic.
        destruct eq_inductive. constructor; auto.
        eapply pred_mkApps; auto.
        econstructor; eauto.
        constructor; auto.
        eapply pred_mkApps; auto.
        econstructor; eauto.

      + apply decompose_app_inv in Heq.
        subst c. simpl.
        simp rho in X0 |- *.
        eapply pred1_mkApps_tCoFix_inv in X as [mfix' [idx' [[? ?] ?]]].
        subst c'.
        simpl in a.
        pose proof X0.
        eapply pred1_mkApps_tCoFix_refl_inv in X0.
        destruct X0.
        unfold unfold_cofix.
        eapply All2_prop2_eq_split in a1. intuition auto.
        assert (All2 (on_Trel eq dname) mfix'
                    (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
        { eapply All2_impl; [eapply b|]; pcuic. }
        pose proof (All2_mix a1 X0) as X2.
        eapply pred1_rho_fix_context_2 in X2; pcuic.
        rewrite - fold_fix_context_rho_ctx in X2.
        rewrite fix_context_map_fix in X2.
        eapply rho_All_All2_local_env_inv in X2; pcuic.
        rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.
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
              rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
              eapply All2_mix. eauto.
              now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b.
          --- unfold unfold_cofix.
              rewrite nth_error_map.
              rewrite H. simpl. f_equal. f_equal.
              unfold map_fix.
              rewrite fold_fix_context_rho_ctx. auto.
              rewrite (map_cofix_subst _ (fun Γ Γ' => rho (Γ ,,,  Γ'))) //.
              intros. simp rho; simpl; simp rho. reflexivity.

        * eapply pred_proj_congr; eauto.

      + eapply decompose_app_inv in Heq. subst c.
        destruct t; noconf d; econstructor; eauto.

    - simp rho; simpl; simp rho.
      rewrite /rho_fix_context - fold_fix_context_rho_ctx.
      constructor; eauto.
      now eapply All2_local_env_pred_fix_ctx. red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho; simpl; simp rho.
      rewrite - fold_fix_context_rho_ctx.
      constructor; eauto.
      now eapply All2_local_env_pred_fix_ctx. red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho; simpl; econstructor; eauto. simpl in X2. now rewrite !app_context_nil_l in X2.
    - simpl in *. simp rho. constructor. eauto. eapply All2_sym, All2_map_left, All2_impl. eauto.
      intros. simpl in X. intuition.
    - destruct t; noconf H; simpl; constructor; eauto.
  Qed.
End Rho.

(* The diamond lemma for parallel reduction follows directly from the triangle lemma. *)

Corollary pred1_diamond {cf : checker_flags} {Σ : global_env} {Γ Δ Δ' t u v} :
  wf Σ ->
  pred1 Σ Γ Δ t u ->
  pred1 Σ Γ Δ' t v ->
  pred1 Σ Δ (rho_ctx Σ Γ) u (rho Σ (rho_ctx Σ Γ) t) *
  pred1 Σ Δ' (rho_ctx Σ Γ) v (rho Σ (rho_ctx Σ Γ) t).
Proof.
  intros.
  split; eapply triangle; auto.
Qed.

Print Assumptions pred1_diamond.
