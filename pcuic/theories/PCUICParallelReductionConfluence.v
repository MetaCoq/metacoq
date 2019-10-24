(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From MetaCoq Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICSize
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution
     PCUICReflect PCUICClosed PCUICParallelReduction.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require CMorphisms.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Derive Signature for pred1 All2_local_env.

Local Set Keyed Unification.
Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Require Import Morphisms.

Instance ren_ext : Morphisms.Proper (`=1` ==> `=1`)%signature ren.
Proof.
  reduce_goal. unfold ren. now rewrite H.
Qed.

Lemma shiftn0 r : shiftn 0 r =1 r.
Proof.
  intros x.
  unfold shiftn. destruct (Nat.ltb_spec x 0). lia.
  rewrite Nat.sub_0_r. lia.
Qed.

Lemma shiftnS n r : shiftn (S n) r =1 shiftn 1 (shiftn n r).
Proof.
  intros x. unfold shiftn.
  destruct x. simpl. auto.
  simpl. rewrite Nat.sub_0_r.
  destruct (Nat.ltb_spec x n).
  destruct (Nat.ltb_spec (S x) (S n)); auto. lia.
  destruct (Nat.ltb_spec (S x) (S n)); auto. lia.
Qed.

Definition rename_context r Γ :=
  fold_context (fun k => rename (shiftn k r)) Γ.
Local Open Scope sigma_scope.

Definition inst_context s Γ :=
  fold_context (fun k => inst (⇑^k s)) Γ.

Definition rename_context_snoc0 r Γ d : rename_context r (d :: Γ) = rename_context r Γ ,, map_decl (rename (shiftn #|Γ| r)) d.
Proof. unfold rename_context. now rewrite fold_context_snoc0. Qed.
Hint Rewrite rename_context_snoc0 : lift.

Lemma rename_context_snoc r Γ d : rename_context r (Γ ,, d) = rename_context r Γ ,, map_decl (rename (shiftn #|Γ| r)) d.
Proof.
  unfold snoc. apply rename_context_snoc0.
Qed.
Hint Rewrite rename_context_snoc : lift.

Lemma rename_context_alt r Γ :
  rename_context r Γ =
  mapi (fun k' d => map_decl (rename (shiftn (Nat.pred #|Γ| - k') r)) d) Γ.
Proof.
  unfold rename_context. apply fold_context_alt.
Qed.

Definition inst_context_snoc0 s Γ d :
  inst_context s (d :: Γ) =
  inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof. unfold inst_context. now rewrite fold_context_snoc0. Qed.
Hint Rewrite inst_context_snoc0 : lift.

Lemma inst_context_snoc s Γ d : inst_context s (Γ ,, d) = inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof.
  unfold snoc. apply inst_context_snoc0.
Qed.
Hint Rewrite inst_context_snoc : lift.

Lemma inst_context_alt s Γ :
  inst_context s Γ =
  mapi (fun k' d => map_decl (inst (⇑^(Nat.pred #|Γ| - k') s)) d) Γ.
Proof.
  unfold inst_context. apply fold_context_alt.
Qed.

Lemma inst_context_length s Γ : #|inst_context s Γ| = #|Γ|.
Proof. apply fold_context_length. Qed.

Hint Rewrite @subst_consn_nil @subst_consn_tip : sigma.

Lemma subst_consn_shiftn n l σ : #|l| = n -> ↑^n ∘ (l ⋅n σ) =1 σ.
Proof.
  induction n in l |- *; simpl; intros; autorewrite with sigma.
  - destruct l; try discriminate. simpl; autorewrite with sigma. reflexivity.
  - destruct l; try discriminate. simpl in *.
    rewrite subst_consn_subst_cons.
    simpl; autorewrite with sigma. apply IHn. lia.
Qed.

Lemma shiftn_consn_idsn n σ : ↑^n ∘ ⇑^n σ =1 σ ∘ ↑^n.
Proof.
  unfold Upn. rewrite subst_consn_shiftn. reflexivity.
  now rewrite idsn_length.
Qed.

Lemma subst10_inst a b τ : b {0 := a}.[τ] = (b.[⇑ τ] {0 := a.[τ]}).
Proof.
  unfold subst10. simpl. rewrite !subst_inst.
  now unfold Upn, Up; autorewrite with sigma.
Qed.

Lemma lift_renaming_0 k : ren (lift_renaming k 0) = ren (Nat.add k).
Proof. reflexivity. Qed.

Lemma lift0_inst n t : lift0 n t = t.[↑^n].
Proof. by rewrite lift_rename rename_inst lift_renaming_0 -ren_shiftk. Qed.

Lemma map_vass_map_def g l r :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (rename r) g) l)) =
  (mapi (fun i d => map_decl (rename (shiftn i r)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite !lift0_inst. rewrite !rename_inst.
  autorewrite with sigma. rewrite -ren_shiftn up_Upn.
  rewrite shiftn_consn_idsn. reflexivity.
Qed.

Lemma rename_fix_context r :
  ∀ (mfix : list (def term)),
    fix_context (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix) =
    rename_context r (fix_context mfix).
Proof.
  intros mfix. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (rename_context_alt r (fix_context mfix)).
  unfold map_decl. now rewrite mapi_length fix_context_length.
Qed.

Lemma map_vass_map_def_inst g l s :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (inst s) g) l)) =
  (mapi (fun i d => map_decl (inst (⇑^i s)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite !lift0_inst.
  autorewrite with sigma.
  rewrite shiftn_consn_idsn. reflexivity.
Qed.

Lemma inst_fix_context:
  forall (mfix : list (def term)) s,
    fix_context (map (map_def (inst s) (inst (⇑^#|mfix| s))) mfix) =
    inst_context s (fix_context mfix).
Proof.
  intros mfix s. unfold fix_context.
  rewrite map_vass_map_def_inst rev_mapi.
  fold (fix_context mfix).
  rewrite (inst_context_alt s (fix_context mfix)).
   now rewrite /subst_decl mapi_length fix_context_length.
Qed.


Lemma mkApps_eq_decompose_app_rec {f args t l} :
  mkApps f args = t ->
  ~~ isApp f ->
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
  ~~ isApp f ->
  match decompose_app t with
  | (f', args') => f' = f /\ t = mkApps f' args'
  end.
Proof.
  intros. apply (@mkApps_eq_decompose_app_rec f args t []); auto.
Qed.

Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
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
    (forall (s : String.string) (u : list Level.t), P (tConst s u)) ->
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
  revert t. set(foo:=Tactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size). simpl. clear H0.
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

  Lemma mkApps_eq_decompose_app {t t' l l'} :
    mkApps t l = mkApps t' l' ->
    decompose_app_rec t l = decompose_app_rec t' l'.
  Proof.
    induction l in t, t', l' |- *; simpl.
    - intros ->. rewrite !decompose_app_rec_mkApps.
      now rewrite app_nil_r.
    - intros H. apply (IHl _ _ _ H).
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

  Lemma pred1_mkApps_tFix_inv (Σ : global_env) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                                       dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ Δ) ) args0 args1 } }%type) +
    ({ mfix1 & { args1 & { narg & { fn &
     ((unfold_fix mfix1 idx = Some (narg, fn)) *
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                    dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *

      (is_constructor narg args1 = true) *
      (All2 (pred1 Σ Γ Δ) args0 args1) *
      (c = mkApps fn args1)) } } } })%type.

  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - right. exists mfix1, args1, narg, fn. intuition eauto.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [[? [? ?]]|[? [? [? [? ?]]]]].
      -- left. eexists _. eexists (_ ++ [N1])%list. rewrite <- mkApps_nested.
         intuition eauto. simpl. subst M1. reflexivity.
         eapply All2_app; eauto.
      -- right. eexists x, (x0 ++ [N1])%list, x1, x2. intuition auto.
         clear -b1.
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

  Lemma pred1_mkApps_tFix_refl_inv (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx0 idx1 (args0 args1 : list term) :
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx0) args0) (mkApps (tFix mfix1 idx1) args1) ->
    (All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                   dtype dbody
                   (fun x => (dname x, rarg x))
                   (pred1 Σ) mfix0 mfix1 *
     (All2 (pred1 Σ Γ Δ) ) args0 args1).
  Proof with solve_discr.
    remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    intros pred. revert mfix0 mfix1 idx0 idx1 args0 args1 Heqfixt Heqfixt'.
    induction pred; intros; solve_discr.
    - (* body not a lambda *)
      move: e. rewrite /unfold_fix.
      destruct nth_error eqn:Hnth => //.
      case isl: isLambda => // [=] => ? ?; subst.
      destruct (dbody d); try discriminate.
      simpl in Heqfixt'.
      eapply mkApps_eq_inj in Heqfixt' => //.
      intuition discriminate.

    - destruct args0 using rev_ind; noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      destruct args1 using rev_ind; noconf Heqfixt'. clear IHargs1.
      rewrite <- mkApps_nested in Heqfixt'. noconf Heqfixt'.
      clear IHpred2. specialize (IHpred1 _ _ _ _ _ _ eq_refl eq_refl).
      destruct IHpred1 as [? ?]. red in a.
      unfold All2_prop2_eq. split. apply a. apply All2_app; auto.
    - constructor; auto.
    - subst. solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv (Σ : global_env) (Γ Δ : context)
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
    unfold on_Trel in *. destruct r as [[pr Hr] Heq].
    destruct p as [pr0 eq0]. !intros.
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
    unfold on_Trel in *.
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
    induction 1; constructor; intuition auto.
  Qed.
  Hint Resolve All2_on_Trel_eq_impl : pcuic.

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

  Equations isConstruct (t : term) : bool :=
    isConstruct (tConstruct _ _ _) => true;
    isConstruct _ => false.
  Transparent isConstruct.

  Inductive construct_view : term -> Set :=
  | construct_construct c u i : construct_view (tConstruct c u i)
  | construct_other t : ~~ isConstruct t -> construct_view t.

  Equations view_construct (t : term) : construct_view t :=
    { | tConstruct ind u i => construct_construct ind u i;
      | t => construct_other t eq_refl }.

  Fixpoint isFix_app (t : term) : bool :=
    match t with
    | tApp (tFix _ _) _ => true
    | tApp f _ => isFix_app f
    | _ => false
    end.

  Inductive fix_app_view : term -> Set :=
  | fix_app_fix mfix i l : l <> [] -> fix_app_view (mkApps (tFix mfix i) l)
  | fix_app_other t : ~~ isFix_app t -> fix_app_view t.

  Lemma view_fix_app (t : term) : fix_app_view t.
  Proof.
    induction t; try solve [apply fix_app_other; simpl; auto].
    destruct IHt1. pose proof (fix_app_fix mfix i (l ++ [t2])).
    forward H. intros eq. destruct l; discriminate.
    now rewrite -mkApps_nested in H.
    destruct t; try solve [apply fix_app_other; simpl; auto].
    apply (fix_app_fix mfix idx [t2]). congruence.
  Qed.

  Definition isFixLambda (t : term) : bool :=
    match t with
    | tFix _ _ => true
    | tLambda _ _ _ => true
    | _ => false
    end.

  Inductive fix_lambda_view : term -> Set :=
  | fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
  | fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
  | fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

  Lemma view_fix_lambda (t : term) : fix_lambda_view t.
  Proof.
    destruct t; repeat constructor.
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

  Lemma lookup_env_cst_inv {Σ c k cst} :
    lookup_env Σ c = Some (ConstantDecl k cst) -> c = k.
  Proof.
    induction Σ. simpl. discriminate.
    simpl. destruct AstUtils.ident_eq eqn:Heq. intros [= ->]. simpl in Heq.
    now destruct (AstUtils.ident_eq_spec c k). auto.
  Qed.

  Definition isLambda_or_Fix_app t :=
    match fst (decompose_app t) with
    | tLambda _ _ _ => true
    | tFix _ _ => true
    | _ => false
    end.

  Lemma decompose_app_rec_head t l f : fst (decompose_app_rec t l) = f ->
                                       ~~ isApp f.
  Proof.
    induction t; simpl; try intros [= <-]; auto.
    intros. apply IHt1. now rewrite !fst_decompose_app_rec.
  Qed.

  Lemma isLambda_or_Fix_app_decompose_app t :
    ~~ isLambda_or_Fix_app t ->
    forall l', ~~ isLambda_or_Fix_app (fst (decompose_app_rec t l')).
  Proof.
    unfold isLambda_or_Fix_app, decompose_app. generalize (@nil term).
    induction t; simpl;
      try intros ? H ? [= <- <-]; simpl; try congruence.
    intros. rewrite !fst_decompose_app_rec. rewrite fst_decompose_app_rec in H.
    apply IHt1. apply H.
  Qed.

  Section TriangleFn.
    Context (Σ : global_env).

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
          if eqb ind ind' then
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
            if eqb i ind' then arg1
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
      | tConst c u =>
        match lookup_env Σ c with
        | Some (ConstantDecl id decl) =>
          match decl.(cst_body) with
          | Some body => subst_instance_constr u body
          | None => tConst c u
          end
        | _ => tConst c u
        end
      | tApp t u =>
        let t' := rho Γ t in
        let u' := rho Γ u in
        match decompose_app (tApp t u), decompose_app (tApp t' u') with
        | (tFix mfix0 idx0, args0), (tFix mfix1 idx1, args1)  =>
          match unfold_fix mfix1 idx1 with
          | Some (rarg, fn) =>
            if is_constructor rarg args1 then
              mkApps fn args1
            else tApp t' u'
          | None => tApp t' u'
          end
        | _, _ => tApp t' u'
        end
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

    Lemma fold_fix_context_length f Γ l m : #|fold_fix_context f Γ l m| = #|m| + #|l|.
    Proof.
      induction m in l |- *; simpl; auto. rewrite IHm. simpl. auto with arith.
    Qed.

    Lemma All_local_env_Alli P ctx :
      All_local_env (on_local_decl P) ctx ->
      Alli (fun n decl =>
          P (skipn (S n) ctx) (decl_type decl)) 0 ctx.
    Proof.
      (* rewrite -{1}(List.rev_length m). *)
      intros.
      eapply forall_nth_error_Alli. intros.
      eapply All_local_env_lookup in H; eauto.  red in H.
      destruct x as [? [?|] ?]. simpl in *. intuition.
      now simpl in H.
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

    Context `{cf : checker_flags} (wfΣ : wf Σ).

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

    (* Definition ctxmap (Γ Δ : context) (s : nat -> term) := *)
    (*   forall x d, nth_error Γ x = Some d -> *)
    (*               match decl_body d return Type with *)
    (*               | Some b => s x = b.[↑^(S x) ∘ s] *)
    (*               | None => Σ ;;; Δ |- s x : d.(decl_type).[↑^(S x) ∘ s] *)
    (*               end. *)

    Definition ctxmap (Γ Δ : context) (s : nat -> term) :=
      forall x d, nth_error Γ x = Some d ->
                  match decl_body d return Type with
                  | Some b =>
                    ∑ i b', s x = tRel i /\
                            option_map decl_body (nth_error Δ i) = Some (Some b') /\
                            b'.[↑^(S i)] = b.[↑^(S x) ∘ s]
                  | None => True
                  end.

    Lemma simpl_pred Γ Γ' t t' u u' : t = t' -> u = u' -> pred1 Σ Γ Γ' t' u' -> pred1 Σ Γ Γ' t u.
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

    Inductive assumption_context : context -> Prop :=
    | assumption_context_nil : assumption_context []
    | assumption_context_vass na t Γ : assumption_context Γ -> assumption_context (vass na t :: Γ).

    Lemma fix_context_assumption_context m : assumption_context (fix_context m).
    Proof.
      unfold fix_context. unfold mapi. generalize 0 at 2.
      induction m using rev_ind.
      constructor. intros.
      rewrite mapi_rec_app /= List.rev_app_distr /=. constructor.
      apply IHm.
    Qed.

    Lemma nth_error_assumption_context Γ n d :
      assumption_context Γ -> nth_error Γ n = Some d ->
      decl_body d = None.
    Proof.
      intros H; induction H in n, d |- * ; destruct n; simpl; try congruence; eauto.
      now move=> [<-] //.
    Qed.

    Hint Rewrite subst10_inst : sigma.

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

    Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
      All2i_nil : All2i R [] []
    | All2i_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
        R (List.length l) x y -> All2i R l l' -> All2i R (x :: l) (y :: l').
    Hint Constructors All2i : core pcuic.

    Definition pres_bodies Γ Δ σ :=
      All2i (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[⇑^n σ]) (decl_body decl)))
            Γ Δ.

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

    Definition pred1_subst Γ Δ Δ' σ τ :=
      forall x, pred1 Σ Δ Δ' (σ x) (τ x) *
                match option_map decl_body (nth_error Γ x) return Type with
                | Some (Some b) => σ x = τ x
                | _ => True
                end.

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

    Lemma inst_mkApps f l σ : (mkApps f l).[σ] = mkApps f.[σ] (map (inst σ) l).
    Proof.
      induction l in f |- *; simpl; auto. rewrite IHl.
      now autorewrite with sigma.
    Qed.
    Hint Rewrite inst_mkApps : sigma.

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
    Hint Resolve inst_is_constructor.

    Lemma map_fix_subst f g mfix :
      (forall n, tFix (map (map_def f g) mfix) n = f (tFix mfix n)) ->
      fix_subst (map (map_def f g) mfix) =
      map f (fix_subst mfix).
    Proof.
      unfold fix_subst. intros.
      rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
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

    Lemma subst_consn_compose l σ' σ : l ⋅n σ' ∘ σ =1 (map (inst σ) l ⋅n (σ' ∘ σ)).
    Proof.
      induction l; simpl. now sigma.
      rewrite subst_consn_subst_cons. sigma.
      rewrite IHl. now rewrite subst_consn_subst_cons.
    Qed.
    Lemma map_idsn_spec (f : term -> term) (n : nat) :
      map f (idsn n) = Nat.recursion [] (fun x l => l ++ [f (tRel x)]) n.
    Proof.
      induction n. simpl. reflexivity.
      simpl. rewrite map_app. now rewrite -IHn.
    Qed.


    Lemma nat_recursion_ext {A} (x : A) f g n :
      (forall x l', x < n -> f x l' = g x l') ->
      Nat.recursion x f n = Nat.recursion x g n.
    Proof.
      intros.
      generalize (le_refl n). induction n at 1 3 4.
      simpl; auto. intros. simpl. rewrite IHn0. lia. now rewrite H.
    Qed.

    Lemma id_nth_spec {A} (l : list A) :
      l = Nat.recursion [] (fun x l' =>
                              match nth_error l x with
                              | Some a => l' ++ [a]
                              | None => l'
                              end) #|l|.
    Proof.
      induction l using rev_ind. simpl. reflexivity.
      rewrite app_length. simpl. rewrite Nat.add_1_r. simpl.
      rewrite nth_error_app_ge. lia. rewrite Nat.sub_diag. simpl.
      f_equal. rewrite {1}IHl. eapply nat_recursion_ext. intros.
      now rewrite nth_error_app_lt.
    Qed.

  Lemma Upn_comp n l σ : n = #|l| -> ⇑^n σ ∘ (l ⋅n ids) =1 l ⋅n σ.
  Proof.
    intros ->. rewrite Upn_eq; simpl.
    rewrite !subst_consn_compose. sigma.
    rewrite subst_consn_shiftn ?map_length //. sigma.
    eapply subst_consn_proper; try reflexivity.
    rewrite map_idsn_spec.
    rewrite {3}(id_nth_spec l).
    eapply nat_recursion_ext. intros.
    simpl. destruct (nth_error_spec l x). unfold subst_consn. rewrite e. reflexivity.
    lia.
  Qed.

   Lemma shift_Up_comm σ : ↑ ∘ ⇑ σ =1 σ ∘ ↑.
   Proof. reflexivity. Qed.

  Lemma pres_bodies_inst_context Γ σ : pres_bodies Γ (inst_context σ Γ) σ.
  Proof.
    red; induction Γ. constructor.
    rewrite inst_context_snoc. constructor. simpl. reflexivity.
    apply IHΓ.
  Qed.
  Hint Resolve pres_bodies_inst_context : pcuic.

  Lemma inst_closed0 σ t : closedn 0 t -> t.[σ] = t.
  Proof. intros. rewrite -{2}[t](inst_closed σ 0) //. now sigma. Qed.

  Lemma isLambda_inst t σ : isLambda t -> isLambda t.[σ].
  Proof. destruct t; auto. Qed.

  Lemma isLambda_subst t s : isLambda t -> isLambda (subst0 s t).
  Proof. destruct t; auto. Qed.

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
        eapply (pred_beta _ _ _ _ _ _ _ _ _ _ X2 X0 X4). (* IHredst1 IHredst2 IHredst3).*) }

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
        destruct (isLambda (dbody d)) eqn:isl; noconf H.
        rewrite isLambda_inst //.
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
      toProp; auto.
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

  Definition rho_ctxmap φ (Γ Δ : context) (s : nat -> term) :=
    forall x d, nth_error Γ x = Some d ->
                match decl_body d return Type with
                | Some b => ∑ i, (s x = tRel i) * (* The image is a variable i in Δ *)
                                 (option_map decl_body (nth_error Δ i) = Some (Some b.[↑^(S x) ∘ s]))
                (* whose body is b substituted with the previous variables *)
                | None => (Σ, φ) ;;; Δ |- s x : d.(decl_type).[↑^(S x) ∘ s]
                end.

  Definition renaming Γ Δ r :=
    forall x, match nth_error Γ x with
              | Some d =>
                match decl_body d return Prop with
                | Some b =>
                  exists b', option_map decl_body (nth_error Δ (r x)) = Some (Some b') /\
                             b'.[↑^(S (r x))] = b.[↑^(S x) ∘ ren r]
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
    intros x.
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
    rewrite shiftnS. apply shiftn1_renaming. apply IHAll2i; try lia. auto.
    apply r0.
  Qed.

  Definition isFix (t : term) : bool :=
    match t with
    | tFix _ _ => true
    | _ => false
    end.

  Definition discr_fix (t : term) : Prop :=
    match t with
    | tFix _ _ => False
    | _ => True
    end.

  Inductive fix_view : term -> Set :=
  | fix_fix mfix i : fix_view (tFix mfix i)
  | fix_other t : discr_fix t -> fix_view t.

  Lemma view_fix (t : term) : fix_view t.
  Proof. induction t; constructor; simpl; auto. Qed.

  Lemma fold_mkApps_tApp f l a : mkApps (tApp f a) l = mkApps f (a :: l).
  Proof. reflexivity. Qed.

  Lemma fold_tApp f a : tApp f a = mkApps f [a].
  Proof. reflexivity. Qed.

  Lemma isFix_app_false mfix idx l : l <> [] -> ~~ isFix_app (mkApps (tFix mfix idx) l) -> False.
  Proof.
    induction l using rev_ind; simpl; auto. intros H.
    rewrite -mkApps_nested. destruct l using rev_ind. simpl. auto. clear IHl0.
    intros. forward IHl. move/app_eq_nil=> []. congruence.
    apply IHl. simpl in H0.
    rewrite -{1}mkApps_nested in H0. now simpl in H0.
  Qed.

  Definition lambda_app_discr (t : term) : bool :=
    match t with
    | tApp (tLambda _ _ _) _ => true
    | _ => false
    end.

  Inductive lambda_app_view : term -> Set :=
  | lambda_app_fix na t b a : lambda_app_view (tApp (tLambda na t b) a)
  | lambda_app_other t : ~~ lambda_app_discr t -> lambda_app_view t.

  Lemma view_lambda_app (t : term) : lambda_app_view t.
  Proof.
    destruct t; try solve [apply lambda_app_other; simpl; auto].
    destruct t1; constructor; constructor.
  Qed.

  Lemma isFix_app_tapp f x : ~~ isFix_app (tApp f x) -> ~~ isFix_app f.
  Proof.
    simpl. destruct f; intuition.
  Qed.

  Lemma discr_fix_match (P : Type)
        (p : mfixpoint term -> nat -> P)
        (q : P) :
    forall t l, l <> [] -> ~~ isFix_app (mkApps t l) ->
                (match t with tFix mfix idx => p mfix idx | _ => q end) = q.
  Proof.
    induction t => /=; intros l' Hl' H; try congruence.
    destruct l'. congruence. apply isFix_app_false in H. elim H.
    congruence.
  Qed.

  Definition rho_fix Γ t l :=
    let t' := rho Γ t in
    let u' := map (rho Γ) l in
    match t' with
    | tFix mfix1 idx1  =>
      match unfold_fix mfix1 idx1 with
      | Some (rarg, fn) =>
        if is_constructor rarg u' then
          mkApps fn u'
        else mkApps t' u'
      | None => mkApps t' u'
      end
    | _ => mkApps t' u'
    end.

  Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
  Proof.
    induction l; auto => Hl. simpl.
    rewrite (IHl Hl). destruct l, l'; simpl; congruence.
  Qed.

  Lemma mkApps_tApp_tApp f a l :
    mkApps (tApp f a) l = tApp (mkApps f (removelast (a :: l))) (List.last l a).
  Proof.
    induction l using rev_ind; simpl; auto.
    rewrite -mkApps_nested IHl.
    simpl.
    rewrite last_app. congruence. simpl. f_equal.
    simpl in IHl. rewrite -IHl.
    assert (l ++ [x] <> []).
    { move/app_eq_nil => [<- H].
      apply (f_equal (@List.length _)) in H. simpl in H. lia. }
    destruct (l ++ [x]) eqn:Hlx at 1.
    contradiction. rewrite removelast_app. congruence.
    simpl. now rewrite app_nil_r.
  Qed.

  Lemma decompose_app_rec_non_nil f l :
    l <> [] ->
    forall t' l', decompose_app_rec f l = (t', l') -> l' <> [].
  Proof. induction f in l |- *; simpl; intros; try noconf H0; eauto.
         eapply IHf1. 2:eauto. congruence.
  Qed.

  Lemma isLambda_nisApp t : isLambda t -> ~~ isApp t.
  Proof. case: t => /= //. Qed.

  Lemma rho_fix_unfold Γ mfix idx l :
    rho Γ (mkApps (tFix mfix idx) l) = rho_fix Γ (tFix mfix idx) l.
  Proof.
    induction l using rev_ind; simpl; try reflexivity.
    - rewrite /rho_fix /= /unfold_fix nth_error_map_fix.
      case nth: (nth_error mfix idx) => [d|] /= //.
      case isl: isLambda => //.
      case isc: is_constructor => //.
      move: isc. rewrite /is_constructor nth_error_nil //.
    - rewrite -mkApps_nested.
      destruct l.
      + simpl.
        simpl in IHl.
        now move: IHl; rewrite /rho_fix /=.
      + simpl in *. move eq_mkApps: (mkApps _ l) IHl => a.
        rewrite mkApps_tApp_tApp in eq_mkApps.
        subst a. move=> IHl.
        rewrite -mkApps_tApp_tApp.
        replace (tApp (mkApps (tApp (tFix mfix idx) t) l) x) with
            (mkApps (tFix mfix idx) (t :: l ++ [x])); first last.
        simpl. now rewrite -mkApps_nested.
        rewrite decompose_app_mkApps //.
        rewrite -mkApps_tApp_tApp in IHl.
        rewrite IHl. destruct decompose_app eqn:rhofix.
        pose proof (decompose_app_inv rhofix).
        remember (mkApps t0 l0) as app0.
        destruct (view_fix_app app0).
        * eapply mkApps_eq_decompose_app in Heqapp0.
          simpl in Heqapp0. rewrite atom_decompose_app in Heqapp0.
          eapply decompose_app_rec_head. unfold decompose_app in rhofix. erewrite rhofix. reflexivity.
          noconf Heqapp0. simpl. clear H.
          move: rhofix.
          rewrite /rho_fix /= /unfold_fix nth_error_map.
          destruct nth_error as [[arg fn]|] eqn:Hunf; simpl.
          case islam: (isLambda _) => //.
          case isc: (is_constructor _ _).
          ** move=> H. elimtype False. simpl in H.
             (* Impossible: the body of a fix cannot be directly a fix! *)
             rewrite [tApp _ _](mkApps_nested _ _ [rho Γ x]) in H.
             rewrite [mkApps _ _](mkApps_nested _ [rho Γ t] _) in H.
             rewrite decompose_app_mkApps in H.
             apply isLambda_nisApp.
             rewrite isLambda_subst //.
             noconf H. hnf in H. noconf H.
             apply (f_equal isLambda) in H. simpl in H.
             rewrite subst_inst isLambda_inst in H => //.
          ** simpl. rewrite fold_mkApps_tApp fold_tApp mkApps_nested.
             rewrite decompose_app_mkApps // => [= <- <- <-].
             rewrite nth_error_map_fix Hunf /= islam.
             rewrite map_app /=.
             destruct (is_constructor _ (_ :: _ ++ _)) eqn:isc'.
             reflexivity. reflexivity.
          ** rewrite fold_mkApps_tApp fold_tApp mkApps_nested.
             rewrite decompose_app_mkApps // => [= <- <- <-].
             rewrite nth_error_map_fix Hunf /= islam.
             rewrite map_app /= //.
          ** rewrite fold_mkApps_tApp fold_tApp mkApps_nested.
             rewrite decompose_app_mkApps // => [= <- <- <-].
             rewrite nth_error_map_fix Hunf /=.
             rewrite map_app /= //.

        * subst t1.
          assert (~~ isApp t0).
          eapply decompose_app_rec_head.
          unfold decompose_app in rhofix; now erewrite -> rhofix.
          assert (l0 <> []).
          { revert H. rewrite fold_tApp.
            move=> H. apply eq_sym in H.
            apply mkApps_eq_decompose_app in H; auto.
            simpl in H.
            rewrite atom_decompose_app in H; auto. symmetry in H.
            eapply decompose_app_rec_non_nil in H; auto. congruence. }
          rewrite (discr_fix_match _ _ _ t0 l0) //.
          apply decompose_app_inv in rhofix.
          rewrite rhofix. move: rhofix.
          rewrite /rho_fix /= /unfold_fix nth_error_map_fix.
          destruct nth_error eqn:Hnth. simpl.
          destruct isLambda eqn:isl.
          destruct is_constructor eqn:isc.
          unfold is_constructor in *. simpl. destruct (nth_error _ (rarg d)) eqn:Harg; try discriminate.
          move: (nth_error_Some_length Harg) => /=.
          rewrite map_length => Hargl.
          rewrite map_app app_comm_cons nth_error_app_lt /= ?map_length // Harg isc.
          now rewrite -mkApps_nested. simpl.

          rewrite map_app app_comm_cons.
          move=> H'. elimtype False. rewrite -H' in i.
          rewrite fold_mkApps_tApp fold_tApp mkApps_nested in i.
          now eapply isFix_app_false in i.

          simpl. now rewrite fold_mkApps_tApp !fold_tApp !mkApps_nested map_app /=.
          simpl. now rewrite fold_mkApps_tApp !fold_tApp !mkApps_nested map_app /=.
  Qed.

  Definition rho_fix_context Γ mfix :=
    fold_fix_context rho Γ [] mfix.

  Lemma rho_fix_context_length Γ mfix : #|rho_fix_context Γ mfix| = #|mfix|.
  Proof. now rewrite fold_fix_context_length Nat.add_0_r. Qed.

  Lemma isLambda_rho Γ t : isLambda t -> isLambda (rho Γ t).
  Proof. destruct t; auto. Qed.

  Lemma nisLambda_rho Γ t : ~~ isLambda (rho Γ t) -> ~~ isLambda t.
  Proof. destruct t; auto. Qed.

  Lemma rho_fix_unfold_inv Γ mfix i l :
    match nth_error mfix i with
    | Some d =>
      let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
      if isLambda (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) && is_constructor (rarg d) (map (rho Γ) l) then
         (rho Γ (mkApps (tFix mfix i) l) = mkApps fn (map (rho Γ) l))
      else
        rho Γ (mkApps (tFix mfix i) l) = mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)
    | None => rho Γ (mkApps (tFix mfix i) l) = mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)
    end.
  Proof.
    destruct nth_error eqn:Hnth.
    intros fn.
    destruct isLambda eqn:Hlam.
    destruct is_constructor eqn:Hisc.
    - simpl.
      rewrite rho_fix_unfold.
      rewrite /rho_fix. simpl.
      rewrite /unfold_fix /map_fix.
      rewrite ?nth_error_map ?Hnth /= Hlam.
      unfold is_constructor in *. simpl in Hisc.
      rewrite nth_error_map in Hisc |- *.
      case Hnth' : nth_error Hisc => [arg|] /=.
      + move => ->.
        rewrite map_fix_subst //.
      + discriminate.
    - simpl. move: Hlam. rewrite rho_fix_unfold /rho_fix.
      simpl. rewrite /unfold_fix nth_error_map Hnth => /= ->.
      move: Hisc.
      rewrite /is_constructor nth_error_map //.
      case Hnth' : nth_error => [arg|] /= //.
      + now move => ->.
    - simpl. move: Hlam. rewrite rho_fix_unfold /rho_fix.
      simpl. now rewrite /unfold_fix nth_error_map Hnth => /= ->.
    - simpl. rewrite rho_fix_unfold /rho_fix.
      simpl. now rewrite /unfold_fix nth_error_map Hnth => /=.
  Qed.

  Inductive rho_fix_spec Γ mfix i l : term -> Type :=
  | rho_fix_red d :
      let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
      nth_error mfix i = Some d ->
      isLambda (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) && is_constructor (rarg d) (map (rho Γ) l) ->
      rho_fix_spec Γ mfix i l (mkApps fn (map (rho Γ) l))
  | rho_fix_stuck :
      (match nth_error mfix i with
       | None => True
       | Some d =>
         let fn := (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
         ~~ isLambda fn \/ ~~ is_constructor (rarg d) (map (rho Γ) l)
       end) ->
      rho_fix_spec Γ mfix i l (mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)).

  Lemma rho_fix_elim Γ mfix i l :
    rho_fix_spec Γ mfix i l (rho Γ (mkApps (tFix mfix i) l)).
  Proof.
    rewrite rho_fix_unfold /rho_fix /= /unfold_fix.
    rewrite nth_error_map.
    case e: nth_error => [d|] /=.
    rewrite map_fix_subst //.
    case isl: isLambda.
    case isc: is_constructor => /=.
    - eapply (rho_fix_red Γ mfix i l d) => //.
      now rewrite isl isc.
    - apply rho_fix_stuck.
      rewrite e. right. now rewrite isc.
    - simpl.
      apply rho_fix_stuck. rewrite e /= isl. now left.
    - apply rho_fix_stuck. now rewrite e /=.
  Qed.

  Definition rho_app Γ t :=
    let '(hd, args) := decompose_app t in
    match hd with
    | tLambda na dom b =>
      match args with
      | a :: args => mkApps (rho Γ (tApp hd a)) (map (rho Γ) args)
      | [] => rho Γ t
      end
    | tFix _ _ => rho_fix Γ hd args
    | _ => mkApps (rho Γ hd) (map (rho Γ) args)
    end.

  Lemma discr_fix_eq (A : Type) (a : mfixpoint term -> nat -> A) (b c : A) t :
    ~~ isFix t ->
    b = c ->
    match t with
    | tFix mfix idx => a mfix idx
    | _ => b
    end = c.
  Proof. destruct t; simpl; try congruence. Qed.

  Lemma is_constructor_app_ge n l l' : is_constructor n l -> is_constructor n (l ++ l').
  Proof.
    unfold is_constructor. destruct nth_error eqn:Heq.
    rewrite nth_error_app_lt ?Heq //; eauto using nth_error_Some_length.
    discriminate.
  Qed.

  Lemma isLambda_nisFix t : isLambda t -> ~~ isFix t.
  Proof. destruct t; auto. Qed.

  Lemma rho_app_unfold Γ t : rho Γ t = rho_app Γ t.
  Proof.
    unfold rho_app. destruct decompose_app eqn:Heq.
    assert (~~ isApp t0). eapply decompose_app_rec_head. unfold decompose_app in Heq; now erewrite Heq.
    apply decompose_app_inv in Heq. subst.
    revert t0 H. induction l using rev_ind; intros.
    - simpl. intros.
      destruct t0; auto. now rewrite -rho_fix_unfold.
    - rewrite -mkApps_nested. simpl mkApps at 1.
      destruct l. destruct t0; try solve [reflexivity].
      depelim H.

      specialize (IHl t0 H). simpl mkApps in IHl at 1.
      simpl app. cbv beta iota.
      simpl map. rewrite map_app. rewrite - !mkApps_nested. simpl map.
      assert (exists f r', mkApps t0 (t :: l) = tApp f r') as [f [r' Heq]].
      { induction l using rev_ind; simpl; eexists _, _; try reflexivity.
        rewrite -mkApps_nested. reflexivity. }
      simpl rho at 1. simpl in Heq. rewrite Heq.
      destruct (decompose_app (tApp (tApp f r') x)) as [head r] eqn:Heq'.
      apply (f_equal fst) in Heq'. simpl in Heq'. subst head. rewrite -Heq. clear Heq f r'.
      unfold decompose_app at 1. simpl decompose_app_rec. rewrite decompose_app_rec_mkApps.
      simpl decompose_app_rec.
      rewrite atom_decompose_app //. simpl fst.
      destruct (view_fix_lambda t0).
      + now rewrite IHl.
      + rewrite IHl.
        case e: decompose_app => [head args].
        unfold decompose_app in e. simpl in e.
        generalize (rho_fix_unfold_inv Γ mfix i (t :: l)).
        rewrite IHl.
        unfold unfold_fix.
        destruct nth_error eqn:Heq; simpl; try destruct (isLambda _ && _) eqn:isc.
        * intros Hrho. rewrite Hrho in e.
          rewrite decompose_app_rec_mkApps in e.
          simpl in e.
          move/andP: isc => [islam isc].
          rewrite atom_decompose_app in e.
          now apply isLambda_nisApp, isLambda_subst.
          noconf e. apply discr_fix_eq.
          now apply isLambda_nisFix, isLambda_subst.
          generalize (rho_fix_unfold_inv Γ mfix i (t :: l ++ [x])).
          now rewrite Heq /= islam /= map_app app_comm_cons is_constructor_app_ge //
              (rho_fix_unfold _ _ _ (t :: l ++ [x])) Hrho -mkApps_nested => ->.
        * intros Hrho. rewrite Hrho in e.
          rewrite decompose_app_rec_mkApps in e.
          simpl in e. noconf e => /=.
          rewrite nth_error_map_fix Heq /= app_comm_cons.
          generalize (rho_fix_unfold_inv Γ mfix i (t :: l ++ [x])).
          rewrite Heq. cbv zeta.
          rewrite /map_fix map_fix_subst //.
          move/andb_false_iff: isc => [islam|isc].
          rewrite islam /= map_app app_comm_cons
              (rho_fix_unfold _ _ _ (t :: l ++ [x])) => ->.
          rewrite Hrho. simpl. now rewrite -mkApps_nested.
          rewrite /= map_app.
          destruct isLambda eqn:isl => /=.
          destruct (is_constructor _ (_ :: _ ++ _)) eqn:isc'.
          now rewrite -rho_fix_unfold => <-.
          rewrite - !mkApps_nested.
          rewrite Hrho. simpl mkApps. rewrite -rho_fix_unfold => <-.
          simpl mkApps. now rewrite -mkApps_nested.
          rewrite - !mkApps_nested.
          rewrite Hrho. simpl mkApps. rewrite -rho_fix_unfold => <-.
          simpl mkApps. now rewrite -mkApps_nested.

        * intros Hrho. rewrite Hrho in e.
          rewrite decompose_app_rec_mkApps in e.
          simpl in e. noconf e.
          simpl. rewrite nth_error_map_fix Heq /=.
          generalize (rho_fix_unfold_inv Γ mfix i (t :: l ++ [x])).
          now rewrite Heq /= map_app app_comm_cons
              (rho_fix_unfold _ _ _ (t :: l ++ [x])) Hrho -mkApps_nested => ->.
      + assert (tApp (rho Γ (mkApps (tApp t0 t) l)) (rho Γ x) =
                mkApps (rho Γ t0) (rho Γ t :: map (rho Γ) l ++ [rho Γ x])).
        { rewrite IHl app_comm_cons -mkApps_nested. simpl.
          destruct t0; simpl in i; congruence. }
        destruct t0; simpl in i; congruence.
  Qed.

  Definition lambda_discr (t : term) : bool :=
    match t with
    | tLambda _ _ _ => true
    | _ => false
    end.

  Lemma discr_lambda_fix_eq (A : Type) (a b c d : A) t :
    ~ isFix t -> ~ lambda_discr t ->
    c = d ->
    match t with
    | tFix _ _ => a
    | tLambda _ _ _ => b
    | _ => c
    end = d.
  Proof. destruct t; simpl; try congruence. Qed.

  Lemma rho_app_discr_aux Γ f a :
    ~ isLambda f ->
    ~~ isFix_app (tApp f a) ->
    rho_app Γ (tApp f a) = tApp (rho Γ f) (rho Γ a).
  Proof.
    intros Hlam.
    rewrite rho_app_unfold.
    intros Hdisc'.
    rewrite /rho_app.
    move e : (tApp f a) => app.
    case eapp: (decompose_app app) => [hd args].
    subst app. rewrite /decompose_app /= in eapp.
    destruct args using rev_ind; auto.
    apply decompose_app_rec_non_nil in eapp; try congruence.
    clear IHargs.
    assert(exists a' args', (args ++ [x]) = a' :: args') as [a' [args' Heq']].
    { clear. induction args. now exists x, [].
      exists a, (args ++ [x]). now rewrite app_comm_cons. }
    rewrite Heq'.
    assert (~~ isApp hd).
    { eapply decompose_app_rec_head; eauto. now erewrite eapp. }
    apply decompose_app_rec_inv in eapp. simpl in eapp. rewrite -mkApps_nested in eapp.
    simpl in eapp. noconf eapp.
    rewrite decompose_app_mkApps //.
    rewrite -Heq'. rewrite map_app -mkApps_nested.
    destruct hd; auto.
    - destruct args. noconf Heq'. simpl in Hlam. red in Hlam. destruct (Hlam eq_refl).
      simpl in Heq'. noconf Heq'. now rewrite map_app -mkApps_nested.
    - rewrite [tApp _ _](mkApps_nested (tFix mfix idx) args [a]) in Hdisc'.
      eapply isFix_app_false in Hdisc'. destruct Hdisc'. congruence.
  Qed.

  Lemma rho_mkApps_non_nil Γ f l :
    ~~ isLambda f -> l <> nil -> ~~ isApp f -> ~~ isFix f ->
    rho Γ (mkApps f l) = mkApps (rho Γ f) (map (rho Γ) l).
  Proof.
    intros Hlam Hl Happ.
    rewrite !rho_app_unfold.
    intros Hdisc'.
    rewrite /rho_app.
    move e : (mkApps f l) => app.
    case eapp: (decompose_app app) => [hd args].
    subst app.
    rewrite /decompose_app decompose_app_rec_mkApps app_nil_r /= in eapp.
    destruct args using rev_ind; auto.
    apply decompose_app_rec_non_nil in eapp; try congruence.
    clear IHargs.
    assert(exists a' args', (args ++ [x]) = a' :: args') as [a' [args' Heq']].
    { clear. induction args. now exists x, [].
      exists a, (args ++ [x]). now rewrite app_comm_cons. }
    rewrite Heq'.
    assert (~~ isApp hd).
    { eapply decompose_app_rec_head; eauto. now erewrite eapp. }
    destruct l using rev_ind; try congruence. clear IHl.
    apply decompose_app_rec_inv in eapp. rewrite - !mkApps_nested in eapp.
    simpl in eapp. noconf eapp. simpl in H0. noconf H0.
    apply mkApps_eq_inj in H0 => //. destruct H0; subst.
    replace (decompose_app hd) with (hd, @nil term).
    rewrite -Heq'. rewrite !map_app - !mkApps_nested. simpl map.
    destruct hd; auto.
    - simpl in Hlam. discriminate.
    - simpl in Hdisc'. congruence.
    - change hd with (mkApps hd []) at 2.
      now rewrite decompose_app_mkApps.
  Qed.

  Lemma rho_mkApps Γ f l :
    ~~ isApp f -> ~~ isLambda f -> ~~ isFix f ->
    rho Γ (mkApps f l) = mkApps (rho Γ f) (map (rho Γ) l).
  Proof.
    intros Happ.
    destruct l using rev_ind. simpl; auto.
    move => Hl Hfix.
    rewrite rho_mkApps_non_nil //.
    move/app_eq_nil => [_ H]; discriminate.
  Qed.

  Lemma decompose_app_rec_inv' f l hd args : decompose_app_rec f l = (hd, args) ->
                                       ~~ isApp hd /\ mkApps f l = mkApps hd args.
  Proof.
    intros. pose proof (decompose_app_rec_inv H).
    split; auto.
    eapply decompose_app_rec_head. now erewrite H.
  Qed.

  Lemma decompose_app_inv' f hd args : decompose_app f = (hd, args) ->
                                       ~~ isApp hd /\ f = mkApps hd args.
  Proof.
    rewrite /decompose_app. apply/decompose_app_rec_inv'.
  Qed.

  Lemma mkApps_eq_app f l f' a :
    ~~ isApp f ->
    mkApps f l = tApp f' a ->
    l <> nil /\ a = last l a /\ f' = mkApps f (removelast l).
  Proof.
    intros.
    apply (f_equal decompose_app) in H0.
    rewrite decompose_app_mkApps in H0 => //.
    rewrite /decompose_app in H0.
    symmetry in H0. apply decompose_app_rec_inv' in H0.
    destruct H0.
    simpl in H1.
    clear H0. revert f f' a H H1.
    induction l using rev_ind.
    - simpl in *; intuition auto; subst f; discriminate.
    - intros.
      rewrite -mkApps_nested in H1. noconf H1.
      rewrite last_app // removelast_app ?app_nil_r; try congruence.
      intuition auto. apply app_eq_nil in H0. intuition congruence.
  Qed.

  Lemma discr_lambda_app_isLambda f a : ~~ lambda_app_discr (tApp f a) <-> ~ isLambda f.
  Proof.
    simpl. split. intros Hf Hf'; red in Hf'.
    destruct f; simpl in Hf'; try congruence.
    red in Hf; auto. intros Hf. destruct f; simpl in Hf; try auto.
  Qed.

  Lemma rho_tApp_discr Γ f a :
    ~~ lambda_app_discr (tApp f a) ->
    ~~ isFix_app (tApp f a) ->
    rho Γ (tApp f a) = tApp (rho Γ f) (rho Γ a).
  Proof.
    move=> Hdiscr Hdisc'.
    rewrite rho_app_unfold.
    rewrite rho_app_discr_aux; auto.
    destruct f; auto.
  Qed.

  Lemma discr_fix_app_mkApps f args : ~~ isApp f -> ~~ isFix f -> ~~ isFix_app (mkApps f args).
  Proof.
    revert f.
    induction args using rev_ind. simpl; auto. intros. clear H0.
    destruct f; simpl in *; auto.
    intros f Ha H. rewrite -mkApps_nested. simpl mkApps.
    specialize (IHargs _ Ha H). simpl.
    destruct args using rev_ind. simpl in *. destruct f; auto.
    rewrite -{1}mkApps_nested. now simpl.
  Qed.

  Lemma discr_lambda_app_rename r f :
    lambda_app_discr f = lambda_app_discr (rename r f).
  Proof.
    destruct f; auto.
    destruct f1; auto.
  Qed.

  Lemma isFix_app_rename r f :
    isFix_app f = isFix_app (rename r f).
  Proof.
    induction f; auto.
    destruct f1; auto.
  Qed.

  Lemma isConstruct_app_rho Γ t : isConstruct_app t -> isConstruct_app (rho Γ t).
  Proof.
    move/isConstruct_app_inv => [ind [k [u [args ->]]]] //.
    rewrite rho_mkApps //.
    unfold isConstruct_app. rewrite decompose_app_mkApps //.
  Qed.

  Lemma rename_mkApps r f l: rename r (mkApps f l) = mkApps (rename r f) (map (rename r) l).
  Proof.
    induction l in f |- *; simpl; auto.
    now rewrite IHl.
  Qed.

  Lemma isConstruct_app_rename r t :
    isConstruct_app t = isConstruct_app (rename r t).
  Proof.
    unfold isConstruct_app. unfold decompose_app. generalize (@nil term) at 1.
    change (@nil term) with (map (rename r) []). generalize (@nil term).
    induction t; simpl; auto.
    intros l l0. specialize (IHt1 (t2 :: l) (t2 :: l0)).
    now rewrite IHt1.
  Qed.

  Lemma mfixpoint_size_nth_error {mfix i d} :
    nth_error mfix i = Some d ->
    size (dbody d) < mfixpoint_size size mfix.
  Proof.
    induction mfix in i, d |- *; destruct i; simpl; try congruence.
    move=> [] ->. unfold def_size. lia.
    move/IHmfix. lia.
  Qed.

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

  Lemma mfixpoint_size_In {mfix d} :
    In d mfix ->
    size (dbody d) < mfixpoint_size size mfix /\
    size (dtype d) < mfixpoint_size size mfix.
  Proof.
    induction mfix in d |- *; simpl; auto. intros [].
    move=> [->|H]. unfold def_size. split; lia.
    destruct (IHmfix d H). split; lia.
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
      sigma.
      unfold Basics.compose.
      rewrite -(H (Γ ,,, rho_fix_context Γ mfix)).
      now apply renaming_shift_rho_fix_context.
      reflexivity.
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

  (* TODO rename isConstruct to isConstruct *)
  Lemma nisConstruct_elim {A} {t} {a : inductive -> nat -> universe_instance -> A} {b : A} :
    ~~ isConstruct t ->
    match t with
    | tConstruct ind n u => a ind n u
    | _ => b
    end = b.
  Proof.
    destruct t => /= //.
  Qed.

  Lemma isConstruct_rename {r t} : ~~ isConstruct t -> ~~ isConstruct (rename r t).
  Proof.
    move: t. case; auto.
  Qed.

  Lemma isLambda_rename r t : isLambda (rename r t) = isLambda t.
  Proof. destruct t; auto. Qed.

  Lemma nth_nth_error {A} {i} {l : list A} {d v} :
    nth i l d = v ->
    (nth_error l i = Some v) +
    (nth_error l i = None /\ v = d).
  Proof.
    move: i v. elim: l => [|hd tl IH] //.
    - case => /= //; now right.
    - case => /= // _ <-. now left.
  Qed.

  Lemma rho_rename Γ Δ r t :
    renaming Γ Δ r ->
    rename r (rho Γ t) = rho Δ (rename r t).
  Proof.
    revert t Γ Δ r.
    refine (term_forall_ctx_list_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      intros; try subst Γ; try rename Γ0 into Γ(* ; rename_all_hyps *).
    all:auto 2.

    - red in H. simpl.
      specialize (H n).
      destruct (nth_error Γ n) as [c|] eqn:Heq.
      -- pose proof Heq as Heq'.
         eapply nth_error_Some_length in Heq'.
         simpl. destruct decl_body eqn:Heq''.
         simpl. rewrite lift0_inst.
         destruct H as [b' [-> Hb']].
         rewrite lift0_inst.
         sigma. autorewrite with sigma in *. now rewrite <- Hb'.
         simpl.
         rewrite H. simpl. reflexivity.

      -- simpl. now rewrite H.

    - simpl. f_equal. rewrite !map_map_compose. solve_all.

    - simpl. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl. rewrite /subst1 subst_inst.
      specialize (H _ _ _ H2). specialize (H0 _ _ _ H2).
      autorewrite with sigma in H, H0, H1. erewrite <- (H1 ((vdef n (rho Γ t) (rho Γ t0) :: Γ))).
      2:{ eapply (shift_renaming _ _ [_] [_]). repeat constructor. simpl.
          sigma. now rewrite -H shiftn0. auto. }
      sigma. apply inst_ext. rewrite H.
      rewrite -ren_shiftn. sigma. unfold Up. now sigma.

    - (* Need a fix+lambda view here to factor cases *)
      remember (tApp t u) as tapp.
      destruct (view_fix_app tapp) as [mfix i l n|tapp d].
      + (* Fixpoint application *)
        rewrite rename_mkApps /=.
        assert (All (fun x => rename r (rho Γ x) = rho Δ (rename r x)) l).
        { destruct l using rev_ind; try discriminate. clear IHl.
          rewrite -mkApps_nested in Heqtapp; noconf Heqtapp.
          eapply All_app_inv.
          2:{ constructor. auto. constructor. }
          clear -wfΣ H2 H.
          induction l; constructor; eauto.
          apply H; auto. rewrite mkApps_size. simpl. lia.
          apply IHl. intros t'. rewrite mkApps_size. intros.
          apply H; auto. rewrite mkApps_size. simpl in H0 |- *. lia. }

        specialize (rho_fix_unfold_inv Γ mfix i l).
        specialize (rho_fix_unfold_inv Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix) i
                                               (map (rename r) l)).
        rewrite nth_error_map. destruct nth_error eqn:Hnth.
        simpl option_map. cbv beta iota.
        unfold is_constructor. rewrite !nth_error_map.
        simpl rarg.
        destruct (nth_error _ (rarg d)) eqn:Hisc.
        simpl option_map. cbv beta iota.
        assert (rho Δ (rename r t0) = rename r (rho Γ t0)) as ->.
        eapply nth_error_all in H3; eauto. now simpl in H3.
        simpl.
        assert (Hbod: ∀ (Γ Δ : list context_decl) (r : nat → nat),
                   renaming Γ Δ r → rename r (rho Γ (dbody d)) = rho Δ (rename r (dbody d))).
        { pose proof (H (dbody d)) as Hbod.
          forward Hbod.
          { rewrite mkApps_size. simpl.
            eapply mfixpoint_size_nth_error in Hnth. lia. }
          auto. }
        assert (Hren : renaming (Γ ,,, rho_fix_context Γ mfix)
                           (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                           (shiftn #|mfix| r)).
        now apply renaming_shift_rho_fix_context.
        specialize (Hbod _ _ _ Hren).
        rewrite -Hbod. rewrite isLambda_rename.
        destruct isLambda eqn:isl => /=.
        rewrite -isConstruct_app_rename.
        destruct isConstruct_app eqn:iscon => /= //.
        move => -> ->. rewrite rename_mkApps /=.
        f_equal.

        2:{ rewrite !map_map_compose. solve_all. }
        rewrite !subst_inst.
        { sigma. eapply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          rewrite map_fix_subst // !map_map_compose.
          assert (0 < list_size size l).
          { destruct l; simpl; auto. congruence. lia. }
          clear -H H2 H4.
          unfold fix_subst. generalize #|mfix|.
          induction n; simpl; auto.
          rewrite IHn. f_equal.
          specialize (H (tFix mfix n)) as Hbod.
          forward Hbod.
          { simpl; rewrite mkApps_size. simpl. lia. }
          unfold Basics.compose. rewrite -(Hbod _ _ _ H2).
          now rewrite -rename_inst. }

        move => -> ->.
        rewrite rename_mkApps /= map_length. f_equal.
        2:{ rewrite !map_map_compose. solve_all. }
        f_equal. eapply map_fix_rho_rename; eauto.

        simpl. move=> -> ->.
        rewrite rename_mkApps /= map_length. f_equal.
        2:{ rewrite !map_map_compose. solve_all. }
        f_equal. eapply map_fix_rho_rename; eauto.

        simpl. rewrite !andb_false_r.
        move=> -> ->.
        rewrite rename_mkApps /= map_length. f_equal.
        2:{ rewrite !map_map_compose. solve_all. }
        f_equal. eapply map_fix_rho_rename; eauto.

        simpl.
        move=> -> ->.
        rewrite rename_mkApps /= map_length. f_equal.
        2:{ rewrite !map_map_compose. solve_all. }
        f_equal. eapply map_fix_rho_rename; eauto.

      + (* Lambda abstraction *)
        destruct (view_lambda_app tapp).
        ++ simpl. simpl in d.
           rewrite rename_inst /subst1 subst_inst.
           noconf Heqtapp.
           simpl in H.
           specialize (H0 _ _ _ H2). noconf H0.
           specialize (H2 _ _ _ H3).
           sigma. autorewrite with sigma in H0, H1, H2.
           rewrite H2. rewrite -H1. sigma. apply inst_ext.
           rewrite -ren_shiftn. sigma.
           unfold Up. now sigma.
        ++ subst t0. rewrite rho_tApp_discr //. simpl rename.
           rewrite rho_tApp_discr.
           now rewrite -(discr_lambda_app_rename r (tApp t u)).
           now rewrite -(isFix_app_rename r (tApp t u)).
           simpl. erewrite H0, H1; eauto.

    - (* Constant unfolding *)
      simpl.
      case e: lookup_env => [[kn decl|kn decl]|] //.
      case eb: cst_body => [b|] //.
      rewrite rename_inst inst_closed0 //.
      apply declared_decl_closed in e => //.
      hnf in e. rewrite eb in e. rewrite closedn_subst_instance_constr; auto.
      now move/andP: e => [-> _].

    - (* construct/cofix iota reduction *)
      simpl.
      assert (map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) l) =
              (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) l))) as <-.
      { red in X. rewrite !map_map_compose /compose /on_snd. solve_all. }
      rewrite -(H0 Γ) //.
      rewrite -(H Γ) //.
      case: p => [ind pars].
      case e: decompose_app => [hd args].
      rewrite (decompose_app_rename e).
      destruct (view_construct_cofix hd) => //.
      + simpl.
        case e': decompose_app => [hd' args'].
        rewrite (decompose_app_rename e').
        case: (view_construct hd') => [ind' n u' |] /=.
        change (eq_inductive ind c) with (eqb ind c).
        case: (@eqb_spec _ reflect_inductive ind c) => Hind.
        { (* Reduction *)
          rewrite /iota_red /= -map_skipn rename_mkApps !nth_map //. }
      { simpl. f_equal; auto. }
      { intros t1 Ht1.
        rewrite (nisConstruct_elim Ht1).
        rewrite (nisConstruct_elim (isConstruct_rename Ht1)).
        simpl. f_equal; auto. }

      + simpl.
        case e': decompose_app => [hd' args'].
        rewrite (decompose_app_rename e').
        apply decompose_app_inv' in e as [napp ->].
        rewrite rho_mkApps in e' => //.
        rewrite decompose_app_mkApps in e' => //.
        noconf e'. simpl.
        rewrite /map_fix !map_length !map_map_compose.
        red in X.
        rewrite /unfold_cofix !nth_error_map.
        case efix: (nth_error mfix idx) => [d|] /= //.
        * rewrite rename_mkApps !map_map_compose compose_map_def /on_snd.
          f_equal. f_equal => //.
          rewrite !subst_inst. sigma. apply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          rewrite map_cofix_subst' // !map_map_compose. rewrite map_cofix_subst' //.
          unfold compose. simpl. move=> n; f_equal.
          rewrite /map_fix map_length.
          rewrite !map_map_compose !compose_map_def.
          apply map_ext => x; apply map_def_eq_spec => //.
          apply map_ext => x. now rewrite /compose -rename_inst.
          now rewrite cofix_subst_length map_length.

        * rewrite map_map_compose /on_snd. f_equal.
          rewrite rename_mkApps /= !map_map_compose !compose_map_def /=.
          f_equal. f_equal.
          apply map_ext. intros.
          now rewrite map_length; apply map_def_eq_spec.

      + destruct t1; cbn; rewrite map_map_compose; auto.
        destruct d. destruct d.

    - (* Proj *)
      case: s => [[ind k] p] => /=.
      rewrite -(H Γ) //.
      case e: (decompose_app t) => [hd args].
      rewrite (decompose_app_rename e).
      destruct (view_construct_cofix hd) => //.
      + simpl.
        case e': decompose_app => [hd' args'].
        rewrite (decompose_app_rename e').
        case: (view_construct hd') => [ind' n u' | ] /=.
        rewrite nth_error_map.
        case enth : nth_error => [arg|] /= //.
        change eq_inductive with (@eqb inductive _).
        case: (eqb_spec ind ind') => Hind /= //.
        { intros t1 Ht1.
          rewrite (nisConstruct_elim Ht1).
          rewrite (nisConstruct_elim (isConstruct_rename Ht1)).
          simpl. f_equal; auto. }

      + simpl.
        case e': decompose_app => [hd' args'].
        rewrite (decompose_app_rename e').
        apply decompose_app_inv' in e as [napp ->].
        rewrite rho_mkApps in e' => //.
        rewrite decompose_app_mkApps in e' => //.
        noconf e'. simpl.
        rewrite /map_fix !map_length !map_map_compose.
        rewrite /unfold_cofix !nth_error_map.
        case efix: (nth_error mfix idx) => [d|] /= //.
        * rewrite rename_mkApps !map_map_compose compose_map_def /on_snd.
          f_equal. f_equal => //.
          rewrite !subst_inst. sigma. apply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          rewrite map_cofix_subst' // !map_map_compose. rewrite map_cofix_subst' //.
          unfold compose. simpl. move=> n; f_equal.
          rewrite /map_fix map_length.
          rewrite map_map_compose !compose_map_def. apply map_ext => x.
          apply map_def_eq_spec => //.
          apply map_ext => x. now rewrite /compose -rename_inst.
          now rewrite cofix_subst_length map_length.

        * rewrite rename_mkApps map_map_compose /on_snd. f_equal.
          rewrite /= !map_map_compose !compose_map_def /=.
          f_equal. f_equal.
          apply map_ext. intros.
          now rewrite map_length; apply map_def_eq_spec.

      + destruct t0; cbn; auto.
        destruct d. destruct d.

    - (* Fix *)
      simpl. f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X. solve_all.
      rewrite !compose_map_def.
      eapply map_def_eq_spec. eapply a. auto.
      unfold Basics.compose. erewrite b; auto.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      rewrite {2}H0.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.

    - (* CoFix *)
      simpl. f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X. solve_all.
      rewrite !compose_map_def.
      eapply map_def_eq_spec. eapply a. auto.
      unfold Basics.compose. erewrite b; auto.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      rewrite {2}H0.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.
  Qed.

  Lemma ren_lift_renaming n k : ren (lift_renaming n k) =1 (⇑^k ↑^n).
  Proof.
    unfold subst_compose. intros i.
    simpl. rewrite -{1}(Nat.add_0_r k). unfold ren. rewrite - (shiftn_lift_renaming n k 0).
    pose proof (ren_shiftn k (lift_renaming n 0) i).
    change ((ren (shiftn k (lift_renaming n 0)) i) = ((⇑^k (↑^n)) i)).
    rewrite -H. sigma. rewrite lift_renaming_0. reflexivity.
  Qed.

  Lemma shiftk_compose n m : ↑^n ∘ ↑^m =1 ↑^(n + m).
  Proof.
    induction n; simpl; sigma. reflexivity.
    rewrite -subst_compose_assoc.
    rewrite -shiftk_shift shiftk_shift_l.
    now rewrite subst_compose_assoc IHn -shiftk_shift shiftk_shift_l.
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

  Lemma rho_ctx_over_rev_mapi {Γ m} :
    List.rev (mapi (λ (i : nat) (x : def term),
                    vass (dname x) (lift0 i (rho (rho_ctx Γ) (dtype x)))) m) =
    rho_ctx_over (rho_ctx Γ) (fix_context m).
  Proof.
    rewrite - fold_fix_context_rev.
    now rewrite fold_fix_context_rho_ctx.
  Qed.

  Derive NoConfusion for bool.

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

  Lemma rho_triangle_All_All2_ind_noeq:
    ∀ (Γ Γ' : context) (brs0 brs1 : list (nat * term)),
      pred1_ctx Σ Γ Γ' →
      All2 (on_Trel_eq (λ x y : term, (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type) snd
                       fst) brs0 brs1 ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) snd) brs1 (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0).
  Proof.
    intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; pcuic.
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

  Hint Extern 40 => progress unfold on_Trel, on_decl, on_decl_over in * : pcuic.

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
    clear IHAll2 Hctxs. destruct r.
    destruct o0. destruct p. destruct p.
    simpl in *. simpl in H.
    rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
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
    clear IHAll2 Hctxs. destruct r.
    destruct o0. destruct p. destruct p. red in o.
    simpl in *. noconf Heqlen. simpl in H.
    rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
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

  Lemma rho_cofix_subst Γ mfix :
    cofix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (cofix_subst mfix)).
  Proof.
    unfold cofix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. reflexivity. simpl.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
  Qed.

  Lemma rho_fix_subst Γ mfix :
    fix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (fix_subst mfix)).
  Proof.
    unfold fix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. reflexivity. simpl.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
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
    → pred1_subst (Γ' ,,, fix_context mfix1) Γ'
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

  Lemma isConstruct_app_pred1 {Γ Δ a b} : pred1 Σ Γ Δ a b -> isConstruct_app a -> isConstruct_app b.
  Proof.
    move=> pr; rewrite /isConstruct_app.
    move e: (decompose_app a) => [hd args].
    apply decompose_app_inv in e. subst a. simpl.
    case: hd pr => // ind n ui.
    move/pred1_mkApps_tConstruct => [args' [-> Hargs']] _.
    rewrite decompose_app_mkApps //.
  Qed.

  Lemma isFix_app_inv f args x :
    ~~ isApp f -> isFix_app (tApp (mkApps f args) x) -> isFix f.
  Proof.
    move=> Hf.
    revert f Hf. induction args using rev_ind. simpl.
    induction f; simpl; try congruence.
    intros f Hf. simpl.
    rewrite -mkApps_nested. simpl. specialize (IHargs f Hf).
    simpl in IHargs. auto.
  Qed.


  Lemma pred1_mkApps_tLambda_inv (* (Σ : global_env) *) (Γ Δ : context) na ty b args0 c :
    pred1 Σ Γ Δ (mkApps (tLambda na ty b) args0) c ->
    ({ ty' & { b' & { args1 &
               (c = mkApps (tLambda na ty' b') args1) *
               (pred1 Σ Γ Δ ty ty') *
               (pred1 Σ (Γ ,, vass na ty) (Δ ,, vass na ty') b b') *
               (All2 (pred1 Σ Γ Δ) ) args0 args1 } } }%type) +
    ({ ty' & { b' & { hd & { tl &
               (pred1 Σ Γ Δ ty ty') *
               (pred1 Σ (Γ ,, vass na ty) (Δ ,, vass na ty') b b') *
               (All2 (pred1 Σ Γ Δ) args0 (hd :: tl)) *
               (c = mkApps (b' {0:= hd}) tl) } } } })%type.
  Proof with solve_discr.
    intros Hpred. remember (mkApps _ _) as fixt. revert na ty b args0 Heqfixt.
    induction Hpred; intros; solve_discr.
    - right. exists t1, b1, a1, []. intuition eauto.
    - clear IHHpred2.
      -- left. exists M', N', []. intuition eauto.
    - destruct args0 using rev_ind; try discriminate. clear IHargs0.
      rewrite -mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHHpred2.
      specialize (IHHpred1 _ _ _ _ eq_refl).
      destruct IHHpred1 as [[? [? [? ?]]]|[? [? [? [? ?]]]]].
      -- left. eexists x, x0, (x1 ++ [N1]). intuition eauto. subst M1.
         now rewrite -mkApps_nested. subst M1.
         eapply All2_app; eauto.
      -- right. eexists x, x0.
         destruct p as [[? ?] ?]. subst M1.
         depelim a.
         exists x1, (x2 ++ [N1]). intuition auto.
         rewrite app_comm_cons.
         eapply All2_app; auto.
         now rewrite -mkApps_nested.
    - subst t. solve_discr.
  Qed.

  Lemma is_constructor_rho Γ n args :
    is_constructor n args -> is_constructor n (map (rho (rho_ctx Γ)) args).
  Proof.
    rewrite /is_constructor nth_error_map.
    case e: nth_error => [a|] /=.
    apply isConstruct_app_rho. auto.
  Qed.

  Lemma mkApps_inj_args_length f f' l l' : #|l| = #|l'| -> mkApps f l = mkApps f' l' -> f = f' /\ l = l'.
  Proof.
    revert l'. elim/@rev_ind: l => [|hd tl IH]. case => /= //.
    elim/@rev_ind => [|hd' tl' _] => /= //; rewrite !app_length /= ?Nat.add_1_r //.
    move=> [=] Htl. rewrite - !mkApps_nested /= => [=] Hf ->.
    now case: (IH _ Htl Hf) => <- <-.
  Qed.

  Lemma pred1_mkApps_Lambda_Fix_inv Γ Γ' f a u l a' l' :
    isFix u -> isLambda f -> #|l| = #|l'| ->
    pred1 Σ Γ Γ' (mkApps f (a :: l)) (mkApps u (a' :: l')) ->
    ∑ na ty b ty' b' a'',
    (f = tLambda na ty b) *
    (tApp u a' = b' {0 := a''}) *
    pred1 Σ Γ Γ' ty ty' *
    pred1 Σ Γ Γ' a a'' *
    pred1 Σ (Γ ,, vass na ty) (Γ' ,, vass na ty') b b' *
    All2 (pred1 Σ Γ Γ') l l'.
  Proof.
    move => Hu Hf Hl Hpred.
    destruct f; try discriminate.
    eapply pred1_mkApps_tLambda_inv in Hpred.
    destruct Hpred as [(ty' & b' & args' & ((H' & ?) & ?) & H'')|(ty' & b' & hd & tl & (((?&?) & ?) & ?))].
    depelim H''. destruct u; try discriminate.
    eapply mkApps_eq_inj in H' as [He Hargs] => //.
    exists na, f1, f2, ty', b', hd. destruct u; try discriminate.
    depelim a0.
    pose proof (All2_length _ _ a0).
    simpl in e.
    eapply mkApps_inj_args_length in e.
    simpl. intuition auto. subst. auto. lia.
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
      rewrite rho_mkApps //.
      rewrite decompose_app_mkApps; auto. simpl.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec ind ind); try discriminate.
      unfold iota_red. eapply pred_mkApps; eauto.
      eapply pred_snd_nth. red in X2.
      now eapply rho_triangle_All_All2_ind_noeq. auto.
      eapply All2_skipn. eapply All2_sym.
      rewrite - {1} (map_id args1). eapply All2_map, All2_impl; eauto. simpl. intuition.
      congruence.

    - (* Fix reduction *)
      unfold unfold_fix in heq_unfold_fix |- *.
      generalize (rho_fix_unfold_inv (rho_ctx Γ) mfix0 idx args0).
      destruct nth_error eqn:Heq; noconf heq_unfold_fix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      rewrite Hnth. simpl.
      destruct args0. depelim X4. unfold is_constructor in heq_is_constructor.
      rewrite nth_error_nil in heq_is_constructor => //.
      pose proof Hnth.
      eapply All2_nth_error_Some in H; eauto.
      destruct H as [fn' [Hnth' [? ?]]].
      destruct t', d.
      simpl in * |-. noconf Heq. destruct o, p as [[ol ol'] or].
      simpl in * |-. noconf or.
      revert X4. generalize (t :: args0). clear t args0. intros args0 Hargs.
      simpl. destruct (isLambda dbody0) eqn:isl; noconf heq_unfold_fix.
      case e: isLambda => /=.
      move: heq_is_constructor.
      unfold is_constructor.
      case enth: nth_error => [a|] /= //.
      rewrite nth_error_map.
      eapply (All2_nth_error_Some_right _ _ Hargs) in enth as [t' [-> [redt' redat']]].
      simpl in redt'. simpl.
      move/(isConstruct_app_pred1 redat') => ->.
      move ->.
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

      simpl.
      (* Impossible: the body of a fix has to be a lambda *)
      destruct dbody0; try discriminate.
      clear -wfΣ Hreleq1 e. depelim Hreleq1. solve_discr.
      rewrite rho_ctx_app in H. rewrite /rho_fix_context in e.
      rewrite -fold_fix_context_rho_ctx in e. rewrite H in e.
      discriminate. depelim i.

    - (* Case-CoFix reduction *)
      simpl. destruct ip.
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
      set (rhoΓ := rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) in *.
      rewrite !subst_inst. eapply simpl_pred; try now sigma.
      eapply strong_substitutivity. eauto. apply ctxmap_cofix_subst.
      unfold rhoΓ.
      rewrite -{1}fix_context_map_fix.
      now eapply ctxmap_cofix_subst.
      now eapply pred_subst_rho_cofix; auto.
      eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
      eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel in *.
      intuition eauto.

    - (* Proj-Cofix reduction *)
      simpl.
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
      { eapply wf_rho_cofix_subst; eauto.
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
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec i i) => //.

    - simpl. eapply pred_abs; auto. unfold snoc in *. simpl in X2.
      rewrite app_context_nil_l in X2. apply X2.

    - case le': (isFix_app (tApp M0 N0)).
      + (* Fix at head *)
        rewrite rho_app_unfold /rho_app.
        case e: decompose_app => [hd args].
        eapply decompose_app_inv' in e as [Hhd Heq].
        destruct args using rev_ind. simpl in Heq. rewrite -Heq in Hhd. discriminate.
        clear IHargs. rewrite -mkApps_nested in Heq. noconf Heq.
        apply isFix_app_inv in le' => //.
        destruct hd; try discriminate.
        move: X0.
        rewrite -rho_fix_unfold.
        destruct (rho_fix_elim (rho_ctx Γ) mfix idx args).
        move/andP: i => [isl isc].
        destruct (rho_fix_elim (rho_ctx Γ) mfix idx (args ++ [N0])).
        * (* Both reduce *)
          rewrite e in e0. noconf e0.
          rewrite map_app in i.
          move/andP: i => [isl' isc'].
          rewrite (is_constructor_app_ge (rarg d) _ _) in isc' => //.
          rewrite map_app - !mkApps_nested.
          move=> redo. eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
          repeat constructor; auto.
        * (* Shorter appliction reduces, longer one doesn't: impossible *)
          elimtype False.
          rewrite e in y. cbn in y. rewrite isl in y.
          destruct y; auto.
          rewrite map_app (is_constructor_app_ge (rarg d) _ _) in H => //.
        * (* Shorter application does not reduce *)
          destruct (rho_fix_elim (rho_ctx Γ) mfix idx (args ++ [N0])).
          ** (* Longer application reduces *)
            rewrite e in y.
            rewrite map_app in i.
            move/andP: i => [isl' isc'].
            simpl in y. rewrite isl' in y.
            assert (~~ is_constructor (rarg d) (map (rho (rho_ctx Γ)) args) /\ rarg d = #|args|) as [isc rargl].
            { destruct y => //. split; auto.
              move: isc' H; rewrite /is_constructor.
              rewrite !nth_error_map.
              destruct (Nat.leb_spec (S (rarg d)) #|args|).
              rewrite nth_error_app_lt ?map_length //.
              rewrite !nth_error_map. move => ->. discriminate.
              rewrite nth_error_app_ge ?map_length //. lia.
              simpl.
              case e': nth_error => [arg'|]. simpl.
              move => isC _. eapply nth_error_Some_length in e'. simpl in e'. lia.
              discriminate. }
            simpl.
            case: (pred1_mkApps_tFix_inv _ _ _ _ _ _ _ X).
            { move=> [mfix1 [args1 [[HM1 Hmfix] Hargs]]].
              move: HM1 X => -> X.
              rewrite [tApp _ _](mkApps_nested _ _ [N1]).
              move/pred1_mkApps_tFix_refl_inv => [redo redargs].
              rewrite map_app.
              eapply pred_fix; eauto with pcuic.
              eapply pred1_rho_fix_context_2; auto with pcuic.
              red in redo. solve_all.
              unfold on_Trel in *. intuition auto. now noconf b0.
              now noconf b0.
              unfold unfold_fix. rewrite nth_error_map e /=.
              rewrite /rho_fix_context in isl'. rewrite isl'.
              rewrite map_fix_subst /= //.
              eapply All2_app => //. repeat constructor; auto. }
            { move => [mfix1 [args1 [narg [fn' [[[[Hunf Hpre] Hpre']] a]]]]] eq.
              subst M1.
              rewrite /unfold_fix in Hunf.
              red in Hpre.
              case Heq: (nth_error mfix1 idx) Hunf => [d'|] //.
              destruct (isLambda (dbody d')) eqn:isl => //. move => [=] Harg Hfn'.
              subst fn' narg.
              eapply All2_nth_error_Some_right in Heq; eauto.
              destruct Heq as [d'' [nth' Hd'']]. rewrite nth' in e; noconf e.
              move => redo.
              rewrite map_app -mkApps_nested.
              apply (pred_mkApps _ _ _ _ _ [N1] _).
              case: Hd'' => reddd' [Hdd' deq].
              noconf deq. simpl in H. noconf H. rewrite -H0 in Hpre'.
              move: Hpre'; rewrite /is_constructor.
              rewrite (All2_length _ _ a) in rargl.
              rewrite rargl. rewrite (proj2 (nth_error_None _ _)). lia. discriminate.
              repeat constructor; auto. }

          ** (* None reduce *)
            simpl. rewrite map_app.
            rewrite -mkApps_nested => redo.
            apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
            repeat constructor; auto.
      + case le: (lambda_app_discr (tApp M0 N0)).
        simpl in le'.
        destruct M0; try discriminate.
        (* Beta at top *)
        depelim X. solve_discr.
        depelim X0... econstructor; eauto.
        discriminate.
        rewrite rho_tApp_discr => //.
        now apply: negbT. now apply: negbT.
        constructor; auto.

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
          --- apply All2_sym. eapply All2_map_left. eapply All2_impl; eauto.
              unfold on_Trel in *.
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
        change eq_inductive with (@eqb inductive _).
        destruct (eqb_spec ind c0); subst.
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
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simpl.
      rewrite - fold_fix_context_rho_ctx.
      constructor; eauto.
      now eapply All2_local_env_pred_fix_ctx. red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simpl; econstructor; eauto. simpl in X2. now rewrite !app_context_nil_l in X2.
    - simpl in *. constructor. eauto. eapply All2_sym, All2_map_left, All2_impl. eauto.
      intros. simpl in X. intuition.
    - destruct t; noconf H; simpl; constructor; eauto.
  Qed.

  End TriangleFn.

  (* The confluence theorem in terms of the triangle operator. *)

  Corollary confluence {cf : checker_flags} : forall Σ Γ Δ Δ' t u v, wf Σ ->
    pred1 Σ Γ Δ t u ->
    pred1 Σ Γ Δ' t v ->
    pred1 Σ Δ (rho_ctx Σ Γ) u (rho Σ (rho_ctx Σ Γ) t) *
    pred1 Σ Δ' (rho_ctx Σ Γ) v (rho Σ (rho_ctx Σ Γ) t).
  Proof.
    intros.
    split; eapply triangle; auto.
  Qed.

End Confluence.

Print Assumptions confluence.
