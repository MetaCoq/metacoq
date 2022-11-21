From Coq Require Import ssreflect.
From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICProgram TemplateToPCUIC.

Definition isConstruct t :=
   match t with tConstruct _ _ _ => true | _ => false end.

 Definition isFix t :=
  match t with tFix _ _ => true | _ => false end.

Definition isRel t :=
    match t with tRel _ => true | _ => false end.

Section expanded.

Variable Σ : global_env.

Local Unset Elimination Schemes.

Inductive expanded (Γ : list nat) : term -> Prop :=
| expanded_tRel (n : nat) m args : nth_error Γ n = Some m -> forall Hle : m <= #|args|, Forall (expanded Γ) args -> expanded Γ (mkApps (tRel n) args)
| expanded_tVar (id : ident) : expanded Γ (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall (expanded Γ) args -> expanded Γ (tEvar ev args)
| expanded_tSort (s : Universe.t) : expanded Γ (tSort s)
| expanded_tProd (na : aname) (ty : term) (body : term) : expanded Γ (tProd na ty body)
| expanded_tLambda (na : aname) (ty : term) (body : term) : expanded (0 :: Γ) body -> expanded Γ (tLambda na ty body)
| expanded_tLetIn (na : aname) (def : term) (def_ty : term) (body : term) : expanded Γ def -> expanded (0 :: Γ) body -> expanded Γ (tLetIn na def def_ty body)
| expanded_mkApps (f : term) (args : list term) : ~ (isConstruct f || isFix f || isRel f) -> expanded Γ f -> Forall (expanded Γ) args -> expanded Γ (mkApps f args)
| expanded_tConst (c : kername) (u : Instance.t) : expanded Γ (tConst c u)
| expanded_tInd (ind : inductive) (u : Instance.t) : expanded Γ (tInd ind u)
| expanded_tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term)) : expanded Γ discr ->
        Forall (expanded Γ) type_info.(pparams) ->
        Forall (fun br =>
          ∥ All_fold (fun Δ d => ForOption (fun b => expanded (repeat 0 #|Δ| ++ repeat 0 #|type_info.(pparams)|) b) d.(decl_body)) br.(bcontext) ∥ /\
          expanded (repeat 0 #|br.(bcontext)| ++ Γ) br.(bbody)) branches ->
        expanded Γ (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded Γ t -> expanded Γ (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d :
  Forall (fun d => isLambda d.(dbody) /\ let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in expanded (ctx ++ Γ) d.(dbody)) mfix ->
  Forall (expanded Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  expanded Γ (mkApps (tFix mfix idx) args)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) :   Forall (fun d => expanded (repeat 0 #|mfix| ++ Γ) d.(dbody)) mfix -> expanded Γ (tCoFix mfix idx)
| expanded_tConstruct_app ind c u mind idecl cdecl args :
    declared_constructor Σ (ind, c) mind idecl cdecl ->
    #|args| >= (ind_npars mind + context_assumptions (cstr_args cdecl)) ->
    Forall (expanded Γ) args ->
    expanded Γ (mkApps (tConstruct ind c u) args)
| expanded_tPrim p : expanded Γ (tPrim p).

End expanded.
Derive Signature for expanded.

Definition expanded_context Σ Γ ctx :=
  ∥ All_fold (fun Δ d => ForOption (expanded Σ (repeat 0 #|Δ| ++ Γ)) d.(decl_body)) ctx ∥.

Lemma expanded_ind :
  forall (Σ : global_env) (P : list nat -> term -> Prop),
  (forall (Γ : list nat) (n m : nat) (args : list term),
  nth_error Γ n = Some m ->
  m <= #|args| -> Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps (tRel n) args)) ->
  (forall (Γ : list nat) (id : ident), P Γ (tVar id)) ->
  (forall (Γ : list nat) (ev : nat) (args : list term),
  Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (tEvar ev args)) ->
  (forall (Γ : list nat) (s : Universe.t), P Γ (tSort s)) ->
  (forall (Γ : list nat) (na : aname) (ty body : term), P Γ (tProd na ty body)) ->
  (forall (Γ : list nat) (na : aname) (ty body : term),
  expanded Σ (0 :: Γ) body -> P (0 :: Γ) body -> P Γ (tLambda na ty body)) ->
  (forall (Γ : list nat) (na : aname) (def def_ty body : term),
  expanded Σ Γ def ->
  P Γ def ->
  expanded Σ (0 :: Γ) body ->
  P (0 :: Γ) body -> P Γ (tLetIn na def def_ty body)) ->
  (forall (Γ : list nat) (f6 : term) (args : list term),
  ~ (isConstruct f6 || isFix f6 || isRel f6) ->
  expanded Σ Γ f6 ->
  P Γ f6 -> Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps f6 args)) ->
  (forall (Γ : list nat) (c : kername) (u : Instance.t), P Γ (tConst c u)) ->
  (forall (Γ : list nat) (ind : inductive) (u : Instance.t), P Γ (tInd ind u)) ->
  (forall (Γ : list nat) (ci : case_info) (type_info : predicate term)
    (discr : term) (branches : list (branch term)),
  expanded Σ Γ discr ->
  P Γ discr ->
  Forall (expanded Σ Γ) type_info.(pparams) ->
  Forall (P Γ) type_info.(pparams) ->
  Forall
    (fun br : branch term =>
    expanded_context Σ (repeat 0 #|type_info.(pparams)|)  br.(bcontext) /\
    expanded Σ (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
    Forall
    (fun br : branch term =>
      ∥ All_fold (fun Δ d => ForOption (fun b => P (repeat 0 (#|Δ| + #|type_info.(pparams)|)) b) d.(decl_body)) br.(bcontext) ∥ /\
      P (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
      P Γ (tCase ci type_info discr branches)) ->
  (forall (Γ : list nat) (proj : projection) (t : term),
  expanded Σ Γ t -> P Γ t -> P Γ (tProj proj t)) ->
  (forall (Γ : list nat) (mfix : mfixpoint term) (idx : nat)
    (args : list term) (d : def term),
  Forall
    (fun d0 : def term =>
      isLambda d0.(dbody) /\ let ctx := rev_map (fun d1 : def term => 1 + rarg d1) mfix in
      expanded Σ (ctx ++ Γ) (dbody d0)) mfix ->
  Forall
      (fun d0 : def term =>
      let ctx := rev_map (fun d1 : def term => 1 + rarg d1) mfix in
      P (ctx ++ Γ) (dbody d0)) mfix ->
  Forall (expanded Σ Γ) args -> Forall (P Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > rarg d -> P Γ (mkApps (tFix mfix idx) args)) ->
  (forall (Γ : list nat) (mfix : mfixpoint term) (idx : nat),
  Forall (fun d : def term => expanded Σ (repeat 0 #|mfix| ++ Γ) (dbody d))
    mfix ->  Forall (fun d : def term => P (repeat 0 #|mfix| ++ Γ) (dbody d))
    mfix  -> P Γ (tCoFix mfix idx)) ->
  (forall (Γ : list nat) (ind : inductive) (c : nat)
    (u : Instance.t) (mind : mutual_inductive_body)
    (idecl : one_inductive_body) (cdecl : constructor_body)
    (args : list term),
  declared_constructor Σ (ind, c) mind idecl cdecl ->
  #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
  Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (mkApps (tConstruct ind c u) args)) ->
  (forall Γ p, P Γ (tPrim p)) ->
  forall (Γ : list nat) (t : term), expanded Σ Γ t -> P Γ t.
Proof.
  intros Σ P HRel HVar HEvar HSort HProd HLamdba HLetIn HApp HConst HInd HCase HProj HFix HCoFix HConstruct HPrim.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  - eapply HRel; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HEvar; eauto. clear - f H. induction H; econstructor; eauto.
  - eapply HApp; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HCase; eauto. induction H; econstructor; eauto.
    clear -H1 f. induction H1; constructor; auto.
    clear -H0 f.
    revert H0. induction 1; constructor; auto.
    split. destruct H as [[] ?]; constructor; auto.
    clear -X f. induction X; constructor; auto. destruct p; constructor; auto.
    apply f. rewrite repeat_app. exact H.
    eapply f, H.
  - assert (Forall (P Γ) args). { clear - H0 f. induction H0; econstructor; eauto. }
    eapply HFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H. induction H; econstructor; cbn in *; intuition eauto; split.
  - eapply HCoFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct; eauto.
    clear - H1 f. induction H1; econstructor; eauto.
Qed.

From MetaCoq.PCUIC Require Import PCUICInductiveInversion PCUICLiftSubst PCUICSigmaCalculus.

Record expanded_constant_decl Σ (cb : constant_body) : Prop :=
  { expanded_body : on_Some_or_None (expanded Σ []) cb.(cst_body); }.
    (* expanded_type : expanded Σ [] cb.(Ast.Env.cst_type) }. *)

Record expanded_constructor_decl Σ mdecl cdecl :=
  { expanded_cstr_args : expanded_context Σ (repeat 0 (#|mdecl.(ind_params)| + #|mdecl.(ind_bodies)|)) cdecl.(cstr_args) }.
    (* expanded_cstr_indices : All (expanded Σ []) cdecl.(cstr_indices); *)
    (* expanded_cstr_type : expanded Σ (repeat 0 #|mdecl.(ind_bodies)|) cdecl.(cstr_type) }. *)

Record expanded_inductive_decl Σ mdecl idecl :=
  { (* expanded_ind_type : expanded Σ [] idecl.(ind_type); *)
    expanded_ind_ctors : Forall (expanded_constructor_decl Σ mdecl) idecl.(ind_ctors) }.

Record expanded_minductive_decl Σ mdecl :=
  { expanded_params : expanded_context Σ [] mdecl.(ind_params);
    expanded_ind_bodies : Forall (expanded_inductive_decl Σ mdecl) mdecl.(ind_bodies) }.

Definition expanded_decl Σ d :=
  match d with
  | ConstantDecl cb => expanded_constant_decl Σ cb
  | InductiveDecl idecl => expanded_minductive_decl Σ idecl
  end.

Inductive expanded_global_declarations (univs : ContextSet.t) retro : forall (Σ : global_declarations), Prop :=
| expanded_global_nil : expanded_global_declarations univs retro []
| expanded_global_cons decl Σ : expanded_global_declarations univs retro Σ ->
  expanded_decl {| universes := univs; declarations := Σ; retroknowledge := retro |} decl.2 ->
  expanded_global_declarations univs retro (decl :: Σ).

Definition expanded_global_env (g : global_env) :=
  expanded_global_declarations g.(universes) g.(retroknowledge) g.(declarations).

Definition expanded_pcuic_program (p : pcuic_program) :=
  expanded_global_env p.1 /\ expanded p.1 [] p.2.


Lemma All_tip {A} {P : A -> Type} {a : A} : P a <~> All P [a].
Proof. split; intros. repeat constructor; auto. now depelim X. Qed.

Lemma expanded_mkApps_expanded {Σ Γ f args} :
  expanded Σ Γ f -> All (expanded Σ Γ) args ->
  expanded Σ Γ (mkApps f args).
Proof.
  intros.
  destruct (isConstruct f || isFix f || isRel f) eqn:eqc.
  destruct f => //.
  - depelim H; solve_discr. eapply expanded_tRel; tea. cbn in Hle. lia. solve_all.
    destruct args0 using rev_case; cbn in *; subst. cbn in H. congruence.
    rewrite mkApps_app in H2; noconf H2.
  - depelim H; solve_discr.
    destruct args0 using rev_case; cbn in *; subst. cbn in H. congruence.
    rewrite mkApps_app in H2; noconf H2.
    eapply expanded_tConstruct_app; tea. cbn in H0. lia. solve_all.
  - depelim H; solve_discr.
    destruct args0 using rev_case; cbn in *; subst. cbn in H. congruence.
    rewrite mkApps_app in H2; noconf H2.
  - eapply expanded_mkApps. now rewrite eqc. auto. solve_all.
Qed.

Lemma expanded_lift Σ n k b Γ Δ Δ' :
  #|Γ| = k ->
  #|Δ'| = n ->
  expanded Σ (Γ ++ Δ) b ->
  expanded Σ (Γ ++ Δ' ++ Δ) (lift n k b).
Proof.
  intros Hk Hn.
  remember (Γ ++ Δ)%list as Γ_.
  intros exp; revert Γ n k Hn Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' n' k Hn Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:try solve [cbn; econstructor => //; solve_all ].
  - subst n'. rewrite lift_mkApps /=.
    destruct (Nat.leb_spec k n).
    * rewrite nth_error_app_ge in H. lia.
      eapply expanded_tRel.
      rewrite nth_error_app_ge; [lia|].
      rewrite nth_error_app_ge; [lia|]. erewrite <- H. lia_f_equal.
      now len. solve_all.
    * eapply expanded_tRel.
      rewrite nth_error_app_lt in H; [lia|].
      rewrite nth_error_app_lt; [lia|]. tea. now len. solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') n' (S k)); cbn; auto; lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') n' (S k)); cbn; auto; lia.
  - rewrite lift_mkApps.
    destruct (isConstruct (lift n' k f6) || isFix (lift n' k f6) || isRel (lift n' k f6)) eqn:eqc.
    specialize (IHexp  _ _ _ Hn Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. now rewrite eqc. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. solve_all. cbn. solve_all.
    solve_all.
    specialize (H1 (repeat 0 #|bcontext x| ++ Γ') n' (#|bcontext x| + k) Hn).
    forward H1. len.
    forward H1. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H1.
  - rewrite lift_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all.
      specialize (a
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (lift n' k) (lift n' (#|mfix| + k))) mfix) ++ Γ') n' (#|mfix| + k) Hn).
      forward a. { rewrite rev_map_spec; len. }
      forward a. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a.
    + solve_all.
    + destruct args => //.
    + rewrite nth_error_map /= H4 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a (repeat 0 #|mfix| ++ Γ') n' (#|mfix| + k) Hn).
    forward a. { len. }
    forward a. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a.
  - rewrite lift_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
Qed.

Lemma expanded_subst Σ a k b Γ Δ :
    #|Γ| = k ->
  Forall (expanded Σ Δ) a ->
  expanded Σ (Γ ++ repeat 0 #|a| ++ Δ) b ->
  expanded Σ (Γ ++ Δ) (subst a k b).
Proof.
  intros Hk H.
  remember (Γ ++ _ ++ Δ)%list as Γ_.
  intros exp; revert Γ k Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' k Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:solve[ cbn; econstructor => //; solve_all ].
  - rewrite subst_mkApps /=.
    destruct (Nat.leb_spec k n).
    destruct (nth_error a _) eqn:hnth.
    * eapply expanded_mkApps_expanded.
      eapply nth_error_forall in H; tea.
      eapply (expanded_lift Σ k 0 _ [] Δ Γ'); auto.
      solve_all.
    * rewrite nth_error_app_ge in H0. lia.
      eapply nth_error_None in hnth.
      rewrite nth_error_app_ge in H0. rewrite repeat_length. lia.
      rewrite repeat_length in H0.
      eapply expanded_tRel. rewrite nth_error_app_ge. lia. erewrite <- H0.
      lia_f_equal. len. solve_all.
    * rewrite nth_error_app_lt in H0. lia.
      eapply expanded_tRel. rewrite nth_error_app_lt. lia. tea. now len.
      solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') (S k)); cbn; auto; lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') (S k)); cbn; auto; lia.
  - rewrite subst_mkApps.
    destruct (isConstruct (subst a k f6) || isFix (subst a k f6) || isRel (subst a k f6)) eqn:eqc.
    specialize (IHexp  _ _ Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. now rewrite eqc. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. cbn. solve_all. solve_all.
    specialize (H2 (repeat 0 #|bcontext x| ++ Γ') (#|bcontext x| + k)).
    forward H2 by len.
    forward H2. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H2.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all. now eapply isLambda_subst.
      specialize (a0
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (subst a k) (subst a (#|mfix| + k))) mfix) ++ Γ') (#|mfix| + k)).
      forward a0 by len.
      forward a0. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a0.
    + solve_all.
    + now destruct args.
    + rewrite nth_error_map /= H5 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a0 (repeat 0 #|mfix| ++ Γ') (#|mfix| + k)).
    forward a0 by len.
    forward a0. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a0.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
Qed.

Lemma All_fold_tip {A : Type} (P : list A -> A -> Type) {x} : All_fold P [x] -> P [] x.
Proof.
  intros a; now depelim a.
Qed.

Lemma expanded_let_expansion Σ (Δ : context) Γ t :
  expanded_context Σ Γ Δ ->
  expanded Σ (repeat 0 #|Δ| ++ Γ) t ->
  expanded Σ (repeat 0 (context_assumptions Δ) ++ Γ) (expand_lets Δ t).
Proof.
  intros [ha].
  revert Γ t ha.
  induction Δ using PCUICInduction.ctx_length_rev_ind.
  - cbn; intros. now rewrite expand_lets_nil.
  - intros Γ' t ha; destruct d as [na [b|] ty]; cbn; len; cbn.
    * rewrite expand_lets_vdef /= //.
      intros exp. relativize (context_assumptions Γ).
      eapply H. now len.
      { eapply All_fold_app_inv in ha as [].
        depelim a. depelim a. cbn in *.
        rewrite /subst_context.
        eapply PCUICParallelReduction.All_fold_fold_context_k.
        eapply All_fold_impl; tea. cbn; intros.
        depelim f.
        destruct decl_body => //; constructor. depelim H1.
        len in H1. cbn in H1.
        cbn. len. eapply expanded_subst. now rewrite repeat_length. eauto.
        auto. cbn. now rewrite repeat_app /= -app_assoc /= in H1. }
      len.
      rewrite repeat_app -app_assoc /= in exp.
      eapply All_fold_app_inv in ha as []. eapply All_fold_tip in a. cbn in a. depelim a.
      eapply expanded_subst. rewrite repeat_length //. constructor; auto.
      cbn. exact exp. now len.
    * rewrite expand_lets_vass /= //.
      rewrite !repeat_app -!app_assoc.
      intros exp. relativize (context_assumptions Γ).
      eapply H. lia.
      { eapply All_fold_app_inv in ha as [].
        depelim a. cbn in f. depelim a.
        eapply All_fold_impl; tea. cbn; intros.
        destruct decl_body => //; constructor. depelim H0. len in H0. cbn in H0.
        now rewrite repeat_app /= -app_assoc /= in H0. }
      exact exp. lia.
Qed.

Require Import PCUICUnivSubst.

Lemma subst_instance_isConstruct t u : isConstruct t@[u] = isConstruct t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isRel t u : isRel t@[u] = isRel t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isFix t u : isFix t@[u] = isFix t.
Proof. destruct t => //. Qed.
Lemma subst_instance_isLambda t u : isLambda t@[u] = isLambda t.
Proof. destruct t => //. Qed.

Lemma expanded_subst_instance Σ Γ t u : expanded Σ Γ t -> expanded Σ Γ t@[u].
Proof.
  induction 1 using PCUICEtaExpand.expanded_ind; cbn.
  all:intros; rewrite ?subst_instance_mkApps.
  all:try solve [econstructor; eauto 1].
  - econstructor; eauto. now rewrite map_length. solve_all.
  - econstructor; eauto. solve_all.
  - econstructor; eauto. 2:solve_all.
    rewrite subst_instance_isConstruct subst_instance_isFix subst_instance_isRel //.
  - econstructor; eauto. cbn. solve_all.
    solve_all.
  - cbn; eapply expanded_tFix. solve_all. rewrite subst_instance_isLambda //.
    rewrite rev_map_spec map_map_compose -rev_map_spec //.
    solve_all. now destruct args => //.
    rewrite nth_error_map H4 //.
    now len.
  - econstructor; eauto. solve_all.
  - eapply expanded_tConstruct_app; tea. now len. solve_all.
Qed.

Lemma expanded_weakening Σ Γ t : expanded Σ Γ t -> forall Γ', expanded Σ (Γ ++ Γ') t.
Proof.
  induction 1 using PCUICEtaExpand.expanded_ind; cbn.
  1:{ intros. eapply expanded_tRel; tea. rewrite nth_error_app_lt.
     now eapply nth_error_Some_length in H. assumption.
    solve_all. }
  all:intros; try solve [econstructor; eauto 1; solve_all; try now rewrite app_assoc].
Qed.
