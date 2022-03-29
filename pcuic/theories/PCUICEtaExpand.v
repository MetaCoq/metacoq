From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.

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
        (discr:term) (branches : list (branch term)) : expanded Γ discr -> Forall (fun br => expanded (repeat 0 #|br.(bcontext)| ++ Γ) br.(bbody)) branches -> expanded Γ (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded Γ t -> expanded Γ (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d : 
  Forall (fun d => let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in expanded (ctx ++ Γ) d.(dbody)) mfix ->
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
    expanded Γ (mkApps (tConstruct ind c u) args).

End expanded.

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
 Forall
   (fun br : branch term =>
	expanded Σ (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
  Forall
  (fun br : branch term =>
 P (repeat 0 #|bcontext br| ++ Γ) (bbody br)) branches ->
 P Γ (tCase ci type_info discr branches)) ->
(forall (Γ : list nat) (proj : projection) (t : term),
 expanded Σ Γ t -> P Γ t -> P Γ (tProj proj t)) ->
(forall (Γ : list nat) (mfix : mfixpoint term) (idx : nat) 
   (args : list term) (d : def term),
 Forall
   (fun d0 : def term =>
    let ctx := rev_map (fun d1 : def term => 1 + rarg d1) mfix in
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
forall (Γ : list nat) (t : term), expanded Σ Γ t -> P Γ t.
Proof.
  intros Σ P HRel HVar HEvar HSort HProd HLamdba HLetIn HApp HConst HInd HCase HProj HFix HCoFix HConstruct.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  - eapply HRel; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HEvar; eauto. clear - f H. induction H; econstructor; eauto.
  - eapply HApp; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HCase; eauto. induction H; econstructor; eauto.
  - assert (Forall (P Γ) args). { clear - H0 f. induction H0; econstructor; eauto. }
    eapply HFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HCoFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct; eauto.
    clear - H1 f. induction H1; econstructor; eauto.
Qed.
