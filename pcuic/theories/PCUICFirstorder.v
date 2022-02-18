From Coq Require Import Program ssreflect ssrbool List.
From MetaCoq.Template Require Import config utils Kernames MCRelations.


From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction   
  PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp
  PCUICContextConversionTyp
  PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion
  PCUICUnivSubstitutionTyp
  PCUICCumulativity PCUICSR PCUICSafeLemmata
  PCUICValidity PCUICPrincipality PCUICElimination 
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICCanonicity.

From MetaCoq Require Import PCUICArities PCUICSpine.
From MetaCoq.PCUIC Require PCUICWcbvEval.



Section firstorder.

  Context {Σ : global_env_ext}.
  Context {Σb : list (kername × (Instance.t -> list bool))}.
  
  Fixpoint plookup_env {A} (Σ : list (kername × A)) (kn : kername) {struct Σ} :
  option A :=
  match Σ with
  | [] => None
  | d :: tl => if eq_kername kn d.1 then Some d.2 else plookup_env tl kn
  end. 
  (* 
  Definition zo_type (t : term) :=
    match (PCUICAstUtils.decompose_app t).1 with
    | tProd _ _ _ => false
    | tSort _ => false
    | tInd (mkInd nm i) _ => match (plookup_env Σb nm) with 
                             | Some l => nth i l false | None => false
                             end
    | _ => true
    end. *)
  
  Definition firstorder_type (t : term) :=
    match (PCUICAstUtils.decompose_app t).1 with
    | tInd (mkInd nm i) u => match (plookup_env Σb nm) with 
                             | Some f => nth i (f u) false | None => true
                             end
    | _ => false
    end.
  (* 
  Definition firstorder_type (t : term) :=
    match (PCUICAstUtils.decompose_app t).1 with
    | tInd (mkInd nm i) _ => match (plookup_env Σb nm) with 
                             | Some l => nth i l false | None => false
                             end
    | _ => false
    end. *)
  
  Definition firstorder_con i u mind (c : constructor_body):=
    forallb (fun '({| decl_body := b ; decl_type := t ; decl_name := n|}) => firstorder_type t) 
      (subst_context (inds i u mind.(ind_bodies)) 0 (c.(cstr_args) ++ mind.(ind_params))@[u])%list.
  
  Definition firstorder_oneind i u mind (ind : one_inductive_body) :=
    forallb (firstorder_con i u mind) ind.(ind_ctors) && negb (Universe.is_level (ind_sort ind)).
    
  Definition firstorder_mutind i u (mind : mutual_inductive_body) :=
    (* if forallb (fun decl => firstorder_type decl.(decl_type)) mind.(ind_params) then *)
    map (firstorder_oneind i u mind) mind.(ind_bodies)
    (* else repeat false (length mind.(ind_bodies)). *).
  
  Definition firstorder_ind (i : inductive) u :=
    match lookup_env Σ.1 (inductive_mind i) with
    | Some (InductiveDecl mind) =>
        check_recursivity_kind Σ (inductive_mind i) Finite &&
        nth (inductive_ind i) (firstorder_mutind i.(inductive_mind) u mind) false
    | _ => false
    end.
  
End firstorder.
  
Fixpoint firstorder_env' (Σ : global_env) Σb :=
  match Σ with
  | nil => Σb
  | (nm, ConstantDecl _) :: Σ' => firstorder_env' Σ' ((nm, fun _ => []) :: Σb) 
  | (nm, InductiveDecl mind) :: Σ' => firstorder_env' Σ' ((nm, (fun u => @firstorder_mutind Σb nm u mind)) :: Σb)
  end.                            

Definition firstorder_env Σ :=
  firstorder_env' Σ [].

Section cf.

Context {cf : config.checker_flags}.

Definition isPropositional Σ ind b := 
  match lookup_env Σ (inductive_mind ind) with
  | Some (InductiveDecl mdecl) =>
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with 
    | Some idecl =>
      match destArity [] idecl.(ind_type) with
      | Some (_, s) => is_propositional s = b
      | None => False
      end
    | None => False
    end
  | _ => False
  end.

Inductive firstorder_value Σ Γ : term -> Prop :=
| firstorder_value_C i n ui u args pandi : 
   Σ ;;; Γ |- mkApps (tConstruct i n ui) args : 
   mkApps (tInd i u) pandi ->
   Forall (firstorder_value Σ Γ) args ->
   isPropositional Σ i false ->
   firstorder_value Σ Γ (mkApps (tConstruct i n ui) args).

Lemma firstorder_value_inds :
 forall (Σ : global_env_ext) (Γ : context) (P : term -> Prop),
(forall (i : inductive) (n : nat) (ui u : Instance.t)
   (args pandi : list term),
 Σ;;; Γ |- mkApps (tConstruct i n ui) args : mkApps (tInd i u) pandi ->
 Forall (firstorder_value Σ Γ) args ->
 Forall P args ->
 isPropositional (PCUICEnvironment.fst_ctx Σ) i false ->
 P (mkApps (tConstruct i n ui) args)) ->
forall t : term, firstorder_value Σ Γ t -> P t.
Proof.
  intros ? ? ? ?. fix rec 2. intros t [ ]. eapply H; eauto.
  clear - H0 rec.
  induction H0; econstructor; eauto.
Qed.

Lemma firstorder_ind_propositional {Σ : global_env_ext} i mind oind u :
  squash (wf_ext Σ) ->
  declared_inductive Σ i mind oind ->
  @firstorder_ind Σ (firstorder_env Σ) i u ->
  isPropositional Σ i false.
Proof.
  intros Hwf d. pose proof d as [d1 d2]. intros H. red in d1. unfold firstorder_ind in H.
  red. sq.
  unfold PCUICEnvironment.fst_ctx in *. rewrite d1 in H |- *.
  solve_all.
  unfold firstorder_mutind in H0.
  rewrite d2. eapply map_nth_error with (f := @firstorder_oneind (firstorder_env Σ) (inductive_mind i) u mind) in d2.
  erewrite nth_nth_error in H0. unfold PCUICEnvironment.fst_ctx in *. rewrite d2 in H0.
  unfold firstorder_oneind in H0. solve_all.
  destruct (ind_sort oind) eqn:E2; inv H1.
  eapply PCUICInductives.declared_inductive_type in d.
  rewrite d. rewrite E2.
  now rewrite destArity_it_mkProd_or_LetIn.
Qed.

Inductive firstorder_spine Σ (Γ : context) : term -> list term -> term -> Type :=
| firstorder_spine_nil ty ty' :
    isType Σ Γ ty ->
    isType Σ Γ ty' ->
    Σ ;;; Γ ⊢ ty ≤ ty' ->
    firstorder_spine Σ Γ ty [] ty'

| firstorder_spine_cons ty hd tl na i u args B B' mind oind :
    isType Σ Γ ty ->
    isType Σ Γ (tProd na (mkApps (tInd i u) args) B) ->
    Σ ;;; Γ ⊢ ty ≤ tProd na (mkApps (tInd i u) args) B ->
    declared_inductive Σ i mind oind ->
    Σ ;;; Γ |- hd : (mkApps (tInd i u) args) ->
    @firstorder_ind Σ (@firstorder_env Σ) i u ->
    firstorder_spine Σ Γ (subst10 hd B) tl B' ->
    firstorder_spine Σ Γ ty (hd :: tl) B'.

Inductive instantiated {Σ} (Γ : context) : term -> Type :=
| instantiated_mkApps i u args : instantiated Γ (mkApps (tInd i u) args)
| instantiated_tProd na B i u args : 
  @firstorder_ind Σ (@firstorder_env Σ) i u ->
    (forall x, Σ ;;; Γ |- x : mkApps (tInd i u) args -> instantiated Γ (subst10 x B)) ->
    instantiated Γ (tProd na (mkApps (tInd i u) args) B).

Lemma typing_spine_arity_spine Σ Γ Δ args T' i u pars :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T' ->
    arity_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T'.
Proof.
  intros H. revert args pars T' H.
  induction Δ using PCUICInduction.ctx_length_rev_ind; intros args pars T' H.
  - cbn. depelim H.
    + econstructor; eauto.
    + eapply invert_cumul_ind_prod in w. eauto.
  - cbn. depelim H.
    + econstructor; eauto.
    + rewrite it_mkProd_or_LetIn_app in w, i0 |- *. cbn. destruct d as [name [body |] type]; cbn in *.
      -- todo "let". 
      -- eapply cumul_Prod_inv in w as []. econstructor.
         ++ eapply type_ws_cumul_pb. 3: eapply PCUICContextConversion.ws_cumul_pb_eq_le; symmetry. all:eauto.
            eapply isType_tProd in i0. eapply i0. 
         ++ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. autorewrite with subst.
            cbn. eapply X. len. lia.
            eapply typing_spine_strengthen. eauto.
            2:{ replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }   
            eapply substitution0_ws_cumul_pb. eauto. eauto.
            }
            replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }   
            eapply isType_subst. eapply PCUICSubstitution.subslet_ass_tip. eauto.
            (* eapply isType_ws_cumul_pb_refl.
            eapply isType_tProd in i0. eapply i0. econstructor. eapply typing_wf_local. eauto.
            eapply isType_tProd in i1. eapply i1. econstructor. eapply context_ws_cumul_pb_refl.
            todo "search". econstructor. eauto. eauto. Unshelve. all:todo "wf". *) todo "??".
            Unshelve. all:todo "".
Qed.
    
Lemma leb_spect : forall x y : nat, BoolSpecSet (x <= y) (y < x) (x <=? y).
Proof.
  intros x y. destruct (x <=? y) eqn:E;
  econstructor; destruct (Nat.leb_spec x y); lia.
Qed.

Lemma firstorder_args {Σ : global_env_ext} { mind cbody i n ui args u pandi oind} :
  wf Σ ->
  declared_constructor Σ (i, n) mind oind cbody ->
  PCUICArities.typing_spine Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi) ->
  @firstorder_ind Σ (@firstorder_env Σ) i ui ->
  firstorder_spine Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi).
Proof.
  intros Hwf Hdecl Hspine  Hind. revert Hspine.
  unshelve edestruct @declared_constructor_inv with (Hdecl := Hdecl); eauto. eapply weaken_env_prop_typing.

  (* revert Hspine. *) unfold type_of_constructor.
  erewrite cstr_eq. 2: eapply p.
  rewrite <- it_mkProd_or_LetIn_app.
  rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn. 
  rewrite PCUICSpine.subst0_it_mkProd_or_LetIn. intros Hspine.

  match goal with
   | [ |- firstorder_spine _ _ ?T _ _ ] =>
  assert (@instantiated Σ [] T) as Hi end.
  { clear Hspine. destruct Hdecl as [[d1 d3] d2]. pose proof d3 as Hdecl.
    unfold firstorder_ind in Hind. 
    rewrite d1 in Hind. solve_all. clear a.
    eapply map_nth_error in d3.
    rewrite nth_nth_error in H0.
    rewrite d3 in H0.
    unfold firstorder_oneind in H0.
    solve_all.
    eapply nth_error_all in H0. 2: eauto.
    cbn in H0. unfold firstorder_con in H0. solve_all.
    revert H0. cbn. unfold context. generalize ((subst_context (inds (inductive_mind i) ui (ind_bodies mind)) 0
    (cstr_args cbody ++ ind_params mind)%list@[ui])). clear - Hdecl.
    (* generalize conclusion to mkApps tInd args *)
    intros c. induction c using PCUICInduction.ctx_length_rev_ind.
    - unfold cstr_concl, cstr_concl_head.
      autorewrite with substu subst. rewrite !map_app. autorewrite with list.
      todo "". (* 
      rewrite PCUICInductives.subst_inds_concl_head. { cbn. eapply nth_error_Some. rewrite Hdecl. congruence. }
      econstructor. *)
    - intros Hall. eapply All_app in Hall as [Hall1 Hall2]. inv Hall2. destruct d. cbn in *.
      rewrite it_mkProd_or_LetIn_app. cbn. destruct decl_body. 
      + todo "letin".
      + cbn. unfold firstorder_type in H.
        destruct ((PCUICAstUtils.decompose_app decl_type)) eqn:E.
        * cbn in H. destruct t; inv H.
          destruct ind. eapply PCUICAstUtils.decompose_app_inv in E as E'.
          rewrite E'. econstructor.
          -- admit.
          -- intros. unfold subst10.
             rewrite PCUICLiftSubst.subst_it_mkProd_or_LetIn.
             (* stability of firstorder_type under subst *) 
             admit. }
    revert Hi Hspine.
    unfold cstr_concl, cstr_concl_head.
    autorewrite with substu subst. todo "". (* autorewrite with list.
    rewrite PCUICInductives.subst_inds_concl_head. { cbn. destruct Hdecl as [[d1 d2] d3]. eapply nth_error_Some. rewrite d2. congruence. }
    match goal with [ |- context[mkApps _ ?args]] => generalize args end. 
    intros args' Hi Spine. eapply typing_spine_arity_spine in Spine.
    revert Hi Spine.  cbn.
    remember (mkApps (tInd i u) pandi) as concl. revert args' concl Heqconcl.
    induction 3; subst. (* 
    match goal with [ |- context[it_mkProd_or_LetIn ?x ?y]] => generalize x end.

     (* generalize conclusion to mkApps tInd args *) *)
  (* eapply typing_spine_arity_spine in Hspine. *)
  revert Hi Hspine.
  generalize (type_of_constructor mind cbody (i, n) ui). *)
  (* intros t. induction 2. *)
  (* - econstructor; eauto. all:admit.
  - inv Hi.
    + econstructor; eauto. admit.
    + eapply invert_cumul_prod_ind in e. eauto.
  - todo "letin".
  - inv Hi.
    + admit.
    + econstructor. 5: cbn; eauto. all: eauto. 3: eapply ws_cumul_pb_refl. all: eauto. all: admit.       *)
    
Admitted.

Lemma firstorder_univs (Σ : global_env_ext) i n cbody ui u mind oind :
  declared_constructor Σ (i, n) mind oind cbody ->
   PCUICEquality.R_global_instance Σ.1 (eq_universe Σ) 
   (eq_universe Σ) (ConstructRef i n)
   (ind_npars mind + context_assumptions (cstr_args cbody)) ui u
-> @firstorder_ind Σ (firstorder_env Σ) i ui -> @firstorder_ind Σ (firstorder_env Σ) i u.
Proof.
  intros Hdecl Heq H. destruct Hdecl as [[Hdecl1 Hdecl2] Hdecl3]. red in Hdecl1. cbn in *.
  unfold firstorder_ind in *. unfold PCUICEnvironment.fst_ctx in *.
  rewrite Hdecl1 in H |- *.
  solve_all.

  unfold firstorder_mutind in H0.
  eapply map_nth_error in Hdecl2 as H1.
  erewrite nth_nth_error in H0. setoid_rewrite H1 in H0.
  clear H1.
  eapply map_nth_error in Hdecl2 as H1.
  erewrite nth_nth_error. setoid_rewrite H1.
  clear H1.
  
  unfold firstorder_oneind in *.
  solve_all.

  unfold firstorder_con in *.
  solve_all.
  revert H0. generalize (cstr_args x ++ ind_params mind)%list, 0.
  (* 
  rewrite !PCUICUnivSubstitutionConv.subst_instance_app in H0 |- *.
  rewrite <- !subst_context_app0 in H0 |- *.
  eapply All_app in H0 as []. eapply All_app_inv.
  - revert a0. *)
  induction l as [ | a c IH] using rev_ind.
  - econstructor.
  - rewrite !PCUICUnivSubstitutionConv.subst_instance_app. cbn.
    change ((c@[ui] ++ [a@[ui]]))%list with (app_context ([a@[ui]]) (c@[ui])).
    change ((c@[u] ++ [a@[u]]))%list with (app_context ([a@[u]]) (c@[u])). intros len.
    rewrite !PCUICLiftSubst.subst_context_app.
    unfold subst_context at 1 3. cbn. intros Hall.
    eapply All_app in Hall as []. eapply All_app_inv; eauto.
    inv a1. cbn. econstructor. 2:econstructor.
    destruct a. cbn in *.

    unfold firstorder_type in *.
    
 (*    destruct (PCUICAstUtils.decompose_app (subst (inds (inductive_mind i) u (ind_bodies mind)) len decl_type)) as [L R] eqn:ELR.
    (* eapply (f_equal (fun t : term * list term => t@[ui])) in ELR as ELR1.
     *) eapply (f_equal (fun t : term * list term => t@[u])) in ELR as ELR2.
    rewrite !PCUICUnivSubstitutionConv.subst_instance_decompose_app in ELR2.
    autorewrite with substu in ELR2.  unfold subst_instance in ELR2 at 1. unfold subst_instance_instance in ELR2.  cbn in ELR2.
    cbn in ELR.
    (* destruct (PCUICAstUtils.decompose_app (decl_type@[ui])) as [L R] eqn:ELR. *)
    erewrite PCUICSubstitution.decompose_app_subst. 2: eauto. cbn.
      destruct decl_type; cbn in *; try congruence.
    + destruct (len <=? n0) ; cbn in *; try congruence.
      destruct (nth_error (inds (inductive_mind i) ui (ind_bodies mind))  (n0 - len)) eqn:E; cbn in *; try congruence.
      eapply PCUICInductiveInversion.inds_nth_error in E as E'; destruct E' as [m ->]. cbn in H2.
      eapply nth_error_Some_length in E.
      rewrite inds_length in E.
      erewrite <- inds_length in E.
      eapply nth_error_Some' in E as [k E].
      setoid_rewrite E. 
      eapply PCUICInductiveInversion.inds_nth_error in E as E'; destruct E' as [m' ->]. cbn in *.
      destruct plookup_env as [f | ] eqn:Eenv; try congruence.
      admit.
    + admit.
      cbn in *.
      subst.
      unfold inds in *.
      destruct (nth_error (inds (inductive_mind i) u (ind_bodies mind)) (n0 - len)); cbn in *; try congruence.
    

    

  rewrite subst_context_app.
  autorewrite with subst.

  eapply All_nth_error in H0. 2: eauto. *)
Admitted.

  
Lemma firstorder_value_spec Σ t i u args mind :
  wf_ext Σ -> wf_local Σ [] ->
   Σ ;;; [] |- t : mkApps (tInd i u) args -> 
   PCUICWcbvEval.value t -> 
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i u ->
  firstorder_value Σ [] t.
Proof.
  intros Hwf Hwfl Hty Hvalue.
  revert mind i u args Hty.
  induction Hvalue as [ t Hvalue | t args' Hhead Hargs IH | t args' Hargs IH Hstuck ] using PCUICWcbvEval.value_values_ind; 
   intros mind i u args Hty Hlookup Hfo.
  - destruct t; inversion_clear Hvalue.
    + exfalso. eapply inversion_Sort in Hty as (? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_ind in Hcumul.
    + exfalso. eapply inversion_Prod in Hty as (? & ? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_ind in Hcumul.
    + exfalso. eapply inversion_Lambda in Hty as (? & ? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_prod_ind in Hcumul.
    + exfalso. eapply inversion_Ind in Hty as (? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICInductives.declared_inductive_type in d.
      rewrite d in w.
      destruct (ind_params x ,,, ind_indices x0) as [ | [? [] ?] ? _] using rev_ind.
      * cbn in w. now eapply invert_cumul_sort_ind in w.
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w. todo "letin".
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w. 
        now eapply invert_cumul_prod_ind in w.
    + eapply inversion_Construct in Hty as Hty'; eauto.
      destruct Hty' as (? & ? & ? & ? & ? & ? & ?).
      assert (ind = i) as ->. {
         eapply PCUICInductiveInversion.Construct_Ind_ind_eq with (args0 := []); eauto.
      }
      eapply firstorder_value_C with (args := []); eauto.
      eapply firstorder_ind_propositional; eauto. sq. eauto.      
      now eapply (declared_constructor_inductive (ind := (i, _))).
    + exfalso. eapply invert_fix_ind with (args0 := []) in Hty as [].
      destruct unfold_fix as [ [] | ]; auto. eapply nth_error_nil.
    + exfalso. eapply (typing_cofix_coind (args := [])) in Hty. red in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      rewrite Hlookup in Hfo.
      eapply andb_true_iff in Hfo as [Hfo _].
      eapply check_recursivity_kind_inj in Hty; eauto. congruence.
  - destruct t; inv Hhead.
    + exfalso. now eapply invert_ind_ind in Hty.
    + apply inversion_mkApps in Hty as H; auto.
      destruct H as (?&typ_ctor& spine).
      apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
      pose proof d as [[d' _] _]. red in d'. cbn in *. unfold PCUICEnvironment.fst_ctx in *.
      eapply PCUICInductiveInversion.Construct_Ind_ind_eq with (mdecl := x0) in Hty as Hty'; eauto.
      destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
      econstructor; eauto.
      2:{ eapply firstorder_ind_propositional; sq; eauto. eapply declared_constructor_inductive in d. eauto. }
      eapply PCUICSpine.typing_spine_strengthen in spine. 3: eauto. 
      2: eapply PCUICInductiveInversion.declared_constructor_valid_ty; eauto.

      eapply firstorder_args in spine; eauto.
      2:{ eapply R_global_instance_cstr_irrelevant in r. 2: eauto. now eapply firstorder_univs; eauto. }
         
      clear c0 c1 e0 w Hty.
      induction spine.
      * econstructor.
      * destruct d as [d1 d2]. inv IH.
        econstructor. 2:eapply IHspine; eauto. 2: now inv Hargs.
        eapply H; eauto. eapply d0.
    + exfalso. eapply (typing_cofix_coind (args := args')) in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      rewrite Hlookup in Hfo.
      eapply andb_true_iff in Hfo as [Hfo _].
      eapply check_recursivity_kind_inj in Hty; eauto. congruence.
  - exfalso. destruct t; inversion Hstuck as [Hstuck'].
    destruct PCUICWcbvEval.cunfold_fix as [[] | ] eqn:E; inversion Hstuck'.
    eapply invert_fix_ind in Hty. auto.
    unfold unfold_fix. unfold PCUICWcbvEval.cunfold_fix in E.
    destruct (nth_error mfix idx); auto.
    inversion E; subst; clear E.
    eapply nth_error_None. now eapply leb_complete.
Qed.

End cf.