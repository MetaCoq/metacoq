(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool Utf8.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From Coq Require Import Bool String List Program.
From MetaCoq.Template Require Import config monad_utils utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICArities PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeLemmata PCUICSubstitution PCUICValidity
     PCUICGeneration PCUICInversion PCUICValidity PCUICInductives PCUICInductiveInversion
     PCUICSpine PCUICSR PCUICCumulativity PCUICConversion PCUICConfluence PCUICArities
     PCUICWeakeningEnv PCUICContexts PCUICContextConversion PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICSafeLemmata.

From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeReduce.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MonadNotation.

Hint Constructors assumption_context : pcuic.

Derive NoConfusion for type_error.

Set Equations With UIP.
Set Equations Transparent.

Add Search Blacklist "_graph_mut".

Add Search Blacklist "obligation".

Require Import ssreflect.

Definition well_sorted {cf:checker_flags} Σ Γ T := 
  ∥ ∑ s, Σ ;;; Γ |- T : tSort s ∥.

Lemma well_sorted_well_typed {cf:checker_flags} {Σ Γ T} : well_sorted Σ Γ T -> welltyped Σ Γ T.
Proof.
  intros [[s Hs]]. now exists (tSort s).
Qed.

Coercion well_sorted_well_typed : well_sorted >-> welltyped.

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ inst Δ s} :
  wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ Γ inst s (smash_context [] Δ) ->
  ∑ s', spine_subst Σ Γ inst s' Δ.
Proof.
  intros wf.
  move/spine_subst_ctx_inst.
  intros c. eapply ctx_inst_smash in c.
  unshelve epose proof (ctx_inst_spine_subst _ c); auto.
  now eexists.
Qed.

(** Smashed variant that is easier to use *)
Lemma inductive_cumulative_indices_smash {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) napp u u' ->
  forall Γ pars pars',
  spine_subst Σ Γ pars (List.rev pars) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ pars' (List.rev pars') (smash_context [] (subst_instance u' (ind_params mdecl))) ->  
  equality_terms Σ Γ pars pars' ->
  let indctx := idecl.(ind_indices)@[u] in
  let indctx' := idecl.(ind_indices)@[u'] in
  let pindctx := subst_context_let_expand (List.rev pars) (ind_params mdecl)@[u] (smash_context [] indctx) in
  let pindctx' := subst_context_let_expand (List.rev pars') (ind_params mdecl)@[u'] (smash_context [] indctx') in
  context_equality_rel true Σ Γ pindctx pindctx'.
Proof.
  intros ind mdecl idecl u u' napp isdecl up cu cu' hR Γ pars pars' sppars sppars' eq.
  unshelve epose proof (spine_subst_smash_inv _ sppars) as [parsubst sppars2].
  eapply PCUICWeakening.weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu).
  unshelve epose proof (spine_subst_smash_inv _ sppars') as [parsubst' sppars3].
  eapply PCUICWeakening.weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu').
  epose proof (inductive_cumulative_indices isdecl up cu cu' hR Γ pars pars' _ _ sppars2 sppars3 eq).
  intros.
  cbn in X.
  rewrite (spine_subst_inst_subst sppars2) in X.
  rewrite (spine_subst_inst_subst sppars3) in X.
  rewrite /pindctx /pindctx'.
  rewrite - !smash_context_subst_context_let_expand.
  apply X.
Qed.

(** * Retyping

  The [infer] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Definition principal_type {cf:checker_flags} Σ Γ t := 
  { T : term | ∥ (Σ ;;; Γ |- t : T) * (forall T', Σ ;;; Γ |- t : T' -> Σ ;;; Γ ⊢ T ≤ T') ∥ }.
Definition principal_sort {cf:checker_flags} Σ Γ T := 
  { s : Universe.t | ∥ (Σ ;;; Γ |- T : tSort s) * (forall s', Σ ;;; Γ |- T : tSort s' -> leq_universe Σ s s') ∥ }.

Definition principal_typed_type {cf:checker_flags} {Σ Γ t} (wt : principal_type Σ Γ t) := proj1_sig wt.
Definition principal_sort_sort {cf:checker_flags} Σ Γ T (ps : principal_sort Σ Γ T) : Universe.t := proj1_sig ps.
Coercion principal_typed_type : principal_type >-> term.
Coercion principal_sort_sort : principal_sort >-> Universe.t.

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Lemma typing_welltyped Γ t T : Σ ;;; Γ |- t : T -> welltyped Σ Γ T.
  Proof.
    intros H.
    destruct hΣ. destruct Hφ.
    apply validity in H; auto. destruct H as [s tyT].
    econstructor; eauto.
  Qed.
End TypeOf.

Definition on_subterm P Pty Γ t : Type := 
  match t with
  | tProd na t b => Pty Γ t * Pty (Γ ,, vass na t) b
  | tLetIn na d t t' => 
    Pty Γ t * P Γ d * P (Γ ,, vdef na d t) t'
  | tLambda na t b => Pty Γ t * P (Γ ,, vass na t) b
  | _ => True
  end.

Lemma welltyped_subterm {cf:checker_flags} {Σ : global_env_ext} (wfΣ : ∥ wf Σ ∥) {Γ t} :
  welltyped Σ Γ t -> on_subterm (welltyped Σ) (well_sorted Σ) Γ t.
Proof.
  destruct t; simpl; auto; intros [T HT]; sq.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto; split; try econstructor; eauto.
  eapply inversion_Lambda in HT as (? & ? & ? & ? & ?); auto; split; try econstructor; eauto.
  eapply inversion_LetIn in HT as (? & ? & ? & ? & ? & ?); auto; split; [split|]; try econstructor; eauto.
Qed.

Lemma on_free_vars_ind_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl → 
  on_free_vars_ctx (closedP (context_assumptions (ind_params mdecl)) xpredT) 
    (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli.
  rewrite <- closedn_ctx_on_free_vars.
  eapply PCUICClosed.closed_ind_predicate_context; tea.
  eapply (PCUICClosed.declared_minductive_closed decli).
Qed.

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).

  Local Notation ret t := (exist t _).

  Section SortOf.
    Obligation Tactic := idtac.
    Program Definition infer_as_sort {Γ t} (wf : well_sorted Σ Γ t)
      (tx : principal_type Σ Γ t) : principal_sort Σ Γ t :=
      match @reduce_to_sort cf Σ hΣ Γ tx _ with
      | Checked (u ; _) => u
      | TypeError e => !
      end.
      
    Next Obligation. intros Γ t [[s Hs]] [ty [[Hty Hp]]]; simpl.
      eapply typing_welltyped; eauto. Defined.
    Next Obligation. intros Γ t ws [s [[Hs Hp]]]. simpl in *.
      unfold infer_as_sort_obligation_1.
      destruct ws as [[s' Hs']]. 
      specialize (Hp _ Hs') as s'cum.
      eapply equality_Sort_r_inv in s'cum as [u' [redu' leq]].
      destruct reduce_to_sort => //.
      intros u wc [= <-].
      sq.
      split.
      - eapply type_reduction in Hs. 2:exact wc. assumption.
      - intros ? typ.
        specialize (Hp _ typ).
        eapply equality_red_l_inv in Hp. 2:exact wc.
        now apply equality_Sort_inv in Hp.
    Qed.
    Next Obligation.
      simpl. intros.
      pose proof (reduce_to_sort_complete hΣ _ (eq_sym Heq_anonymous)).
      clear Heq_anonymous.
      destruct tx as (?&[(?&?)]).
      destruct wf as [(?&?)].
      apply e0 in t1.
      eapply equality_Sort_r_inv in t1 as (?&r&_).
      eapply H, r.
    Qed.
  End SortOf.

  Program Definition infer_as_prod Γ T
    (wf : welltyped Σ Γ T)
    (isprod : ∥ ∑ na A B, Σ ;;; Γ ⊢ T ≤ tProd na A B ∥) : 
    ∑ na' A' B', ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥ :=
    match @reduce_to_prod cf Σ hΣ Γ T wf with
    | Checked p => p
    | TypeError e => !
    end.
    Next Obligation.
      destruct isprod as [(?&?&?&cum)].
      destruct hΣ.
      apply equality_Prod_r_inv in cum as cum'; auto;
        destruct cum' as (?&?&?&[]).
      symmetry in Heq_anonymous.
      eapply reduce_to_prod_complete in Heq_anonymous => //. exact c.
    Qed.

  Equations lookup_ind_decl ind : typing_result
        ({decl & {body & declared_inductive (fst Σ) ind decl body}}) :=
  lookup_ind_decl ind with inspect (lookup_env (fst Σ) ind.(inductive_mind)) :=
    { | exist (Some (InductiveDecl decl)) look with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) :=
      { | exist (Some body) eqnth => Checked (decl; body; _);
        | ret None => raise (UndeclaredInductive ind) };
      | _ => raise (UndeclaredInductive ind) }.
  Next Obligation.
    split.
    - symmetry in look.
      etransitivity. eassumption. reflexivity.
    - now symmetry.
  Defined.

  Lemma lookup_ind_decl_complete ind e : lookup_ind_decl ind = TypeError e -> 
    ((∑ mdecl idecl, declared_inductive Σ ind mdecl idecl) -> False).
  Proof.
    apply_funelim (lookup_ind_decl ind).
    1-2:intros * _ her [mdecl [idecl [declm decli]]];
    red in declm; rewrite declm in e0; congruence.
    1-2:intros * _ _ => // => _ [mdecl [idecl [declm /= decli]]].
    red in declm. rewrite declm in e1. noconf e1.
    congruence.
  Qed.
  
  Obligation Tactic := idtac.

  Equations? infer (Γ : context) (t : term) (wt : welltyped Σ Γ t) : principal_type Σ Γ t 
    by struct t :=
  { infer Γ (tRel n) wt with 
    inspect (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) := 
    { | ret None => !;
      | ret (Some t) => ret t };
    
    infer Γ (tVar n) wt := !;
    infer Γ (tEvar ev args) wt := !;

    infer Γ (tSort s) _ := ret (tSort (Universe.super s));

    infer Γ (tProd n ty b) wt :=
      let ty1 := infer Γ ty (welltyped_subterm hΣ wt).1 in
      let s1 := infer_as_sort (welltyped_subterm hΣ wt).1 ty1 in
      let ty2 := infer (Γ ,, vass n ty) b (welltyped_subterm hΣ wt).2 in
      let s2 := infer_as_sort (welltyped_subterm hΣ wt).2 ty2 in
      ret (tSort (Universe.sort_of_product s1 s2));

    infer Γ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) b (welltyped_subterm hΣ wt).2 in
      ret (tProd n t t2);

    infer Γ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) b' (welltyped_subterm hΣ wt).2 in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ (tApp t a) wt :=
      let ty := infer Γ t _ in
      let pi := infer_as_prod Γ ty _ _ in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ (tConst cst u) wt with inspect (lookup_env (fst Σ) cst) :=
      { | ret (Some (ConstantDecl d)) := ret (subst_instance u d.(cst_type));
        |  _ := ! };

    infer Γ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked decl) := ret (subst_instance u decl.π2.π1.(ind_type));
        | ret (TypeError e) := ! };
    
    infer Γ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_ctors) k) := 
        { | ret (Some cdecl) => ret (type_of_constructor d.π1 cdecl (ind, k) u);
          | ret None => ! };
      | ret (TypeError e) => ! };

    infer Γ (tCase ci p c brs) wt with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
      { | ret (Checked indargs) =>
          let ptm := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
          ret (mkApps ptm (List.skipn ci.(ci_npar) indargs.π2.π2.π1 ++ [c]));
        | ret (TypeError _) => ! };

    infer Γ (tProj (ind, n, k) c) wt with inspect (@lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_projs) k) :=
        { | ret (Some pdecl) with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
          { | ret (Checked indargs) => 
              let ty := snd pdecl in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance indargs.π2.π1 ty));
            | ret (TypeError _) => ! };
         | ret None => ! };
        | ret (TypeError e) => ! };

    infer Γ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! };

    infer Γ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! };

    infer Γ (tPrim p) wt := !
  }.
  Proof.
    all:try clear infer.
    all:destruct hΣ, Hφ; destruct wt as [T HT].
    all:try solve [econstructor; eauto].

    - sq. destruct (nth_error Γ n) eqn:hnth => //.
      eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in hnth; noconf hnth. noconf wildcard0.
      split; [now constructor|].
      intros T' Ht'.
      eapply inversion_Rel in Ht' as (? & ? & ? & ?); auto.
      now rewrite e in e1; noconf e1.
      
    - eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in wildcard => //.
     
    - depind HT. eapply IHHT1; eauto.

    - depind HT; eapply IHHT1; eauto.

    - eapply inversion_Sort in HT as (wfΓ & wf & cum); auto.
      sq.
      split. econstructor; eauto.
      intros T' (wfΓ'' & wf' & cum')%inversion_Sort; auto.
            
    (*- eapply inversion_Prod in HT as (? & ? & ? & ? & ?); try econstructor; eauto.

    - destruct hΣ. destruct Hφ. destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?); try econstructor; eauto.*)

    - simpl in *.
      destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?).
      subst ty1 s1.
      destruct infer_as_sort as [x1 [[Hx1 Hx1p]]]; simpl.
      destruct infer_as_sort as [x2 [[Hx2 Hx2p]]]; simpl.
      subst s2; simpl in *. sq.
      split.
      * specialize (Hx1p _ t0).
        specialize (Hx2p _ t).
        econstructor; eauto.
      * intros T' Ht'.
        eapply inversion_Prod in Ht' as (? & ? & ? & ? & ?); auto.
        etransitivity; eauto. constructor; fvs. constructor.
        eapply leq_universe_product_mon; eauto.

    - simpl in t2. destruct (inversion_Lambda Σ w HT) as (? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst t2; simpl in *.
      sq. split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ?)%inversion_Lambda; auto.
        specialize (pbty _ t3).
        transitivity (tProd n t x2); eauto.
        eapply equality_Prod; auto.
        now eapply wt_equality_refl.

    - simpl in b'_ty.
      destruct (inversion_LetIn Σ w HT) as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst b'_ty; simpl in *.
      sq; split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_LetIn; auto.
        etransitivity; eauto.
        eapply equality_LetIn_bo; eauto.

    - eapply inversion_App in HT as (? & ? & ? & ? & ?); try econstructor; eauto.

    - simpl in ty. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst ty; simpl in *.
      apply wat_welltyped; auto.
      sq.
      eapply validity; eauto.
    - simpl in ty. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst ty; simpl in *.
      sq. exists x, x0, x1. now eapply pbty.
      
    - simpl in *. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [tty [[Htty pbty]]]; subst ty; simpl in *.
      destruct pi as [na' [A' [B' [red]]]].
      sq. split.
      * simpl.
        eapply type_reduction in Htty; eauto.
        assert (Σ ;;; Γ ⊢ tProd na' A' B' ≤ tProd x x0 x1).
        { eapply equality_red_l_inv; eauto. exact red. }
        eapply equality_Prod_Prod_inv in X as [eqna Ha Hb]; auto.
        specialize (pbty _ t0).
        eapply type_App'.
        2:{ eapply (type_equality (le:=false)); eauto. 2:now symmetry.
            eapply validity in Htty; auto.
            eapply isType_red in Htty. 2:exact red.
            eapply isType_tProd in Htty; pcuic. }
        eapply type_reduction in Htty.
        2:exact red. exact Htty.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_App; auto.
        specialize (pbty _ t2). simpl.
        etransitivity; [|eassumption].
        assert (Σ ;;; Γ ⊢ tProd na' A' B' ≤ tProd x2 x3 x4).
        { eapply equality_red_l_inv; eauto. exact red. }
        eapply equality_Prod_Prod_inv in X as [eqann Ha Hb]; auto.
        eapply (substitution0_equality); eauto.

    - eapply inversion_Const in HT as [decl ?] => //.
      intuition auto. rewrite a0 in wildcard. noconf wildcard.
      sq. split.
      * constructor; eauto.
      * intros T' [decl [wf [lookup [cu cum]]]]%inversion_Const; auto.
        red in lookup. congruence.
    - apply inversion_Const in HT as [decl [wf [lookup [cu cum]]]]; auto.
      red in lookup. subst wildcard0. rewrite lookup in e. congruence.
    - apply inversion_Const in HT as [decl [wf [lookup [cu cum]]]]; auto.
      red in lookup. subst wildcard0. rewrite lookup in e. congruence.

    - destruct decl as [decl [body decli]].
      eapply inversion_Ind in HT; auto.
      dependent elimination HT as [(mdecl; idecl; (wf'', (decli', (rest, cum))))].
      pose proof (declared_inductive_inj decli decli') as [-> ->].
      sq. split.
      * econstructor; eauto.
      * intros T' HT'.
        eapply inversion_Ind in HT'; auto.
        dependent elimination HT' as [(mdecl'; idecl'; (wf''', (decli'', (rest', cum'))))].
        simpl.
        now destruct (declared_inductive_inj decli decli'') as [-> ->].
    - eapply inversion_Ind in HT; auto.
      dependent elimination HT as [(mdecl; idecl; (wf'', (decli', (rest, cum))))].
      move: wildcard0. destruct decli' as [look hnth].
      move=> looki.
      eapply lookup_ind_decl_complete. now symmetry.
      exists mdecl, idecl. split; auto.

    - destruct d as [decl [body decli]].
      assert (declared_constructor Σ (ind, k) decl body cdecl) as declc.
      { red; intuition auto. }
      eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl; (wf'', (declc', (rest, cum))))].
      pose proof (declared_constructor_inj declc declc') as [-> [-> ->]].
      sq. split.
      * econstructor; eauto.
      * intros T' HT'.
        eapply inversion_Construct in HT'; auto.
        dependent elimination HT' as [(mdecl'; idecl'; cdecl'; (wf''', (declc'', (rest', cum'))))].
        simpl.
        now destruct (declared_constructor_inj declc declc'') as [-> [-> ->]].
    - eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl'; (wf'', (declc'', (rest, cum))))].
      destruct declc''.
      destruct d as [decl [body decli]].
      pose proof (declared_inductive_inj decli H0) as [-> ->]. simpl in *. congruence.
    
    - symmetry in wildcard2.
      eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl; (wf'', (declc', (rest, cum))))].
      eapply lookup_ind_decl_complete in wildcard2; eauto.
      now destruct declc'.
    
    - eapply inversion_Case in HT; auto.
      destruct HT as (mdecl & idecl & isdecl & indices & [] & cum).
      eexists; eauto.
    - cbn. 
      destruct inversion_Case as (mdecl & idecl & isdecl & indices & data & cum).
      destruct infer as [cty [[Hty Hp]]]. simpl.
      eapply validity in Hty.
      eapply wat_welltyped; auto. sq; auto.
    - cbn -[reduce_to_ind] in *.
      destruct inversion_Case as (mdecl & idecl & isdecl & indices & data & cum).
      destruct infer as [cty [[Hty Hp]]].
      destruct reduce_to_ind => //.
      injection wildcard. intros ->. clear wildcard.
      destruct a as [i [u' [l [red]]]].
      simpl in *.
      eapply type_reduction in Hty. 2:exact red.
      destruct data.
      pose proof (Hp _ scrut_ty).
      assert (Σ ;;; Γ ⊢ mkApps (tInd i u') l ≤ mkApps (tInd ci (puinst p)) (pparams p ++ indices)).
      { eapply equality_red_l_inv; eauto. exact red. }
      eapply equality_Ind_inv in X0 as [eqi Ru cl]; auto. subst i.
      assert (conv_indices : All2 (fun x y : term => Σ;;; Γ ⊢ x = y) (indices ++ [c])
        (skipn (ci_npar ci) l ++ [c])).
      { eapply All2_app. 2:now eapply All2_tip, wt_equality_refl.
        eapply (All2_skipn _ _ _ _ _ (ci_npar ci)) in a.
        symmetry in a. rewrite skipn_all_app_eq in a.
        now rewrite (wf_predicate_length_pars wf_pred).
        exact a. }
      pose proof (validity scrut_ty).
      have clpars : forallb (is_open_term Γ) (pparams p).
      { eapply isType_open in X0.
        rewrite on_free_vars_mkApps forallb_app in X0.
        now move/andP: X0 => [] _ /andP[]. }
      have clpctx : on_free_vars_ctx (shiftnP (context_assumptions (ind_params mdecl)) xpred0) (pcontext p).
      { symmetry in conv_pctx.
        eapply All2_fold_All2 in conv_pctx.
        unshelve epose proof (eq_context_upto_names_on_free_vars _ _ _ _ conv_pctx); [shelve|..].
        eapply on_free_vars_ind_predicate_context; tea.
        now rewrite -PCUICConfluence.closedP_shiftnP. }
      have cli : is_closed_context (Γ ,,, inst_case_predicate_context p).
      { rewrite on_free_vars_ctx_app cl /=.
        eapply on_free_vars_ctx_inst_case_context; trea.
        rewrite test_context_k_closed_on_free_vars_ctx.
        rewrite (wf_predicate_length_pars wf_pred).
        rewrite (PCUICClosed.declared_minductive_ind_npars isdecl).
        now rewrite PCUICConfluence.closedP_shiftnP. }
      have eqctx : All2 (PCUICEquality.compare_decls eq eq) (Γ ,,, inst_case_predicate_context p) 
        (Γ ,,, case_predicate_context ci mdecl idecl p).
      { eapply All2_app. 2:reflexivity.
        symmetry; eapply All2_fold_All2; eapply PCUICAlpha.inst_case_predicate_context_eq; tea.
        eapply All2_fold_All2. now symmetry. }
      have convctx : Σ ⊢ Γ,,, predctx = Γ,,, inst_case_predicate_context p.
      { eapply eq_context_upto_context_equality => //. fvs.
        eapply All2_fold_All2. rewrite /predctx. symmetry. eapply All2_impl; tea.
        intros ?? []; constructor; subst; auto; try reflexivity. }
      assert (Σ ;;; Γ |- it_mkLambda_or_LetIn (inst_case_predicate_context p) (preturn p) : 
        it_mkProd_or_LetIn (inst_case_predicate_context p) (tSort ps)).
      { eapply type_it_mkLambda_or_LetIn.
        eapply closed_context_conversion; tea.
        eapply wf_local_alpha. symmetry; tea.
        eapply wf_case_predicate_context; tea. }
      sq; split; simpl.
      * destruct (isType_mkApps_Ind_smash isdecl X0) as [sppars [spargs cu']].
        now eapply wf_predicate_length_pars.
        have lenidx : #|indices| = context_assumptions (ind_indices idecl).
        { pose proof (PCUICContextSubst.context_subst_length spargs). len in H. }
        have lenpars : #|pparams p| = context_assumptions (ind_params mdecl).
        { pose proof (PCUICContextSubst.context_subst_length sppars). len in H. }
        have lenskip : #|skipn (ci_npar ci) l| = context_assumptions (ind_indices idecl).
        { eapply All2_length in conv_indices.
          cbn in conv_indices. len in conv_indices.
          have ->: #|skipn (ci_npar ci) l| = #|indices| by lia.
          pose proof (PCUICContextSubst.context_subst_length spargs). len in H. }
        have lenfirst : #|firstn (ci_npar ci) l| = context_assumptions (ind_params mdecl).
        { eapply All2_length in a.
          len in a. rewrite -(firstn_skipn (ci_npar ci) l) in a.
          rewrite app_length in a. rewrite lenskip in a.
          rewrite lenidx in a. lia. }
        have sp : ∑ inst, spine_subst Σ Γ (pparams p ++ skipn (ci_npar ci) l) 
          inst (ind_params mdecl,,, ind_indices idecl)@[puinst p].
        { eapply validity in Hty.
          rewrite -(firstn_skipn (ci_npar ci) l) in Hty.
          have eqci := !! (PCUICClosed.declared_minductive_ind_npars isdecl).
          rewrite eq_npars in eqci.          
          eapply (isType_mkApps_Ind_smash isdecl) in Hty as [sppars' [spargs' cu'']].
          2:{ congruence. }
          apply (spine_subst_smash_inv (Γ := Γ) (inst:=pparams p ++ skipn (ci_npar ci) l)
            (Δ := (ind_params mdecl ,,, ind_indices idecl)@[puinst p])
            (s := List.rev (pparams p ++ skipn (ci_npar ci) l))).
          { eapply PCUICWeakening.weaken_wf_local; tea. pcuic.
            eapply on_minductive_wf_params_indices_inst; tea. }
          { rewrite PCUICUnivSubstitution.subst_instance_app_ctx smash_context_app_expand.
            rewrite List.rev_app_distr. eapply spine_subst_app.
            * len. 
            * eapply wf_local_expand_lets, wf_local_smash_end.
              rewrite -app_context_assoc -PCUICUnivSubstitution.subst_instance_app_ctx.
              eapply PCUICWeakening.weaken_wf_local => //. pcuic.
              eapply on_minductive_wf_params_indices_inst; tea.
            * len.
              rewrite skipn_all_app_eq. len. apply sppars.
            * len.
              rewrite skipn_all_app_eq. len.
              rewrite (firstn_app_left _ 0). len.
              rewrite firstn_0 // app_nil_r.
              eapply spine_subst_cumul. 6:exact spargs'.
              eapply smash_context_assumption_context; auto. constructor.
              rewrite expand_lets_smash_context -(PCUICClosed.smash_context_subst []).
              eapply smash_context_assumption_context; auto. constructor.
              apply spargs'. rewrite smash_context_subst_context_let_expand in spargs.
              apply spargs.
              rewrite smash_context_subst_context_let_expand.
              epose proof (inductive_cumulative_indices_smash isdecl) as cumi.
              forward cumi. apply (weaken_lookup_on_global_env' _ _ _ _ (proj1 isdecl)).
              specialize (cumi cu'' cons Ru).
              specialize (cumi _ _ _ sppars' sppars).
              rewrite -(firstn_skipn (ci_npar ci) l) in a.
              eapply All2_app_inv in a as [eqpars eqidx]. 2:len.
              exact (cumi eqpars). } }
        have typec' : Σ ;;; Γ |- c : mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) l).
        { have tyr : isType Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) l)).
          { destruct sp as [inst' sp].
            eexists. eapply isType_mkApps_Ind; tea. }
          eapply (type_equality (le:=true)); tea.
          transitivity (mkApps (tInd ci (puinst p)) l).
          constructor. fvs. fvs.
          rewrite on_free_vars_mkApps /=. fvs.
          eapply PCUICEquality.eq_term_upto_univ_mkApps.
          now constructor. reflexivity.
          eapply equality_eq_le.
          eapply equality_mkApps.
          eapply equality_refl; fvs.
          rewrite -{1}(firstn_skipn (ci_npar ci) l) in a.
          rewrite -{1}(firstn_skipn (ci_npar ci) l).
          eapply All2_app_inv in a as []. 2:len.
          eapply All2_app => //.
          eapply equality_terms_refl. fvs.
          fvs. }
        eapply meta_conv.
        econstructor. 10:tea. all:tea.
        destruct sp as [inst sp].
        apply (spine_subst_ctx_inst sp).
        now rewrite /ptm -(PCUICCasesContexts.inst_case_predicate_context_eq conv_pctx).
      * intros T'' Hc'.
        eapply inversion_Case in Hc' as (mdecl' & idecl' & isdecl' & indices' & [] & cum'); auto.
        etransitivity. simpl in cum'. 2:eassumption.
        eapply equality_eq_le, equality_mkApps; auto.
        destruct (declared_inductive_inj isdecl isdecl'). subst mdecl' idecl'.
        rewrite /ptm. symmetry.
        eapply equality_it_mkLambda_or_LetIn => //.
        eapply wt_equality_refl; tea.

        eapply All2_app. 2:eapply All2_tip.
        specialize (Hp _ scrut_ty0).
        assert (Σ ;;; Γ ⊢ mkApps (tInd ci u') l ≤ mkApps (tInd ci (puinst p)) 
                                                             (pparams p ++ indices')).
        { eapply equality_red_l_inv; eauto. exact red. }
        eapply equality_Ind_inv in X2 as [eqi' Ru' cl' e]; auto.
        eapply All2_skipn in e. instantiate (1 := ci_npar ci) in e.
        rewrite skipn_all_app_eq // in e.
        now rewrite (wf_predicate_length_pars wf_pred).
        eapply wt_equality_refl; tea.
      
    - cbn in wildcard1.
      destruct inversion_Case as (mdecl & idecl & isdecl & indices & [] & cum).
      destruct infer as [cty [[Hty Hp]]].
      destruct validity as [Hi i]. simpl in wildcard1.
      specialize (Hp _ scrut_ty).
      eapply equality_Ind_r_inv in Hp as [ui' [l' [red Ru ca]]]; auto.
      symmetry in wildcard1; 
      eapply reduce_to_ind_complete in wildcard1 => //.
      exact red.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      simpl in cum.
      eexists; eauto.
    - simpl; destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      eapply validity in Hc'; auto.
      eapply wat_welltyped; auto. sq; auto.
    - simpl in *. destruct inversion_Proj as (u & mdecl & idecl & cdecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      destruct reduce_to_ind => //. injection wildcard1. intros ->.
      clear wildcard1.
      destruct a as [i [u' [l [red]]]]. simpl.
      simpl in red.
      eapply type_reduction in Hc'; eauto.
      pose proof (Hc'' _ Hc).
      assert (Σ ;;; Γ ⊢ mkApps (tInd i u') l ≤ mkApps (tInd ind u) args).
      { eapply equality_red_l_inv; eauto. exact red. }
      eapply equality_Ind_inv in X0 as [eqi' Ru' cl' e]; eauto.
      destruct d as [decl [body decli]].
      pose proof (declared_inductive_inj (proj1 declp) decli) as [-> ->].
      assert (declared_projection Σ (ind, n, k) mdecl idecl cdecl pdecl).
      { red; intuition eauto. simpl. eapply declp. cbn. apply declp. }
      subst ind.
      destruct (declared_projection_inj declp H) as [_ [_ [_ ->]]].
      sq. split; auto.
      * econstructor; eauto. cbn. eapply type_reduction; tea. exact red.
        now rewrite (All2_length e).
      * intros.
        eapply inversion_Proj in X0 as (u'' & mdecl' & cdecl' & idecl' & pdecl'' & args' & 
            declp' & Hc''' & Hargs' & cum'); auto.
        simpl in *. subst ty.
        destruct (declared_projection_inj H declp') as [<- [<- [<- ->]]].
        etransitivity; eauto.
        specialize (Hc'' _ Hc''').
        assert (Σ ;;; Γ ⊢ mkApps (tInd i u') l ≤ mkApps (tInd i u'') args').
        { eapply equality_red_l_inv; eauto. exact red. }
        eapply equality_Ind_inv in X0 as [eqi'' Ru'' cl'']; auto.
        eapply type_reduction in Hc'; tea. 2:exact red.
        assert (consistent_instance_ext Σ (ind_universes mdecl) u').
        { eapply validity in Hc'; eauto.
          destruct Hc' as [s Hs].
          eapply PCUICInductives.invert_type_mkApps_ind in Hs as []; tea. }
        assert (consistent_instance_ext Σ (ind_universes mdecl) u'').
          { eapply validity in Hc'''; eauto.
            destruct Hc''' as [s Hs]; auto.
            eapply invert_type_mkApps_ind in Hs as []; tea. }
        transitivity (subst0 (c :: List.rev l) (subst_instance u'' pdecl''.2)); cycle 1.
        eapply equality_eq_le.
        
        have clu'': is_closed_context (Γ,,, projection_context i mdecl idecl u'').
        eapply wf_local_closed_context.
        eapply PCUICWeakening.weaken_wf_local; tea. pcuic.
        eapply (wf_projection_context _ (p:= (i, n, k))); eauto.
        have clu': is_closed_context (Γ,,, projection_context i mdecl idecl u').
        eapply wf_local_closed_context.
        eapply PCUICWeakening.weaken_wf_local; tea. pcuic.
        eapply (wf_projection_context _ (p:= (i, n, k))); eauto.

        eapply (substitution_equality_subst_conv (Γ0 := projection_context i mdecl idecl u')
        (Γ1 := projection_context i mdecl idecl u'') (Δ := [])); auto.
        eapply subslet_untyped_subslet.
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        eapply subslet_untyped_subslet.
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        constructor; auto. now eapply wt_equality_refl.
        now apply All2_rev.
        pose proof (PCUICClosed.declared_projection_closed w declp').
        eapply equality_refl => //.
        { eapply PCUICWeakeningEnv.on_declared_projection in declp; eauto.
          rewrite closedn_on_free_vars //.
          len. 
          rewrite -(PCUICClosed.declared_minductive_ind_npars H) /=.
          rewrite PCUICClosed.closedn_subst_instance.
          eapply closed_upwards; tea. lia. }
        eapply (substitution_equality (Γ' := projection_context i mdecl idecl u') (Γ'' := [])); auto.
        cbn -[projection_context].
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        rewrite -(All2_length a) in Hargs'. rewrite Hargs' in Ru''.
        unshelve epose proof (projection_cumulative_indices declp _ H0 H1 Ru'').
        { eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ w (proj1 (proj1 (proj1 declp)))). }
        eapply PCUICWeakeningEnv.on_declared_projection in declp; eauto.
        eapply weaken_equality in X0; eauto.

    - simpl in *.
      destruct inversion_Proj as (u & mdecl & idecl & decl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      symmetry in wildcard3.
      pose proof (reduce_to_ind_complete _ _ _ _ _ wildcard3).
      clear wildcard3; simpl. specialize (Hc'' _ Hc) as typ.
      eapply equality_Ind_r_inv in typ as [ui' [l' [red Rgl Ra]]]; auto.
      eapply H. exact red.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & cdecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct declp; simpl in *.
      destruct d as [decl [body decli]].
      destruct (declared_inductive_inj decli H0) as [-> ->].
      simpl in *. intuition congruence.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & cdecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      symmetry in wildcard5.
      eapply lookup_ind_decl_complete in wildcard5; auto.
      destruct declp. do 2 eexists; eauto. exact H0.
    
    - eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
      sq; split.
      * econstructor; eauto.
        eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
      * intros T' HT'.
        eapply inversion_Fix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
        congruence.
      
    - now eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.

    - eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
      sq; split.
      * econstructor; eauto.
        eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
      * intros T' HT'.
        eapply inversion_CoFix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
        congruence.
      
    - now eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.

    - now eapply inversion_Prim in HT.
  Defined.

  Definition type_of Γ t wt : term := (infer Γ t wt).
  
  Open Scope type_scope.
  
  Definition map_typing_result {A B} (f : A -> B) (e : typing_result A) : typing_result B :=
    match e with
    | Checked a => Checked (f a)
    | TypeError e => TypeError e
    end.

  Arguments iswelltyped {cf Σ Γ t A}.

  Lemma infer_clause_1_irrel Γ n H wt wt' : infer_clause_1 infer Γ n H wt = infer_clause_1 infer Γ n H wt' :> term.
  Proof.
    destruct H as [[b|] eq]; simp infer. simpl. reflexivity. bang.
  Qed.

  (* Lemma infer_irrel {Γ t} (wt wt' : welltyped Σ Γ t) : infer Γ t wt = infer Γ t wt' :> term.
  Proof.
    funelim (infer Γ t wt); try solve [simp infer; simpl; try bang; auto].

    simp infer. simpl. f_equal. 
    simp infer. simpl. f_equal. apply H.
    simp infer; simpl; f_equal. apply H.
    simp infer. simpl. 
    simp infer. eapply infer_clause_1_irrel. revert Heqcall. bang.
  Qed.*)

  Lemma type_of_subtype {Γ t T} (wt : Σ ;;; Γ |- t : T) :
    ∥ Σ ;;; Γ ⊢ type_of Γ t (iswelltyped wt) ≤ T ∥.
  Proof.
    unfold type_of.
    destruct infer as [P [[HP Hprinc]]].
    sq. simpl. now eapply Hprinc.
  Qed.

  (* Note the careful use of squashing here: the principal type is accessible 
    computationally but the proof it is principal is squashed (in Prop).
    The [PCUICPrincipality.principal_type] proof gives an unsquashed version of the
    same theorem. *)
    
  Theorem principal_types {Γ t} (wt : welltyped Σ Γ t) : 
    ∑ P, ∥ forall T, Σ ;;; Γ |- t : T -> (Σ ;;; Γ |- t : P) * (Σ ;;; Γ ⊢ P ≤ T) ∥.
  Proof.
    exists (infer Γ t wt).
    destruct infer as [T' [[HT' HT]]].
    sq. intuition eauto.
  Qed.

End TypeOf.
