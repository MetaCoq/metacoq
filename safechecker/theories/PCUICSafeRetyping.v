(* Distributed under the terms of the MIT license. *)

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From Coq Require Import Bool String List Program.
From MetaCoq.Template Require Import config monad_utils utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICSafeLemmata PCUICSubstitution PCUICValidity
     PCUICGeneration PCUICInversion PCUICValidity PCUICInductives PCUICSR
     PCUICCumulativity PCUICConversion PCUICConfluence PCUICArities
     PCUICWeakeningEnv.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker.

Require Import ssreflect.


Require Import PCUICAstUtils.
Lemma cumul_Ind_Ind_inv {cf:checker_flags} {Σ : global_env_ext} Γ ind u args ind' u' args' : 
  wf Σ ->
  Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind' u') args' ->
  eq_inductive ind ind' *
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| u u' *
  All2 (conv Σ Γ) args args'.
Proof.
  intros wfΣ cum.
  eapply invert_cumul_ind_l in cum as [ui' [l' [redl [ru conv]]]]; auto.
  eapply red_mkApps_tInd in redl as [args'' [eqind red']]; auto.
  apply mkApps_eq_inj in eqind as [eq ->]=> //; auto. noconf eq.
  intuition auto.
  eapply eq_inductive_refl.
  transitivity args''; auto.
  eapply All2_symmetry. typeclasses eauto.
  eapply (All2_impl red'). intros x y; apply red_conv.
Qed.


Definition well_sorted {cf:checker_flags} Σ Γ T := 
  ∥ ∑ s, Σ ;;; Γ |- T : tSort s ∥.


(** * Retyping

  The [infer] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Definition principal_type {cf:checker_flags} Σ Γ t := { T : term | ∥ (Σ ;;; Γ |- t : T) * (forall T', Σ ;;; Γ |- t : T' -> Σ ;;; Γ |- T <= T') ∥ }.
Definition principal_sort {cf:checker_flags} Σ Γ T := { s : Universe.t | ∥ (Σ ;;; Γ |- T : tSort s) * (forall s', Σ ;;; Γ |- T : tSort s' -> leq_universe Σ s s') ∥ }.

Definition principal_typed_type {cf:checker_flags} {Σ Γ t} (wt : principal_type Σ Γ t) := proj1_sig wt.
Definition principal_sort_sort {cf:checker_flags} Σ Γ T (ps : principal_sort Σ Γ T) : Universe.t := proj1_sig ps.
Coercion principal_typed_type : principal_type >-> term.
Coercion principal_sort_sort : principal_sort >-> Universe.t.

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Lemma typing_wellformed Γ t T : Σ ;;; Γ |- t : T -> wellformed Σ Γ T.
  Proof.
    intros H.
    destruct hΣ. destruct Hφ.
    apply validity in H; auto. destruct H as [wfA | [s tyT]].
    right. constructor. auto. left. econstructor; eauto.
  Qed.
End TypeOf.

Lemma reduce_to_ind_complete {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ) Γ ty wat e : 
  reduce_to_ind (sq wfΣ) Γ ty wat = TypeError e ->  
  (∑ ind u args, red Σ Γ ty (mkApps (tInd ind u) args)) -> False.
Proof.
Admitted.

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
      eapply typing_wellformed; eauto. Defined.
    Next Obligation. intros Γ t ws [s [[Hs Hp]]]. simpl in *.
      unfold infer_as_sort_obligation_1.
      destruct ws as [[s' Hs']]. 
      specialize (Hp _ Hs').
      eapply invert_cumul_sort_r in Hp as [u' [redu' leq]].
      destruct reduce_to_sort => //.
      intros u wc [= <-].
      todo "Needs completeness of reduce_to_sort"%string.
    Qed.
    Next Obligation.
      simpl. intros.
      todo "sort"%string.
    Qed.
  End SortOf.

  Program Definition infer_as_prod Γ T
    (isprod : ∥ ∑ na A B, Σ ;;; Γ |- T <= tProd na A B ∥) : 
    ∑ na' A' B', ∥ red Σ.1 Γ T (tProd na' A' B') ∥ :=
    match @reduce_to_prod cf Σ hΣ Γ T _ with
    | Checked p => p
    | TypeError e => !
    end.
    Next Obligation. exact (todo "completeness"). Qed.
    Next Obligation. exact (todo "completeness"). Qed.
  
  
  Equations lookup_ind_decl ind : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
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
    ((∑ mdecl idecl, declared_inductive Σ mdecl ind idecl) -> False).
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

    infer Γ (tSort s) _ := ret (tSort (Universe.try_suc s));

    infer Γ (tProd n ty b) wt :=
      let ty1 := infer Γ ty _ in
      let s1 := infer_as_sort (todo "wt") ty1 in
      let ty2 := infer (Γ ,, vass n ty) b _  in
      let s2 := infer_as_sort (todo "wt2") ty2 in
      ret (tSort (Universe.sort_of_product s1 s2));

    infer Γ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) b _ in
      ret (tProd n t t2);

    infer Γ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) b' _ in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ (tApp t a) wt :=
      let ty := infer Γ t _ in
      let pi := infer_as_prod Γ ty _  in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ (tConst cst u) wt with inspect (lookup_env (fst Σ) cst) :=
      { | ret (Some (ConstantDecl d)) := ret (subst_instance_constr u d.(cst_type));
        |  _ := ! };

    infer Γ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked decl) := ret (subst_instance_constr u decl.π2.π1.(ind_type));
        | ret (TypeError e) := ! };
    
    infer Γ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_ctors) k) := 
        { | ret (Some cdecl) => ret (type_of_constructor d.π1 cdecl (ind, k) u);
          | ret None => ! };
      | ret (TypeError e) => ! };

    infer Γ (tCase (ind, par) p c brs) wt with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
      { | ret (Checked indargs) =>
          ret (mkApps p (List.skipn par indargs.π2.π2.π1 ++ [c]));
        | ret (TypeError _) => ! };

    infer Γ (tProj (ind, n, k) c) wt with inspect (@lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_projs) k) :=
        { | ret (Some pdecl) with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
          { | ret (Checked indargs) => 
              let ty := snd pdecl in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance_constr indargs.π2.π1 ty));
            | ret (TypeError _) => ! };
         | ret None => ! };
        | ret (TypeError e) => ! };

    infer Γ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! };

    infer Γ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! }
  }.
  Proof.
    all:destruct hΣ, Hφ; destruct wt as [T HT]; try clear infer.
    all:try solve [econstructor; eauto].

    - sq. destruct (nth_error Γ n) eqn:hnth => //.
      eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in hnth; noconf hnth. noconf wildcard0.
      split; [now constructor|].
      intros T' Ht'.
      eapply inversion_Rel in Ht' as (? & ? & ? & ?); auto.
      now rewrite e in e0; noconf e0.
      
    - eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in wildcard => //.
     
    - depind HT. eapply IHHT; eauto.

    - depind HT; eapply IHHT; eauto.

    - eapply inversion_Sort in HT as (l & wf & inl & eqs & cum); auto; subst s.
      sq.
      split. eapply meta_conv. econstructor; eauto.
      f_equal; eapply eq_univ''. simpl.
      unfold UnivExpr.make, Universe.super.
      destruct (NoPropLevel.of_level l); simpl; auto.
      destruct t; simpl; auto.
      intros T' (l' & wf' & inl' & eqs' & cum')%inversion_Sort; auto.
      eapply Universe.make_inj in eqs'; subst l'.
      etransitivity; eauto.
      do 2 constructor.
      unfold Universe.make, UnivExpr.make, Universe.super.
      destruct (NoPropLevel.of_level l); simpl; auto;
      try destruct t; simpl; auto; reflexivity.
            
    - eapply inversion_Prod in HT as (? & ? & ? & ? & ?); try econstructor; eauto.
    - destruct hΣ. destruct Hφ. destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?); try econstructor; eauto.
    - simpl in *.
      destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?).
      subst ty1 ty2.
      destruct infer_as_sort as [x1 [[Hx1 Hx1p]]]; simpl.
      destruct infer_as_sort as [x2 [[Hx2 Hx2p]]]; simpl.
      subst s1 s2; simpl in *. sq.
      split.
      * specialize (Hx1p _ t).
        specialize (Hx2p _ t0).
        econstructor; eauto.
      * intros T' Ht'.
        eapply inversion_Prod in Ht' as (? & ? & ? & ? & ?); auto.
        etransitivity; eauto. constructor. constructor.
        eapply leq_universe_product_mon; eauto.

    - eapply inversion_Lambda in HT as (? & ? & ? & ? & ?); try econstructor; eauto.
    - simpl in t2. destruct (inversion_Lambda Σ w HT) as (? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst t2; simpl in *.
      sq. split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ?)%inversion_Lambda; auto.
        specialize (pbty _ t3).
        transitivity (tProd n t x2); eauto.
        eapply congr_cumul_prod; auto.

    - eapply inversion_LetIn in HT as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - simpl in b'_ty.
      destruct (inversion_LetIn Σ w HT) as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst b'_ty; simpl in *.
      sq; split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_LetIn; auto.
        etransitivity; eauto.
        eapply cumul_LetIn_bo; eauto.

    - eapply inversion_App in HT as (? & ? & ? & ? & ?); try econstructor; eauto.
    - simpl in ty. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst ty; simpl in *.
      sq. exists x, x0, x1. now eapply pbty.
      
    - simpl in *. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [tty [[Htty pbty]]]; subst ty; simpl in *.
      destruct pi as [na' [A' [B' [red]]]].
      sq. split.
      * simpl.
        eapply type_reduction in Htty; eauto.
        eapply type_App; eauto.
        specialize (pbty _ t0).
        assert (Σ ;;; Γ |- tProd na' A' B' <= tProd x x0 x1).
        eapply cumul_red_l_inv; eauto.
        eapply cumul_Prod_Prod_inv in X as [Ha _]; auto.
        eapply type_Cumul; eauto.
        eapply validity in Htty; auto.
        eapply isWAT_tProd in Htty; pcuic.
        eapply conv_cumul. now symmetry.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_App; auto.
        specialize (pbty _ t2). simpl.
        etransitivity; [|eassumption].
        assert (Σ ;;; Γ |- tProd na' A' B' <= tProd x2 x3 x4).
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Prod_Prod_inv in X as [Ha Hb]; auto.
        eapply (substitution_cumul _ Γ [vass x2 x3] []); eauto.
        eapply validity in t2; pcuic.
        eapply isWAT_tProd in t2 as [_ isWAT]; auto.
        now eapply isWAT_wf_local in isWAT. pcuic.
        constructor. constructor.
        now rewrite subst_empty.

    - eapply inversion_Const in HT as [decl ?] => //.
      intuition auto. red in a0. rewrite a0 in wildcard. noconf wildcard.
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
      assert (declared_constructor Σ decl body (ind, k) cdecl) as declc.
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
      destruct HT as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      eexists; eauto.
    - simpl. destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]]. simpl.
      eapply validity in Hty.
      eapply wat_wellformed; auto. sq; auto. auto.
    - simpl in *. 
      destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]].
      simpl in wildcard. destruct reduce_to_ind => //.
      injection wildcard. intros ->. clear wildcard.
      destruct a as [i [u' [l [red]]]].
      simpl.
      eapply type_reduction in Hty; eauto.
      pose proof (Hp _ Hc).
      assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u) args).
      { eapply cumul_red_l_inv; eauto. }
      eapply cumul_Ind_Ind_inv in X0 as [[eqi Ru] cl]; auto.
      sq; split; simpl.
      * eapply type_Cumul. econstructor. 3:eauto. all:eauto.
        todo "cumulativity here"%string.
        eapply conv_cumul.
        eapply mkApps_conv_args; auto.
        eapply All2_app. 2:repeat (constructor; auto).
        eapply All2_skipn. now symmetry in cl.
      * intros T'' Hc'.
        eapply inversion_Case in Hc' as (u'' & args' & mdecl' & idecl' & ps' & pty'
           & btys' & decli' & indp' & bcp' & Hpty' & lebs' & isco' & Hc' & Hbtys' & all' & cum'); auto.
        etransitivity. simpl in cum'. 2:eassumption.
        eapply conv_cumul, mkApps_conv_args; auto.
        eapply All2_app. 2:repeat (constructor; auto).
        eapply All2_skipn.
        specialize (Hp _ Hc').
        assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u'') args').
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Ind_Ind_inv in X0 as [[eqi' Ru'] cl']; auto.
      
    - simpl in wildcard1.
      destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]]. simpl.
      destruct validity as [_ i]. simpl in wildcard1.
      specialize (Hp _ Hc).
      eapply invert_cumul_ind_r in Hp as [ui' [l' [red [Ru ca]]]]; auto.
      symmetry in wildcard1; eapply reduce_to_ind_complete in wildcard1 => //.
      now exists ind, ui', l'.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      simpl in cum.
      eexists; eauto.
    - simpl; destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      eapply validity in Hc'; auto.
      eapply wat_wellformed; auto. sq; auto.
    - simpl in *. destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      destruct reduce_to_ind => //. injection wildcard1. intros ->.
      clear wildcard1.
      destruct a as [i [u' [l [red]]]]. simpl.
      simpl in red.
      eapply type_reduction in Hc'; eauto.
      pose proof (Hc'' _ Hc).
      assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u) args).
      { eapply cumul_red_l_inv; eauto. }
      eapply cumul_Ind_Ind_inv in X0 as [[eqi' Ru'] cl']; eauto.
      destruct d as [decl [body decli]].
      pose proof (declared_inductive_inj (proj1 declp) decli) as [-> ->].
      assert (declared_projection Σ mdecl idecl (ind, n, k) pdecl).
      { red; intuition eauto. simpl. eapply declp. }
      pose proof (@PCUICReflect.eqb_eq inductive _). apply H0 in eqi'. subst ind.
      destruct (declared_projection_inj declp H) as [_ [_ ->]].
      sq. split; auto.
      * econstructor; eauto. now rewrite (All2_length _ _ cl').
      * intros.
        eapply inversion_Proj in X0 as (u'' & mdecl' & idecl' & pdecl'' & args' & 
            declp' & Hc''' & Hargs' & cum'); auto.
        simpl in *. subst ty.
        destruct (declared_projection_inj H declp') as [-> [-> ->]].
        etransitivity; eauto.
        specialize (Hc'' _ Hc''').
        assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd i u'') args').
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Ind_Ind_inv in X0 as [[eqi'' Ru''] cl'']; auto.
        todo "cumulative inductives here"%string.

    - simpl in *.
      destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      symmetry in wildcard3.
      eapply reduce_to_ind_complete in wildcard3; auto.
      clear wildcard3; simpl. specialize (Hc'' _ Hc).
      eapply invert_cumul_ind_r in Hc'' as [ui' [l' [red [Rgl Ra]]]]; auto.
      eexists _, _, _; eauto.      

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct declp; simpl in *.
      destruct d as [decl [body decli]].
      destruct (declared_inductive_inj decli H0) as [-> ->].
      simpl in *. intuition congruence.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      symmetry in wildcard5.
      eapply lookup_ind_decl_complete in wildcard5; auto.
      destruct declp. do 2 eexists; eauto.
    
    - eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
      sq; split.
      * econstructor; eauto.
        eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
        eapply typing_wf_local; eauto.
      * intros T' HT'.
        eapply inversion_Fix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
        congruence.
      
    - now eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.

  - eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
    sq; split.
    * econstructor; eauto.
      eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
      eapply typing_wf_local; eauto.
    * intros T' HT'.
      eapply inversion_CoFix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
      congruence.
    
  - now eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
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

    simp infer. simpl. f_equal. todo "sorts".
    simp infer. simpl. f_equal. apply H.
    simp infer; simpl; f_equal. apply H.
    simp infer. simpl. todo "prod".
    simp infer. eapply infer_clause_1_irrel. revert Heqcall. bang.
  Qed.*)

  Lemma type_of_subtype {Γ t T} (wt : Σ ;;; Γ |- t : T) :
    ∥ Σ ;;; Γ |- type_of Γ t (iswelltyped wt) <= T ∥.
  Proof.
    unfold type_of.
    destruct infer as [P [[HP Hprinc]]].
    sq. simpl. now eapply Hprinc.
  Qed.

  (* Note the careful use of squashing here: the principal type is accessible 
    computationally but the proof it is principal is squashed (in Prop).
    One could also easily modify the above function to return non-squashed 
    principal typing derivations, if there is some use for it. *)
  Theorem principal_types {Γ t} (wt : welltyped Σ Γ t) : 
    ∑ P, ∥ forall T, Σ ;;; Γ |- t : T -> (Σ ;;; Γ |- t : P) * (Σ ;;; Γ |- P <= T) ∥.
  Proof.
    exists (infer Γ t wt).
    destruct infer as [T' [[HT' HT]]].
    sq. intuition eauto.
  Qed.

End TypeOf.
