(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool Utf8 CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
Set Warnings "-notation-overridden".
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICCasesContexts
     PCUICSigmaCalculus PCUICClosed
     PCUICWeakening PCUICUnivSubst PCUICTyping PCUICGeneration
     PCUICConversion PCUICOnFreeVars PCUICInductives
     PCUICValidity PCUICArities PCUICInversion PCUICInductiveInversion
     PCUICCases PCUICWellScopedCumulativity PCUICSpine PCUICSR
     PCUICSafeLemmata PCUICInductives PCUICInductiveInversion.

Set Warnings "+notation_overridden".

From MetaCoq.PCUIC Require Import PCUICEquality PCUICExpandLets.

Import MCMonadNotation.

Import MCMonadNotation.

Implicit Types cf : checker_flags. (* Use {cf} to parameterize by checker_flags where needed *)

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.


(** Translation from PCUIC back to template-coq terms. 

  This translation is not direct due to two peculiarities of template-coq's syntax:
  - applications are n-ary and not all terms are well-formed, so we have to 
    use an induction on the size of derivations to transform the binary applications
    into n-ary ones.
  - The representation of cases in template-coq is "compact" in the sense that 
    the predicate and branches contexts do not appear in the syntax of terms but can 
    be canonically rebuilt on-demand, as long as the environment has a declaration for the 
    inductive type. In contrast, PCUIC has these contexts explicitely present in terms, 
    so that the theory of reduction (confluence) and conversion do not need to rely on any 
    such well-formedness arguments about the global environment, considerably simplifying the theory:
    For example one couldn't do recursive calls on such "rebuilt" contexts using simple structural
    recursion, the new contexts having no structural relation to the terms at hand.

    This means that Template-Coq's `red1` reduction of cases requires well-formedness conditions
    not readily available in PCUIC's. We solve this conundrum using subject reduction: indeed
    cumulativity is always called starting with two well-sorted types, and we can hence show
    that every one-step reduction in a PCUIC cumulativity derivation goes from a well-typed term
    to a well-typed term. We can hence prove that Template-Coq's `red1` reductions follow from the
    untyped PCUIC reduction when restricted to well-typed terms (which have many more invariants).
    We actually just need the term to be reduced to be well-typed to show that the interpretation 
    preserves one-step reduction in [trans_red1}].
*)

(** Source = PCUIC, Target = Coq *)
Module S := PCUICAst.
Module SE := PCUICEnvironment.
Module ST := PCUICTyping.
Module T := S.
Module TT := ST.

Module SL := PCUICLiftSubst.
Module TL := SL.


Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma trans_local_app Γ Δ : trans_local (SE.app_context Γ Δ) = trans_local Γ ,,, trans_local Δ.
Proof.
  now rewrite /trans_local map_app.
Qed.

Lemma forget_types_map_context {term term'} (f : term' -> term) ctx : 
  forget_types (map_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_context.
Qed.

Lemma All_fold_map_context (P : context -> context_decl -> Type) f ctx :
  All_fold P (map_context f ctx) <~> All_fold (fun Γ d => P (map_context f Γ) (map_decl f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma on_decl_trans_on_free_vars_decl (Γ : context) n (d : context_decl) :
  ondecl
    (λ t : term,
     on_free_vars (closedP (#|Γ| + n) xpredT) (trans t)) d ->
  on_free_vars_decl
    (shiftnP #|map_context trans Γ| (closedP n xpredT)) (trans_decl d).
Proof.
  intros []. unfold on_free_vars_decl, test_decl.
  destruct d as [na [b|] ty]; cbn in * => //;
     rewrite map_context_length shiftnP_closedP shiftnP_xpredT //.
  apply/andP. split; auto.
Qed.

Lemma All_fold_closed_on_free_vars_ctx n ctx : 
  All_fold (λ Γ : context, ondecl (λ t : term,
        on_free_vars (closedP (#|Γ| + n) xpredT)
      (trans t))) ctx ->
  on_free_vars_ctx (closedP n xpredT) (map_context trans ctx).
Proof.
  intros af.
  eapply PCUICConfluence.on_free_vars_ctx_All_fold.
  eapply All_fold_map_context, All_fold_impl; tea => ctx' d; cbn.
  now intros; eapply on_decl_trans_on_free_vars_decl.
Qed.

Definition plengths := 
    (@context_assumptions_subst_context,
    @context_assumptions_app,
    @context_assumptions_subst_instance, @context_assumptions_lift_context,
     @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @app_length, @List.rev_length, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r, 
    @map_length, @mapi_length, @mapi_rec_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    @smash_context_length, @arities_context_length).
  

Lemma trans_on_free_vars P t : 
  on_free_vars P t -> on_free_vars P (trans t).
Proof.
  revert P t. eapply term_on_free_vars_ind; cbn; auto; 
    lazymatch goal with |- context [case_info] => idtac | _ => solve_all end.
  - intros; rtoProp; intuition auto.
    * solve_all.
    * now rewrite map_context_length.
    * rewrite map_length.
      rewrite test_context_k_closed_on_free_vars_ctx.
      now eapply All_fold_closed_on_free_vars_ctx. 
    * solve_all.
      rewrite test_context_k_closed_on_free_vars_ctx.
      rewrite on_free_vars_ctx_smash //.
      destruct X as [_ IH _ _].
      now eapply All_fold_closed_on_free_vars_ctx.
      rewrite smash_context_length /=.
      eapply on_free_vars_expand_lets_k. now len.
      destruct X as [hctx ihctx _ _].
      eapply on_free_vars_ctx_subst_context0.
      rewrite !plengths.
      eapply All_fold_closed_on_free_vars_ctx in ihctx.
      rewrite -> PCUICConfluence.closedP_shiftnP in ihctx.
      rewrite /id. rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      { unfold shiftnP. intros i. rewrite orb_false_r.
        move/Nat.ltb_lt => hlt. now apply/orP; left; eapply Nat.ltb_lt. }
      solve_all.
      rewrite !plengths. now apply X.
  - unfold test_def. solve_all. cbn. now len in b1.
  - unfold test_def. solve_all. cbn. now len in b1.
Qed.

Lemma on_free_vars_ctx_trans k ctx : 
  on_free_vars_ctx (closedP k xpredT) ctx ->
  on_free_vars_ctx (closedP k xpredT) (map_context trans ctx).
Proof.
  intros H; apply PCUICConfluence.on_free_vars_ctx_All_fold in H. 
  eapply All_fold_closed_on_free_vars_ctx.
  eapply All_fold_impl; tea; cbn.
  intros ? ? h.
  destruct x as [na [b|] ty]; cbn in *;
  constructor; cbn; (move/andP: h => /= // || move: h) ;
  rewrite ?shiftnP_closedP ?shiftnP_xpredT //;
  intros; try now eapply trans_on_free_vars.
Qed.

Lemma closedP_mon n n' P i : n <= n' -> closedP n P i -> closedP n' P i.
Proof.
  intros hn; rewrite /closedP.
  repeat nat_compare_specs => //.
Qed.

Ltac len := rewrite !plengths.

Lemma trans_lift (t : S.term) P n k :
  on_free_vars P t ->
  trans (S.lift n k t) = T.lift n k (trans t).
Proof.
  intros onfvs.
  revert P t onfvs k. 
  apply: term_on_free_vars_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - f_equal; auto. 
    rewrite /T.map_predicate_k /id /PCUICAst.map_predicate /= /=. 
    f_equal. autorewrite with map; solve_all.
    rewrite map_context_length. solve_all.
    rewrite !map_map_compose. solve_all.
    rewrite /trans_branch /T.map_branch_k. cbn -[expand_lets].
    len. rewrite (Nat.add_comm (context_assumptions _) k).
    f_equal. destruct X as [onbctx ihbctx hbod ->].
    relativize (context_assumptions _).
    erewrite <- expand_lets_lift. 2:len. 2:reflexivity.
    rewrite !plengths.
    rewrite /id. f_equal.
    rewrite distr_lift_subst_context.
    rewrite !plengths. f_equal.
    rewrite map_rev. f_equal. solve_all.
    rewrite PCUICClosed.closed_ctx_lift //.
    rewrite closedn_ctx_on_free_vars.
    rewrite on_free_vars_ctx_subst_instance.
    eapply on_free_vars_ctx_trans. eapply on_free_vars_ctx_impl; tea.
    intros i. eapply closedP_mon. lia.
  - f_equal. solve_all.
  - f_equal; red in X, X0; solve_all.
Qed.

Definition on_fst {A B C} (f:A->C) (p:A×B) := (f p.1, p.2).

Definition trans_def (decl:def PCUICAst.term) : def term.
Proof.
  destruct decl.
  constructor.
  - exact dname.
  - exact (trans dtype).
  - exact (trans dbody).
  - exact rarg.
Defined.

Lemma trans_global_ext_levels Σ:
  S.global_ext_levels Σ = T.global_ext_levels (trans_global Σ).
Proof.
  unfold S.global_ext_levels, global_ext_levels.
  destruct Σ.
  cbn [trans_global fst snd].
  f_equal.
  induction g.
  - reflexivity.
  - unfold S.global_levels in IHg.
    cbn.
    rewrite IHg.
    f_equal.
    destruct a.
    cbn.
    unfold T.monomorphic_levels_decl, T.monomorphic_udecl_decl, T.on_udecl_decl.
    unfold S.monomorphic_levels_decl, S.monomorphic_udecl_decl, S.on_udecl_decl.
    destruct g0.
    + cbn.
      destruct c.
      reflexivity.
    + cbn.
      destruct m.
      reflexivity.
Qed.

Lemma trans_global_ext_constraints Σ :
  S.global_ext_constraints Σ = T.global_ext_constraints (trans_global Σ).
Proof.
  destruct Σ.
  unfold S.global_ext_constraints, T.global_ext_constraints. simpl.
  f_equal. clear u.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. f_equal. clear.
    destruct a as [? []]; reflexivity.
Qed.

Lemma trans_mem_level_set l Σ:
  LevelSet.mem l (S.global_ext_levels Σ) ->
  LevelSet.mem l (T.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_in_level_set l Σ:
  LevelSet.In l (S.global_ext_levels Σ) ->
  LevelSet.In l (T.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_lookup Σ cst :
  lookup_env (trans_global_decls Σ) cst = option_map trans_global_decl (SE.lookup_env Σ cst).
Proof.
  cbn in *.
  induction Σ.
  - reflexivity.
  - cbn.
    unfold eq_kername in *; destruct kername_eq_dec; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma trans_declared_constant Σ cst decl:
  S.declared_constant Σ cst decl ->
  T.declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold T.declared_constant.
  rewrite trans_lookup.
  unfold S.declared_constant.
  intros ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
  ConstraintSet.In x (S.global_ext_constraints Σ) ->
  ConstraintSet.In x (T.global_ext_constraints (trans_global Σ)).
Proof.
  rewrite trans_global_ext_constraints.
  trivial.
Qed.

Lemma trans_consistent_instance_ext {cf} Σ decl u:
  S.consistent_instance_ext Σ decl u ->
  T.consistent_instance_ext (trans_global Σ) decl u.
Proof.
  intros H.
  unfold consistent_instance_ext, S.consistent_instance_ext in *.
  unfold consistent_instance, S.consistent_instance in *.
  destruct decl;trivial.
  destruct H as (?&?&?).
  repeat split;trivial.
  - eapply forallb_impl.
    2: apply H.
    cbv beta.
    intros.
    now apply trans_mem_level_set.
  - unfold valid_constraints in *.
    destruct config.check_univs;trivial.
    unfold valid_constraints0 in *.
    intros.
    apply H1.
    unfold satisfies in *.
    unfold ConstraintSet.For_all in *.
    intros.
    apply H2.
    now apply trans_constraintSet_in.
Qed.

Lemma trans_declared_inductive Σ ind mdecl idecl:
  S.declared_inductive Σ ind mdecl idecl ->
  T.declared_inductive (trans_global_decls Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body mdecl (inductive_ind ind) idecl).
Proof.
  intros [].
  split.
  - unfold T.declared_minductive, S.declared_minductive in *.
    now rewrite trans_lookup H.
  - cbn. now rewrite nth_error_mapi H0 /=.
Qed.

Lemma trans_declared_constructor Σ c mdecl idecl cdecl :
  let ind := (inductive_ind (fst c)) in
  S.declared_constructor Σ c mdecl idecl cdecl ->
  T.declared_constructor (trans_global_decls Σ) c (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl)
    (trans_constructor_body ind mdecl cdecl).
Proof.
  intros ind [].
  split.
  - now apply trans_declared_inductive.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
  trans (PCUICAst.mkApps t args) =
  mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity. 
  - cbn [map].
    cbn.
    rewrite IHargs.
    reflexivity.
Qed.

Lemma trans_decl_type decl:
  trans (decl_type decl) =
  decl_type (trans_decl decl).
Proof. 
  destruct decl.
  reflexivity.
Qed.

Lemma expand_lets_subst_comm Γ k s : 
  expand_lets (subst_context s k Γ) ∘ subst s (#|Γ| + k) =1 
  subst s (context_assumptions Γ + k) ∘ expand_lets Γ.
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros x. len.
  rewrite !PCUICSigmaCalculus.subst_extended_subst.
  rewrite distr_subst. rewrite Nat.add_comm; f_equal; len.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' 0 Γ) =
  subst_context (map (subst s k) s') 0 (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto; 
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal; 
    auto; f_equal; len;
  rewrite distr_subst_rec; lia_f_equal.
Qed.

Lemma trans_subst p q xs k t :
  on_free_vars p t ->
  forallb (on_free_vars q) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros onfvs; revert p t onfvs k.
  apply: term_on_free_vars_ind; intros; cbn.
  all: cbn;try congruence.
  - destruct leb;trivial.
    rewrite nth_error_map.
    destruct nth_error eqn:hnth;cbn.
    2:now rewrite map_length.
    rewrite (trans_lift _ q) //.
    eapply nth_error_forallb in H0; tea.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    solve_all. rewrite b //. solve_all.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 // H4 //.
  - rewrite H0 // H2 //.
  - f_equal; trivial.
    rewrite /= /id /T.map_predicate_k /map_predicate_k /map_predicate /=.
    f_equal; solve_all.
    * rewrite b //. solve_all.
    * rewrite H1 //. solve_all. now rewrite map_context_length.
    * rewrite H3 //.
    * rewrite /trans_branch; rewrite !map_map_compose.
      eapply All_map_eq, All_impl; tea; cbv beta; intros.
      rewrite /T.map_branch_k /=. f_equal; auto.
      len => /=. destruct X3 as [hctx ihctx hb ihb].
      rewrite ihb // /id. 
      replace (context_assumptions (map_context trans (bcontext x))) with
        (context_assumptions ((subst_context (List.rev (map trans (pparams pred))) 0
        (map_context trans (bcontext x))@[puinst pred]))). 2:now len.
      cbn. erewrite <- expand_lets_subst_comm. f_equal.
      2:now len.
      rewrite subst_context_subst_context. f_equal.
      rewrite map_rev; f_equal. solve_all. rewrite b //. solve_all. len.
      rewrite PCUICSpine.closed_ctx_subst //.
      eapply on_free_vars_ctx_trans in hctx.
      rewrite closedn_ctx_on_free_vars.
      rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      intros. eapply closedP_mon; tea. lia.
  - f_equal. rewrite H0 //.
  - f_equal. rewrite !map_map_compose. solve_all.
    rewrite a //. solve_all.
    rewrite b1 //. solve_all.
  - f_equal. rewrite !map_map_compose. solve_all.
    rewrite a //. solve_all.
    rewrite b1 //. solve_all.
Qed.

Lemma trans_subst_ctx (Γ : context) xs k t :
  on_free_vars (shiftnP (#|xs| + #|Γ|) xpred0) t ->
  forallb (on_free_vars (shiftnP #|Γ| xpred0)) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros ont onxs. 
  now erewrite trans_subst; tea.
Qed.

Lemma trans_subst10 u p q B :
  on_free_vars p B -> 
  on_free_vars q u ->
  trans (S.subst1 u 0 B) =
  T.subst10 (trans u) (trans B).
Proof.
  unfold S.subst1. intros onB onu.
  rewrite (trans_subst p q) //. cbn. now rewrite onu.
Qed.

Lemma trans_subst_instance u t:
  trans (subst_instance u t) =
  subst_instance u (trans t).
Proof.
  induction t in u |- * using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map. 
    f_equal.
    apply All_map_eq. solve_all.
  - red in X, X0.
    f_equal.
    + rewrite /map_predicate /=. f_equal. solve_all. solve_all.
    + solve_all.
    + rewrite !map_map_compose. eapply All_map_eq, All_impl; tea; cbv beta.
      intros ? []. rewrite /trans_branch /= /map_branch /= /id. f_equal.
      rewrite PCUICUnivSubstitution.subst_instance_expand_lets e.
      rewrite PCUICUnivSubstitution.subst_instance_subst_context. f_equal.
      f_equal. rewrite [_@[u]]map_rev. f_equal. solve_all.
      solve_all. rewrite [_@[u]] map_map_compose.
      setoid_rewrite compose_map_decl.
      setoid_rewrite PCUICUnivSubstitution.subst_instance_two.
      clear -a. rewrite [_@[_]]map_map_compose.
      rewrite map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X. rewrite !map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X.
    rewrite !map_map_compose; solve_all.
Qed.

Lemma trans_subst_instance_ctx Γ u :
  trans_local Γ@[u] = (trans_local Γ)@[u].
Proof.
  rewrite /subst_instance /= /trans_local /SE.subst_instance_context /subst_instance_context 
    /map_context.
  rewrite !map_map_compose. apply map_ext.
  move => [na [b|] ty]; cbn;
  rewrite /trans_decl /map_decl /=; f_equal; cbn;
  now rewrite trans_subst_instance.
Qed.

Lemma trans_cst_type decl:
  trans (SE.cst_type decl) =
  cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type mdecl i idecl:
  trans (SE.ind_type idecl) =
  ind_type (trans_one_ind_body mdecl i idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_dtype decl:
  trans (dtype decl) =
  dtype (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_dbody decl:
  trans (dbody decl) =
  dbody (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.



(*Lemma trans_type_of_constructor mdecl cdecl ind i u :
  trans (ST.type_of_constructor mdecl cdecl (ind, i) u) =
  TT.type_of_constructor 
    (trans_minductive_body mdecl) 
    (trans_constructor_body (inductive_ind ind) mdecl cdecl)
    (ind,i)
    u.
Proof.
  unfold ST.type_of_constructor.
  rewrite (trans_subst xpredT xpredT).
  unfold TT.type_of_constructor.
  f_equal.
  - cbn [fst].
    rewrite PCUICCases.inds_spec.
    rewrite inds_spec.
    rewrite map_rev.
    rewrite map_mapi.
    destruct mdecl.
    cbn.
    f_equal.
    remember 0 as k.
    induction ind_bodies0 in k |- *.
    + reflexivity.
    + cbn.
      f_equal.
      apply IHind_bodies0.
  - rewrite trans_subst_instance.
    f_equal.
Qed.*)

Lemma trans_declared_projection Σ p mdecl idecl cdecl pdecl :
  let ind := (inductive_ind (fst (fst p))) in
  S.declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  T.declared_projection (trans_global Σ).1 p (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl) 
    (trans_constructor_body ind mdecl cdecl) (on_snd trans pdecl).
Proof.
  intros ind []. split; [|split].
  - now apply trans_declared_constructor.
  - unfold on_snd.
    destruct H0.
    destruct pdecl, p.
    cbn in *.
    change (Some (i, trans t)) with
      (Some((fun '(x, y) => (x, trans y)) (i,t))).
    now apply map_nth_error.
  - now destruct mdecl;cbn in *.
Qed.

Lemma inv_opt_monad {X Y Z} (f:option X) (g:X->option Y) (h:X->Y->option Z) c:
  (x <- f;;
  y <- g x;;
  h x y) = Some c ->
  exists a b, f = Some a /\
  g a = Some b /\ h a b = Some c.
Proof.
  intros H.
  destruct f eqn: ?;cbn in *;try congruence.
  destruct (g x) eqn: ?;cbn in *;try congruence.
  do 2 eexists.
  repeat split;eassumption.
Qed.

Lemma trans_destr_arity x:
  destArity [] (trans x) =
  option_map (fun '(xs,u) => (map trans_decl xs,u)) (destArity [] x).
Proof.
  set xs := (@nil context_decl). unfold xs at 1.
  replace (@nil context_decl) with (map trans_decl xs) at 1 by (now subst). clearbody xs.
  induction x in xs |- *;cbn;trivial;unfold snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (SE.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (SE.it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map trans_decl xs) (trans t).
Proof.
  induction xs in t |- *;simpl;trivial.
  rewrite IHxs.
  f_equal.
  apply trans_mkProd_or_LetIn.
Qed.


Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

Lemma trans_isLambda t :
  T.isLambda (trans t) = S.isLambda t.
Proof.
  destruct t; cbnr.
Qed.

Lemma trans_unfold_fix p mfix idx narg fn :
  on_free_vars p (tFix mfix idx) ->
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_fix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold fix_subst. rewrite map_length.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.  
Qed.

Lemma trans_unfold_cofix p mfix idx narg fn :
  on_free_vars p (tCoFix mfix idx) ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_cofix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold cofix_subst. rewrite map_length.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.  
Qed.
  
Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite decompose_app_rec_mkApps //. 
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> red1 Σ Γ t u -> red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> red1 Σ Γ t u -> red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.

Lemma forallb_mapi_ext {A B} (p : A -> bool) (l : list A) {f g : nat -> A -> B} :
  forallb p l ->
  (forall i x, p x -> f i x = g i x) ->
  mapi f l = mapi g l.
Proof.
  unfold mapi; generalize 0. induction l; cbn; auto.
  move=> n /andP[] pa pl hf.
  rewrite hf //. f_equal. apply IHl => //.
Qed.

Lemma trans_fix_context p mfix idx :
  on_free_vars p (tFix mfix idx) ->
  map trans_decl (SE.fix_context mfix) =
  fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  unfold fix_context.
  rewrite map_rev map_mapi.
  cbn. move=> onfvs. f_equal.
  rewrite mapi_map. eapply forallb_mapi_ext; tea => i x hx.
  cbn. rewrite /trans_decl /= /vass. f_equal.
  rewrite (trans_lift _ p) //.
  now move/andP: hx.
Qed.

Lemma trans_subst_decl p q s k d : 
  on_free_vars_terms p s ->
  on_free_vars_decl q d ->
  trans_decl (SE.subst_decl s k d) = subst_decl (map trans s) k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /subst_decl /= /map_decl /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //. 
  now move/andP: ond => /=.
  rewrite (trans_subst q p) //. 
  now move/andP: ond => /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //. 
Qed.
  
Lemma trans_subst_context p q s k Γ : 
  on_free_vars_ctx p Γ ->
  on_free_vars_terms q s ->
  trans_local (SE.subst_context s k Γ) = subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|d Γ]; simpl; auto.
  rewrite !subst_context_snoc /= on_free_vars_ctx_snoc.
  move=> /andP[] onΓ ond ons.
  erewrite trans_subst_decl; tea. rewrite /app_context /snoc. len. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_lift_decl p n k d : 
  on_free_vars_decl p d ->
  trans_decl (SE.lift_decl n k d) = lift_decl n k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /lift_decl /= /map_decl /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //. 
  now move/andP: ond => /=.
  rewrite (trans_lift _ p) //. 
  now move/andP: ond => /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //. 
Qed.

Lemma trans_lift_context p n k Γ : 
  on_free_vars_ctx p Γ ->
  trans_local (SE.lift_context n k Γ) = lift_context n k (trans_local Γ).
Proof.
  induction Γ as [|d]; auto.
  rewrite /= !lift_context_snoc /= on_free_vars_ctx_snoc.
  move/andP => [] onΓ ond.
  rewrite (trans_lift_decl (shiftnP #|Γ| p)) //. len. unfold snoc. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_smash_context p Γ Δ : 
  on_free_vars_ctx (shiftnP #|Δ| p) Γ ->
  on_free_vars_ctx p Δ ->
  trans_local (SE.smash_context Γ Δ) = smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in p, Γ |- *; simpl; auto.
  rewrite on_free_vars_ctx_snoc.
  move=> onΓ /andP [] onΔ ona.
  destruct a as [na [b|] ty] => /=.
  rewrite (IHΔ p) //.
  eapply on_free_vars_ctx_subst_context0.
  now rewrite shiftnP_add. cbn.
  move/andP: ona => [] /= -> //.
  f_equal.
  rewrite (trans_subst_context (shiftnP (S #|Δ|) p) (shiftnP #|Δ| p)) //.
  move/andP: ona => [] /= -> //; cbn; auto.
  rewrite (IHΔ p) //. 
  rewrite PCUICConfluence.on_free_vars_ctx_app /=.
  cbn. rewrite shiftnP0. move/andP: ona => [] _ ->.
  now rewrite shiftnP_add. f_equal. rewrite trans_local_app //.
Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = SE.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Lemma on_free_vars_ctx_k_eq p n Γ : 
  on_free_vars_ctx_k p n Γ = on_free_vars_ctx (shiftnP n p) Γ.
Proof.
  rewrite /on_free_vars_ctx_k.
  rewrite alli_shift //.
  rewrite /on_free_vars_ctx.
  eapply alli_ext. intros i x.
  now rewrite shiftnP_add Nat.add_comm.
Qed.

Lemma trans_extended_subst p Γ n :
  on_free_vars_ctx p Γ ->
  map trans (extended_subst Γ n) = extended_subst (trans_local Γ) n.
Proof.
  induction Γ in n, p |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  rewrite on_free_vars_ctx_snoc. move/andP => [] onΓ /andP[] onb onty.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst.
  erewrite on_free_vars_ctx_k_eq => //.
  eapply on_free_vars_ctx_impl; tea. intros i pi. rewrite /shiftnP.
  nat_compare_specs; cbn. auto. now instantiate (1 := xpredT).
  erewrite on_free_vars_lift. eapply onb.
  erewrite (trans_lift _ _); revgoals. eapply onb.
  rewrite (IHΓ p) //. f_equal. f_equal. len.
  now rewrite context_assumptions_map.
  rewrite on_free_vars_ctx_snoc => /andP[] onΓ ont.
  f_equal; eauto.
Qed.

Lemma trans_expand_lets_k p Γ k T : 
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (SE.expand_lets_k Γ k T) = expand_lets_k (trans_local Γ) k (trans T).
Proof.
  rewrite /SE.expand_lets_k => onΓ onT.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0. exact onΓ.
  erewrite on_free_vars_lift. exact onT.
  erewrite (trans_lift _) => //. 2:exact onT.
  erewrite trans_extended_subst; tea.
  rewrite /expand_lets /expand_lets_k.
  now rewrite (context_assumptions_map Γ) map_length.
Qed.

Lemma trans_expand_lets p Γ T : 
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (expand_lets Γ T) = expand_lets (trans_local Γ) (trans T).
Proof.
  move=> onΓ onT.
  rewrite /SE.expand_lets /SE.expand_lets_k.
  rewrite (trans_expand_lets_k p) //.
Qed.

Lemma alpha_eq_trans {Γ Δ} : 
  All2 (compare_decls eq eq) Γ Δ ->
  All2 (compare_decls eq eq) (trans_local Γ) (trans_local Δ).
Proof.
  intros.
  eapply All2_map, All2_impl; tea.
  intros x y []; constructor; subst; auto.
Qed.

Definition wt {cf} Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma isType_wt {cf} Σ Γ T : isType Σ Γ T -> wt Σ Γ T.
Proof.
  intros [s hs]; now exists (PCUICAst.tSort s).
Qed.
Coercion isType_wt : isType >-> wt.

Section wtsub.
  Context {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : PCUICTyping.wf Σ}.
  Import PCUICAst.
  Definition wt_subterm Γ (t : term) : Type := 
    let wt := wt Σ in
    match t with
    | tLambda na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tProd na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tLetIn na b ty b' => [× wt Γ b, wt Γ ty & wt (Γ ,, vdef na b ty) b']
    | tApp f a => wt Γ f × wt Γ a
    | tCase ci p c brs => 
      All (wt Γ) p.(pparams) ×
      ∑ mdecl idecl, 
      [× declared_inductive Σ ci mdecl idecl,
         consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p),
         wf_predicate mdecl idecl p,
         All2 (PCUICEquality.compare_decls eq eq) (PCUICCases.ind_predicate_context ci mdecl idecl) (PCUICAst.pcontext p),
         wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) p.(pcontext)@[p.(puinst)],
         PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p) (List.rev (PCUICAst.pparams p))
          (PCUICEnvironment.smash_context [] (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p]),
          wt (Γ ,,, PCUICCases.case_predicate_context ci mdecl idecl p) p.(preturn),
          wt Γ c &
          All2i (fun i cdecl br => 
            [× wf_branch cdecl br,
               All2 (PCUICEquality.compare_decls eq eq) (bcontext br) (PCUICCases.cstr_branch_context ci mdecl cdecl),
               wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) br.(bcontext)@[p.(puinst)],
               All2 (PCUICEquality.compare_decls eq eq) 
                (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl)
                (Γ ,,, inst_case_branch_context p br) &
              wt (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl) br.(bbody)]) 0 idecl.(ind_ctors) brs]
    | tProj p c => wt Γ c
    | tFix mfix idx | tCoFix mfix idx => 
      All (fun d => wt Γ d.(dtype) × wt (Γ ,,, fix_context mfix) d.(dbody)) mfix
    | tEvar _ l => False
    | tRel i => wf_local Σ Γ
    | _ => unit
    end.
  Import PCUICGeneration PCUICInversion.

  Lemma spine_subst_wt Γ args inst Δ : PCUICSpine.spine_subst Σ Γ args inst Δ ->
    All (wt Σ Γ) inst.
  Proof.
    intros []. clear -inst_subslet wfΣ.
    induction inst_subslet; constructor; auto.
    eexists; tea. eexists; tea.
  Qed.

  Lemma wt_inv {Γ t} : wt Σ Γ t -> wt_subterm Γ t.
  Proof.
    destruct t; simpl; intros [T h]; try exact tt.
    - now eapply typing_wf_local in h.
    - now eapply inversion_Evar in h.
    - eapply inversion_Prod in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Lambda in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_LetIn in h as (?&?&?&?&?&?); tea.
      repeat split; eexists; eauto.
    - eapply inversion_App in h as (?&?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Case in h as (mdecl&idecl&decli&indices&[]&?); tea.
      assert (tty := PCUICValidity.validity scrut_ty).
      eapply PCUICInductiveInversion.isType_mkApps_Ind_smash in tty as []; tea.
      2:eapply (wf_predicate_length_pars wf_pred).
      split.
      eapply spine_subst_wt in s. now eapply All_rev_inv in s.
      exists mdecl, idecl. split; auto. now symmetry.
      * eapply wf_local_app_inv. eapply wf_local_alpha.
        eapply All2_app; [|reflexivity].
        eapply alpha_eq_subst_instance. symmetry; tea.
        eapply wf_ind_predicate; tea. pcuic.
      * eexists; tea.
      * eexists; tea.
      * eapply Forall2_All2 in wf_brs.
        eapply All2i_All2_mix_left in brs_ty; tea.
        eapply All2i_nth_hyp in brs_ty.
        solve_all. split; auto.
        { eapply wf_local_app_inv. eapply wf_local_alpha.
          eapply All2_app; [|reflexivity].
          eapply alpha_eq_subst_instance in a2.
          symmetry; tea.
          eapply validity in scrut_ty.
          epose proof (wf_case_branch_type ps _ decli scrut_ty wf_pred pret_ty conv_pctx i x y).
          forward X. { split; eauto. }
          specialize (X a1) as [].
          eapply wf_local_expand_lets in a5.
          rewrite /PCUICCases.cstr_branch_context.
          rewrite PCUICUnivSubstitution.subst_instance_expand_lets_ctx.
          rewrite PCUICUnivSubstitution.subst_instance_subst_context.
          rewrite PCUICUnivSubstitution.subst_instance_inds.
          erewrite PCUICUnivSubstitution.subst_instance_id_mdecl; tea. }
        erewrite PCUICCasesContexts.inst_case_branch_context_eq; tea. reflexivity.
        eexists; tea.
    - eapply inversion_Proj in h as (?&?&?&?&?&?&?&?&?); tea.
      eexists; eauto.
    - eapply inversion_Fix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
    - eapply inversion_CoFix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
  Qed.
End wtsub.

Ltac outtimes :=
  match goal with
  | ih : _ × _ |- _ =>
    destruct ih as [? ?]
  end.

Lemma red1_cumul {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumul Σ Γ T U.
Proof.
  intros r.
  econstructor 2; tea. constructor. apply leq_term_refl.
Qed.

Lemma red1_cumul_inv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumul Σ Γ U T.
Proof.
  intros r.
  econstructor 3; tea. constructor. eapply leq_term_refl.
Qed.

Definition TTconv {cf} (Σ : global_env_ext) Γ : relation term := 
  clos_refl_sym_trans (relation_disjunction (red1 Σ Γ) (eq_term Σ (T.global_ext_constraints Σ))).

Lemma red1_conv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> TTconv Σ Γ T U.
Proof.
  intros r.
  now repeat constructor. 
Qed.

Lemma trans_expand_lets_ctx p q Γ Δ : 
  on_free_vars_ctx p Γ ->
  on_free_vars_ctx q Δ ->
  trans_local (SE.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Γ) (trans_local Δ).
Proof.
  move=> onΓ onΔ.
  rewrite /SE.expand_lets_ctx /SE.expand_lets_k_ctx /expand_lets_ctx /expand_lets_k_ctx.
  erewrite trans_subst_context.
  erewrite trans_extended_subst; tea.
  erewrite trans_lift_context; tea.
  rewrite context_assumptions_map map_length //.
  erewrite <- on_free_vars_ctx_lift_context; tea.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0; tea. 
Qed.

Lemma trans_inds ind u mdecl : 
  map trans (PCUICCases.inds (inductive_mind ind) u (SE.ind_bodies mdecl)) = 
  inds (inductive_mind ind) u (ind_bodies (trans_minductive_body mdecl)).
Proof.
  rewrite PCUICCases.inds_spec inds_spec.
  rewrite map_rev map_mapi. simpl.
  f_equal. rewrite mapi_mapi. apply mapi_ext => n //.
Qed.

Lemma trans_cstr_branch_context p i ci mdecl cdecl :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)) = 
  cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl).
Proof.
  move=> onpars onargs.
  rewrite /PCUICCases.cstr_branch_context /cstr_branch_context.
  erewrite trans_expand_lets_ctx; tea.
  erewrite trans_subst_context; tea.
  erewrite trans_inds.
  rewrite -(PCUICContexts.expand_lets_smash_context _ []).
  f_equal.
  rewrite PCUICContexts.smash_context_subst_empty.
  f_equal => //. now cbn; rewrite map_length.
  eapply (inds_is_open_terms []).
  eapply on_free_vars_ctx_subst_context. len. exact onargs.
  eapply (inds_is_open_terms []).
Qed.

Lemma trans_cstr_branch_context_inst p i ci mdecl cdecl u :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)@[u]) = 
  (cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl))@[u].
Proof.
  move=> onps onargs.
  rewrite trans_subst_instance_ctx -(PCUICUnivSubstitution.subst_instance_smash _ _ []). 
  rewrite (trans_cstr_branch_context p i) //.
Qed.

Lemma map2_set_binder_name_alpha (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  All2 (compare_decls eq eq) Δ Δ' ->
  All2 (compare_decls eq eq) (map2 set_binder_name nas Δ) Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  constructor; auto. destruct r; subst; cbn; constructor; auto;
  now transitivity na.
Qed.

Notation eq_names := (All2 (fun x y => x = (decl_name y))).

Lemma eq_names_subst_context nas Γ s k : 
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * cbn; auto. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance nas Γ u : 
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map2_set_binder_name_alpha_eq (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => x = (decl_name y)) nas Δ' ->
  All2 (compare_decls eq eq) Δ Δ' ->
  (map2 set_binder_name nas Δ) = Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  f_equal; auto. destruct r; subst; cbn; auto.
Qed.

Require Import PCUICContexts.

Lemma trans_inst_case_branch_context p pred i br ci mdecl cdecl :
  let pred' := PCUICAst.map_predicate id trans trans (map_context trans) pred in
  wf_branch cdecl br ->
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
    (cstr_args cdecl) ->
  on_free_vars_terms p pred.(pparams) ->
  on_free_vars_ctx p br.(bcontext) ->
  (* on_free_vars_ctx p cdecl.(cstr_args) -> *)
  All2 (compare_decls eq eq) br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  (case_branch_context ci
    (trans_minductive_body mdecl) pred' (forget_types (smash_context [] br.(bcontext))) (trans_constructor_body i mdecl cdecl)) =
    (smash_context [] (trans_local (inst_case_branch_context pred br))).
Proof.
  intros p' wfbr onindpars onargs onpars onbctx.
  rewrite /inst_case_branch_context.
  rewrite /inst_case_context.
  rewrite /case_branch_context /case_branch_context_gen.
  rewrite (trans_subst_context p p).
  { rewrite on_free_vars_ctx_subst_instance //. }
  { rewrite [on_free_vars_terms _ _]forallb_rev //. }
  intros eq.
  rewrite map_rev.
  rewrite PCUICContexts.smash_context_subst_empty.
  eapply map2_set_binder_name_alpha_eq.
  { apply eq_names_subst_context.
    eapply All2_map_left.
    rewrite -(trans_smash_context p []) //.
    { rewrite on_free_vars_ctx_subst_instance //. }
    eapply All2_map_right.
    rewrite -(PCUICUnivSubstitution.subst_instance_smash _ _ []).
    eapply All2_map_right; cbn.
    eapply All2_refl. intros. reflexivity. }
  eapply alpha_eq_subst_context.
  eapply alpha_eq_subst_instance in eq.
  symmetry in eq.
  eapply alpha_eq_trans in eq.
  rewrite -(trans_cstr_branch_context_inst p i) //.
  eapply alpha_eq_smash_context. exact eq.
Qed.

Lemma context_assumptions_map2_set_binder_name nas Γ :
  #|nas| = #|Γ| ->
  context_assumptions (map2 set_binder_name nas Γ) = context_assumptions Γ.
Proof.
  induction Γ in nas |- *; destruct nas; simpl; auto; try discriminate.
  intros [=]. destruct (decl_body a); auto.
  f_equal; auto.
Qed.

Require Import PCUICSpine.

(* Lemma case_branch_context_assumptions ind mdecl cdecl p (br : branch term) :
  Forall2 (fun na decl => eq_binder_annot na decl.(decl_name)) br.(bcontext) (cstr_args cdecl) ->
  context_assumptions (case_branch_context ind mdecl cdecl p br) = context_assumptions (cstr_args cdecl).
Proof.
  rewrite /case_branch_context /case_branch_context_gen.
  intros Hforall.
  rewrite context_assumptions_map2_set_binder_name. len.
  eapply (Forall2_length Hforall).
  now do 3 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context ?context_assumptions_subst_instance 
    /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
Qed. *)

Lemma cstr_branch_context_assumptions ci mdecl cdecl : 
  SE.context_assumptions (PCUICCases.cstr_branch_context ci mdecl cdecl) =
  SE.context_assumptions (SE.cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /PCUICEnvironment.expand_lets_ctx
    /PCUICEnvironment.expand_lets_k_ctx.
  now do 2 rewrite !SE.context_assumptions_subst_context ?SE.context_assumptions_lift_context.
Qed.

Lemma trans_reln l p Γ : map trans (SE.reln l p Γ) = 
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; auto.
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (SE.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Lemma trans_ind_predicate_context ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  trans_local (PCUICCases.ind_predicate_context ci mdecl idecl) = 
  (ind_predicate_context ci (trans_minductive_body mdecl)
      (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite /ind_predicate_context /Ast.ind_predicate_context /=.
  rewrite /trans_decl /=. f_equal.
  f_equal. rewrite trans_mkApps /=. f_equal.
  rewrite trans_to_extended_list trans_local_app /to_extended_list.
  f_equal. f_equal.
  now rewrite (trans_smash_context xpred0).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
Qed.

Lemma trans_ind_predicate_context_eq p ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  All2 (compare_decls eq eq) (PCUICAst.pcontext p)
    (PCUICCases.ind_predicate_context ci mdecl idecl) -> 
  All2
    (λ (x : binder_annot name) (y : context_decl),
       eq_binder_annot x (decl_name y))
    (map decl_name (trans_local (PCUICAst.pcontext p)))
    (ind_predicate_context ci (trans_minductive_body mdecl)
       (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite -trans_ind_predicate_context //.
  intros. eapply All2_map, All2_map_left.
  solve_all.
  destruct X; cbn; subst; auto.
Qed.

Lemma trans_cstr_branch_context_eq ci mdecl cdecl p i br :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
  (cstr_args cdecl) ->
  All2 (compare_decls eq eq) (PCUICAst.bcontext br) 
    (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  All2 (compare_decls eq eq)
    (bcontext (trans_branch p (map_branch trans (map_context trans) br)))
    (cstr_branch_context ci (trans_minductive_body mdecl)
      (trans_constructor_body i mdecl cdecl)).
Proof.
  intros clpars clargs a.
  rewrite -(trans_cstr_branch_context xpred0) //.
  cbn. eapply alpha_eq_smash_context.
  eapply All2_map. solve_all.
  destruct X; subst; auto; constructor; cbn; auto.
Qed.

Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' :
  map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma map2_map_map {A B C D} (f : A -> B -> C) (g : D -> B) l l' :
  map2 (fun x y => f x (g y)) l l' = map2 f l (map g l').
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma trans_set_binder na y :
  trans_decl (PCUICEnvironment.set_binder_name na y) = set_binder_name na (trans_decl y).
Proof.
  destruct y as [na' [b|] ty]; cbn; auto.
Qed.

Require Import Morphisms.
Instance map2_Proper {A B C} : Morphisms.Proper (pointwise_relation A (pointwise_relation B (@eq C)) ==> eq ==> eq ==> eq) map2.
Proof.
  intros f g Hfg ? ? -> ? ? ->.
  eapply PCUICNameless.map2_ext, Hfg.
Qed.

Lemma map2_set_binder_name_eq nas Δ Δ' :
  All2 (compare_decls eq eq) Δ Δ' ->
  map2 set_binder_name nas Δ = map2 set_binder_name nas Δ'.
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  rewrite IHX. destruct r; subst; cbn; reflexivity.
Qed.

Lemma eq_binder_trans (nas : list aname) (Δ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas (trans_local Δ).
Proof.
  intros. eapply All2_map_right, All2_impl; tea.
  cbn. intros x y H. destruct y; apply H.
Qed.

Lemma trans_local_set_binder nas Γ : 
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  map2 set_binder_name nas (trans_local Γ).
Proof.
  rewrite /trans_local map_map2.
  setoid_rewrite trans_set_binder.
  now rewrite map2_map_map.
Qed.

Lemma All2_eq_binder_lift_context (l : list (binder_annot name)) n k (Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.lift_context n k Γ).
Proof.
  induction 1; cbn; rewrite ?PCUICLiftSubst.lift_context_snoc //; constructor; auto.
Qed.

Lemma All2_eq_binder_expand_lets_ctx (l : list (binder_annot name)) (Δ Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.expand_lets_ctx Δ Γ).
Proof.
  intros a.
  now eapply All2_eq_binder_subst_context, All2_eq_binder_lift_context.
Qed.

Lemma trans_local_set_binder_name_eq nas Γ Δ :
  All2 (PCUICEquality.compare_decls eq eq) Γ Δ ->
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  trans_local (map2 PCUICEnvironment.set_binder_name nas Δ).
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  f_equal. destruct r; subst; f_equal.
  apply IHX.
Qed.

Lemma map2_trans l l' :
  map2
  (λ (x : aname) (y : PCUICEnvironment.context_decl),
      trans_decl (PCUICEnvironment.set_binder_name x y)) l l' =
  map2 (fun (x : aname) (y : PCUICEnvironment.context_decl) =>
    set_binder_name x (trans_decl y)) l l'.
Proof.
  eapply map2_ext.
  intros x y. rewrite /trans_decl. now destruct y; cbn.
Qed.

Lemma on_free_vars_ind_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl → 
  on_free_vars_ctx (closedP (context_assumptions (ind_params mdecl)) xpredT) 
    (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli.
  rewrite <- closedn_ctx_on_free_vars.
  eapply PCUICClosed.closed_ind_predicate_context; tea.
  eapply (PCUICClosed.declared_minductive_closed (proj1 decli)).
Qed.

Lemma closed_ctx_is_closed_context Γ :
  closed_ctx Γ -> is_closed_context Γ.
Proof.
  now rewrite closedn_ctx_on_free_vars PCUICConfluence.closedP_shiftnP shiftnP0.
Qed.
#[local] Hint Resolve closed_ctx_is_closed_context : pcuic.
#[local] Hint Resolve declared_inductive_closed_params : pcuic.

Lemma closedn_ctx_on_free_vars (Γ Δ : context) :
  closedn_ctx #|Γ| Δ -> on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ.
Proof.
  rewrite closedn_ctx_on_free_vars PCUICConfluence.closedP_shiftnP //.
Qed.

#[local] Hint Resolve closedn_ctx_on_free_vars : pcuic.

Lemma declared_inductive_closed_indices {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  closedn_ctx #|ind_params mdecl| (ind_indices idecl).
Proof.
  move/declared_inductive_closed_pars_indices.
  rewrite closedn_ctx_app /= => /andP[] //.
Qed.
#[local] Hint Resolve declared_inductive_closed_indices : pcuic.

Lemma trans_case_predicate_context {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} Γ ci mdecl idecl p : 
  S.declared_inductive Σ ci mdecl idecl ->
  S.consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p) → 
  let parctx := (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p] in
  PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p)
      (List.rev (PCUICAst.pparams p))
      (PCUICEnvironment.smash_context [] parctx) ->
  wf_predicate mdecl idecl p ->
  let p' := map_predicate id trans trans trans_local p in  
  (case_predicate_context ci (trans_minductive_body mdecl) (trans_one_ind_body mdecl (inductive_ind ci) idecl) p') =
  (trans_local (PCUICCases.case_predicate_context ci mdecl idecl p)).
Proof.
  intros.
  rewrite /case_predicate_context /PCUICCases.case_predicate_context.
  rewrite /case_predicate_context_gen /PCUICCases.case_predicate_context_gen.
  rewrite /trans_local map_map2 map2_trans.
  rewrite -PCUICUnivSubstitution.map2_map_r. f_equal.
  rewrite /p' /=. now rewrite forget_types_map_context.
  rewrite /pre_case_predicate_context_gen /inst_case_context.
  rewrite /PCUICCases.pre_case_predicate_context_gen /PCUICCases.inst_case_context.
  rewrite [map _ _](trans_subst_context (shiftnP (context_assumptions mdecl.(ind_params)) xpred0)
    (shiftnP #|Γ| xpred0)).
  rewrite -PCUICConfluence.closedP_shiftnP on_free_vars_ctx_subst_instance.
  eapply (on_free_vars_ind_predicate_context H).
  now eapply inst_subslet, subslet_open in X.
  rewrite map_rev. f_equal.
  rewrite trans_subst_instance_ctx. 
  rewrite trans_ind_predicate_context; pcuic.
Qed.

Lemma OnOne2All2i_OnOne2All {A B : Type} (l1 l2 : list A) (l3 : list B) 
  (R1 : A → A → Type) (R2 : nat → B → A → Type) (n : nat) (R3 : B -> A -> A -> Type) :
  OnOne2 R1 l1 l2 → 
  All2i R2 n l3 l1 → 
  (forall (n0 : nat) (x y : A) (z : B), R1 x y → R2 n0 z x → R3 z x y) → OnOne2All R3 l3 l1 l2.
Proof.
  induction 1 in n, l3 |- *; intros H; depelim H.
  intros H'. constructor. now eapply H'. eapply (All2i_length _ _ _ _ H).
  intros H'. constructor. now eapply IHX.
Qed.

Lemma trans_eq_binder_annot (Γ : list aname) Δ :
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ ->
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ (trans_local Δ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma map_context_trans Γ : map_context trans Γ = trans_local Γ.
Proof.
  rewrite /map_context /trans_local /trans_decl.
  eapply map_ext. intros []; reflexivity.
Qed.

Lemma trans_bcontext p br :  
  (bcontext (trans_branch p (map_branch trans (map_context trans) br))) = smash_context [] (trans_local (bcontext br)).
Proof.
  now cbn.
Qed.

Lemma OnOne2All_map2_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : B -> I -> I') (f : A -> B) :
  OnOne2All (fun i x y => P (g (f x) i) (f x) (f y)) i l l' -> OnOne2All P (map2 g (map f l) i) (map f l) (map f l').
Proof.
  induction 1; simpl; constructor; try congruence. len.
  now rewrite map2_length !map_length. 
Qed.

Lemma wt_on_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t} : wt Σ Γ t -> on_free_vars (shiftnP #|Γ| xpred0) t.
Proof.
  intros [T wt]. now eapply subject_is_open_term in wt.
Qed.

Ltac fuse_shifts :=
  match goal with
  [ H : is_true (on_free_vars (shiftnP 1 (shiftnP _ _)) _) |- _ ] => 
    rewrite -> shiftnP_add in H; cbn in H
  end.

Ltac tofvs := repeat match goal with [ H : wt _ _ _ |- _ ] => apply wt_on_free_vars in H end; 
  try inv_on_free_vars; repeat fuse_shifts. 

#[local] Hint Extern 3 (is_true (_ && true)) => rewrite andb_true_r : pcuic.

Lemma skipn_map_length {A B} {n} {f : A -> B} {l} : #|skipn n (map f l)| = #|skipn n l|.
Proof.
  now rewrite !List.skipn_length map_length.
Qed.

Lemma trans_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) {wfΣ : PCUICTyping.wf Σ} Γ T U :
  red1 Σ Γ T U ->
  wt Σ Γ T ->
  red1 (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *; intros wt;
    match goal with 
    | |- context [tCase _ _ _ _] => idtac
    | _ => eapply wt_inv in wt; tea; cbn in wt; repeat outtimes
    end;
    try solve [econstructor; eauto].
  
  - simpl. tofvs.
    rewrite (trans_subst_ctx Γ) /=; pcuic. constructor.
    
  - destruct wt. tofvs. rewrite (trans_subst_ctx Γ); pcuic. repeat constructor.

  - destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.
    rewrite (trans_lift _ (shiftnP #|skipn (S i) Γ| xpred0)); eauto.
    eapply nth_error_All_local_env in wt0; tea. cbn in wt0.
    now eapply subject_is_open_term.
    constructor. now rewrite nth_error_map Heq.
    
  - pose proof (wt_on_free_vars wt).
    inv_on_free_vars.
    destruct wt as [s Hs].
    eapply inversion_Case in Hs as [mdecl [idecl [decli [indices [[] ?]]]]].
    epose proof (PCUICValidity.inversion_mkApps scrut_ty) as [? [hc hsp]]; tea.
    eapply inversion_Construct in hc as (mdecl'&idecl'&cdecl&wfΓ&declc&cu&tyc); tea.
    destruct (PCUICWeakeningEnv.declared_inductive_inj decli (proj1 declc)) as [-> ->]. 2:auto.
    rewrite trans_mkApps /=.
    have lenskip : #|skipn (ci_npar ci) (map trans args)| =
      context_assumptions (cstr_args cdecl).
    { destruct (Construct_Ind_ind_eq _ scrut_ty declc) as [[] _].
      rewrite skipn_length. len. rewrite -eq_npars. lia. len.
      rewrite -eq_npars. rewrite e0. lia. }
    eapply All2i_nth_error_r in brs_ty; tea.
    destruct brs_ty as [cdecl' [Hcdecl' [bctxeq [wfbrctx [hbody hbodyty]]]]].
    rewrite (proj2 declc) in Hcdecl'. noconf Hcdecl'.
    have lenbctx : context_assumptions (cstr_args cdecl) = context_assumptions (bcontext br).
    { rewrite (alpha_eq_context_assumptions _ _ bctxeq).
      rewrite cstr_branch_context_assumptions. lia. } 
    relativize (trans (iota_red _ _ _ _)).
    eapply red_iota; tea; eauto. all:auto.
    * rewrite !nth_error_map H; reflexivity.
    * rewrite (PCUICSubstitution.context_assumptions_smash_context []) /= context_assumptions_map. lia.
    * rewrite /iota_red. rewrite skipn_map_length in lenskip.
      have oninst : on_free_vars_ctx (shiftnP #|Γ| xpred0) (inst_case_branch_context p br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).
        eapply typing_wf_local in hbody. eapply wf_local_closed_context in hbody.
        rewrite -> PCUICConfluence.on_free_vars_ctx_app in hbody.
        move/andP: hbody => [] //. }
      have onb : on_free_vars (shiftnP #|inst_case_branch_context p br| (shiftnP #|Γ| xpred0)) (bbody br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).   
        eapply subject_is_open_term in hbody. len in hbody. rewrite shiftnP_add //. }
      rewrite (trans_subst_ctx Γ).
      { len. rewrite lenskip.
        rewrite -shiftnP_add.
        eapply on_free_vars_expand_lets_k => //.
        rewrite /inst_case_branch_context /inst_case_context.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance. lia. }
      { rewrite forallb_rev forallb_skipn //. 
        rewrite on_free_vars_mkApps in p3. move: p3 => /= //. }
      rewrite map_rev map_skipn. f_equal.
      rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
      cbn -[expand_lets].
      
      erewrite expand_lets_eq => //.
      rewrite (trans_inst_case_branch_context (shiftnP #|Γ| xpred0)) => //.
      eapply Forall2_All2 in wf_brs. eapply All2_nth_error in wf_brs; tea.
      eapply declc. reflexivity.

  - simpl. rewrite !trans_mkApps /=.
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. elimtype False; cbn in H1. lia.
    cbn -[mkApps].
    eapply TT.red_fix. 
    apply trans_unfold_fix; eauto.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    discriminate.
    
  - rewrite trans_mkApps.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply TT.red_cofix_case; eauto.

  - rewrite !trans_mkApps.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply TT.red_cofix_proj; eauto.
    
  - rewrite trans_subst_instance. econstructor.
    apply (trans_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body0.

  - rewrite trans_mkApps; eauto with wf.
    simpl. constructor; now rewrite nth_error_map H.
  
  - destruct wt as []; constructor; auto.
  - destruct wt as []; constructor; auto.
  - destruct wt as []; constructor; auto.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply OnOne2_All_mix_left in X; tea.
    constructor.
    eapply OnOne2_map. solve_all.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto. now eapply trans_declared_inductive.
    cbn -[case_predicate_context].
    eapply red1_alpha_eq. eapply IHX.
    { destruct w1 as [sr hs]; exists sr.
      eapply PCUICContextConversion.context_conversion; tea.
      eapply PCUICSafeLemmata.wf_inst_case_context; tea.
      destruct w2. pcuic.
      rewrite /inst_case_context.
      apply compare_decls_conv.
      eapply All2_app. 2:{ reflexivity. }
      eapply compare_decls_eq_context. 
      apply (PCUICAlpha.inst_case_predicate_context_eq (ind:=ci) w).
      cbn. apply compare_decls_eq_context. now symmetry. }
    rewrite [trans_local _]map_app.
    eapply All2_app; [|reflexivity].
    symmetry. etransitivity.
    rewrite (trans_case_predicate_context _ _ _ _ p d c0 s w).
    reflexivity.
    eapply alpha_eq_trans.
    eapply All2_fold_All2, PCUICAlpha.inst_case_predicate_context_eq => //.
    symmetry. now eapply All2_fold_All2.

  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto.
  
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    econstructor; eauto.
    eapply trans_declared_inductive; tea.
    rewrite /case_branches_contexts.
    apply OnOne2All_map2_map_all. cbn.
    apply OnOne2All_map_all.
    eapply OnOne2All2i_OnOne2All; tea.
    intros i br br' ctor.
    simpl. intros [[red IHred] eqctx] [wfrel wtbody].
    unfold on_Trel. split => //. 2:cbn; now rewrite eqctx.
    rewrite [map2 set_binder_name _ _](trans_inst_case_branch_context _ _ ci mdecl ctor) => //.
    rewrite -[_ ++ _]trans_local_app.
    eapply IHred.
    destruct w4 as [s' Hs]. exists s'.
    eapply PCUICContextConversion.context_conversion; tea.
    eapply wf_local_alpha; tea. pcuic.
    now eapply compare_decls_conv.

  - eapply red1_mkApp; auto. eapply trans_wf; tea.
  - eapply (red1_mkApps_r _ _ _ [_] [_]); auto.
    * eapply trans_wf; tea.
    * repeat constructor. eapply trans_wf; tea.
    * constructor; auto.
  
  - constructor. 
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map. solve_all.
    red; intuition auto. destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - eapply TT.fix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    unfold on_Trel in *.
    eapply OnOne2_map. solve_all. unfold on_Trel. cbn. split => //.
    simpl. rewrite -trans_fix_context.
    now rewrite /trans_local map_app in X.
    destruct x, y; simpl in *. noconf b0.
    reflexivity.
    
  - constructor. 
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map. solve_all.
    red; intuition auto. destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - apply TT.cofix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map; solve_all.
    red. destruct x, y; simpl in *. noconf b0.
    intuition auto.
    rewrite /trans_local map_app in X.
    now rewrite -trans_fix_context.
Qed.

Lemma trans_R_global_instance Σ Re Rle gref napp u u' :
  PCUICEquality.R_global_instance Σ Re Rle gref napp u u' ->
  TermEquality.R_global_instance (trans_global_decls Σ) Re Rle gref napp u u'.
Proof.
  unfold PCUICEquality.R_global_instance, PCUICEquality.global_variance.
  unfold TermEquality.R_global_instance, TermEquality.global_variance.
  destruct gref; simpl; auto.
  - unfold S.lookup_inductive, S.lookup_minductive.
    unfold lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite trans_destr_arity.
    destruct PCUICAstUtils.destArity as [[ctx ps]|] => /= //.
    now rewrite context_assumptions_map.
  - unfold S.lookup_constructor, S.lookup_inductive, S.lookup_minductive.
    unfold lookup_constructor, lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed. 

Lemma trans_eq_context_gen_eq_binder_annot Γ Δ :
  eq_context_gen eq eq Γ Δ ->
  All2 eq_binder_annot (map decl_name (trans_local Γ)) (map decl_name (trans_local Δ)).
Proof.
  move/All2_fold_All2.
  intros; do 2 eapply All2_map. solve_all.
  destruct X; cbn; auto.
Qed.

Lemma trans_eq_term_upto_univ {cf} :
  forall Σ Re Rle t u napp,
    PCUICEquality.eq_term_upto_univ_napp Σ Re Rle napp t u ->
    TermEquality.eq_term_upto_univ_napp (trans_global_decls Σ) Re Rle napp (trans t) (trans u).
Proof.
  intros Σ Re Rle t u napp e.
  induction t using term_forall_list_ind in Rle, napp, u, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: try solve [
    repeat constructor ;
    match goal with
    | ih : forall Rle u (napp : nat), _ |- _ =>
      eapply ih ; auto
    end
  ].
  1,6,7: try solve [ constructor; solve_all ].
  all: try solve [ constructor; now eapply trans_R_global_instance ].
  - eapply (TermEquality.eq_term_upto_univ_mkApps _ _ _ _ _ [_] _ [_]); simpl; eauto.
  - destruct X1 as [Hpars [Huinst [Hctx Hret]]].
    destruct X as [IHpars [IHctx IHret]].
    constructor; cbn; auto. solve_all.
    red in X0.
    eapply trans_eq_context_gen_eq_binder_annot in Hctx.
    now rewrite !map_context_trans.
    red in X0. solve_all_one.
    eapply trans_eq_context_gen_eq_binder_annot in a.
    now rewrite !map_context_trans.
  - destruct p as [? []]; constructor.
Qed.

Lemma trans_leq_term {cf} Σ ϕ T U :
  PCUICEquality.leq_term Σ ϕ T U ->
  TermEquality.leq_term (trans_global_decls Σ) ϕ (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ ; eauto.
Qed.

Section wtcumul.
  Import PCUICAst PCUICTyping PCUICEquality.
  Record wt_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) (Γ : PCUICEnvironment.context) T U := 
  { wt_red1_red1 : PCUICReduction.red1 Σ Γ T U;
    wt_red1_dom : isType Σ Γ T;
    wt_red1_codom : isType Σ Γ U }.

  Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

  Inductive wt_cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | wt_cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_l t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ |-- v <= u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_r t u v : Σ ;;; Γ |-- t <= v -> wt_red1 Σ Γ u v -> Σ ;;; Γ |-- t <= u
  where " Σ ;;; Γ |-- t <= u " := (wt_cumul Σ Γ t u) : type_scope.
    
  Lemma cumul_decorate {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    isType Σ Γ T -> isType Σ Γ U ->
    cumul Σ Γ T U ->
    wt_cumul Σ Γ T U.
  Proof.
    intros ht hu.
    induction 1. 
    - constructor. auto.
    - pose proof (isType_red1 ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (isType_red1 hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.
End wtcumul.

Lemma trans_cumul {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wt_cumul Σ Γ T U ->
  TT.cumul (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1. 
  - constructor; auto.
    eapply trans_leq_term in l.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as [s hs]; now eexists.
    econstructor 2; tea.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as [s hs]; now eexists.
    econstructor 3; tea.
Qed.

Definition TTwf_local {cf} Σ Γ := TT.All_local_env (TT.lift_typing TT.typing Σ) Γ.

Lemma trans_wf_local' {cf} :
  forall (Σ : SE.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : PCUICAst.term) _ =>
           TT.typing (trans_global Σ0) (trans_local Γ0) (trans t) (trans T))
    in
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct tu. exists x. eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x. auto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : SE.global_env_ext) Γ b ty =>
              ST.typing Σ Γ b ty × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
        Γ ->
  TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red. red in t1. destruct t1. eapply t2.
Qed.

Lemma trans_branches {cf} Σ Γ brs btys ps:
  All2
    (fun br bty : nat × PCUICAst.term =>
      (((br.1 = bty.1 × ST.typing Σ Γ br.2 bty.2)
        × TT.typing (trans_global Σ) (trans_local Γ) (trans br.2) (trans bty.2))
      × ST.typing Σ Γ bty.2 (PCUICAst.tSort ps))
      × TT.typing (trans_global Σ) (trans_local Γ) (trans bty.2)
        (trans (PCUICAst.tSort ps))) brs btys ->
  All2
    (fun br bty : nat × term =>
    (br.1 = bty.1 × TT.typing (trans_global Σ) (trans_local Γ) br.2 bty.2)
    × TT.typing (trans_global Σ) (trans_local Γ) bty.2 (tSort ps))
    (map (on_snd trans) brs) (map (fun '(x, y) => (x, trans y)) btys).
Proof.
  induction 1;cbn.
  - constructor.
  - constructor.
    + destruct r as [[[[] ] ] ].
      destruct x,y.
      cbn in *.
      repeat split;trivial.
    + apply IHX.
Qed.

Lemma trans_mfix_All {cf} Σ Γ mfix:
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : SE.global_env_ext)
          (Γ : SE.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (SE.app_context Γ (SE.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) mfix)).
Proof.
  intros.
  rewrite <- trans_fix_context.
  match goal with
  |- TTwf_local _ ?A =>
      replace A with (trans_local (SE.app_context Γ (SE.fix_context mfix)))
  end.
  2: {
    unfold trans_local, SE.app_context.
    now rewrite map_app.
  }

  induction X;cbn;constructor;auto;cbn in *.
  - destruct t0 as (?&?&?).
    exists x.
    apply t1.
  - destruct t0 as (?&?&?).
    eexists;eassumption.
  - destruct t1.
    assumption.
Qed.

Lemma trans_mfix_All2 {cf} Σ Γ mfix xfix:
  All
  (fun d : def PCUICAst.term =>
    (ST.typing Σ (SE.app_context Γ (SE.fix_context xfix))
    (dbody d)
    (S.lift0 #|SE.fix_context xfix| (dtype d)))
    × TT.typing (trans_global Σ)
      (trans_local (SE.app_context Γ (SE.fix_context xfix)))
      (trans (dbody d))
      (trans
          (S.lift0 #|SE.fix_context xfix|
            (dtype d)))) mfix ->
  All
    (fun d : def term =>
    TT.typing (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) xfix)) 
    (dbody d) (T.lift0 #|TT.fix_context (map (map_def trans trans) xfix)| (dtype d))) 
    (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - simpl; constructor.
    + destruct p as [].
      unfold app_context, SE.app_context in *.
      unfold trans_local in t0.
      rewrite map_app trans_fix_context in t0.
      rewrite trans_dbody trans_lift trans_dtype in t0.
      replace(#|SE.fix_context xfix|) with
          (#|TT.fix_context (map(map_def trans trans) xfix)|) in t0.
        2:now rewrite TT.fix_context_length map_length fix_context_length.
        now destruct x.
    + auto.
Qed.

Lemma All_over_All {cf} Σ Γ wfΓ :
  ST.All_local_env_over ST.typing
    (fun (Σ : SE.global_env_ext) (Γ : SE.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Σ Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : SE.global_env_ext) (Γ0 : SE.context)
          (b ty : PCUICAst.term) =>
        ST.typing Σ0 Γ0 b ty
        × TT.typing (trans_global Σ0) (trans_local Γ0) (trans b) (trans ty)) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  - constructor.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
    + cbn in *.
      split;eassumption.
Qed.

Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := decompose_prod_assum Γ t in
    AstUtils.decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  all: simpl in *.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt2 in e as e'. apply e'.
  - eapply IHt3 in e as e'. assumption.
  - noconf e. simpl.
    now destruct (mkApp_ex (trans t1) (trans t2)) as [f [args ->]].
  - noconf e. now destruct prim as [? []] => /=.
Qed.

Lemma trans_isApp t : PCUICAst.isApp t = false -> Ast.isApp (trans t) = false.
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_nisApp t : ~~ PCUICAst.isApp t -> ~~ Ast.isApp (trans t).
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_destInd t : ST.destInd t = TT.destInd (trans t).
Proof.
  destruct t => //. simpl.
  now destruct (mkApp_ex (trans t1) (trans t2)) as [f [u ->]].
  now destruct prim as [? []].
Qed.

Lemma trans_decompose_app t : 
  let '(hd, args) := decompose_app t in 
  AstUtils.decompose_app (trans t) = (trans hd, map trans args).
Proof.
  destruct (decompose_app t) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps.
  apply AstUtils.decompose_app_mkApps.
  now rewrite trans_isApp.
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B'} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') l t,
    (forall i x t, f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' f g' g l t.
  unfold mapi. generalize 0.
  intros n h e.
  induction l in n, e, t |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n a) eqn:e'. 2: discriminate.
    eapply h in e' as h'.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHl in e''. rewrite e''. now noconf e.
Qed.

Lemma trans_check_one_fix mfix :
  TT.check_one_fix (map_def trans trans mfix) = ST.check_one_fix mfix.
Proof.
  unfold ST.check_one_fix, TT.check_one_fix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => /= ->.
  rewrite -(trans_smash_context []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error => /= //.
  move: (trans_decompose_app (decl_type c)).
  destruct decompose_app => /=.
  simpl. destruct c. simpl. intros ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_fix mfix :
  map (fun x => TT.check_one_fix (map_def trans trans x)) mfix = 
  map ST.check_one_fix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix :
  TT.check_one_cofix (map_def trans trans mfix) = ST.check_one_cofix mfix.
Proof.
  unfold ST.check_one_cofix, TT.check_one_cofix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => -> /=.
  move: (trans_decompose_app p).
  destruct decompose_app => /= ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_cofix mfix :
  map (fun x => TT.check_one_cofix (map_def trans trans x)) mfix = 
  map ST.check_one_cofix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind Σ k f :
  ST.check_recursivity_kind Σ k f = TT.check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, TT.check_recursivity_kind.
  rewrite trans_lookup.
  destruct SE.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ mfix :
  TT.wf_fixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_fixpoint Σ mfix.
Proof.
  unfold ST.wf_fixpoint, TT.wf_fixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_fix.
  destruct map_option_out as [[]|] => //.
  now rewrite trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  TT.wf_cofixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_cofixpoint Σ mfix.
Proof.
  unfold ST.wf_cofixpoint, TT.wf_cofixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_cofix.
  destruct map_option_out as [[]|] => //.
  now rewrite trans_check_rec_kind.
Qed.

Lemma type_mkApps_napp `{checker_flags} Σ Γ f u T T' :
  ~~ isApp f ->
  TT.typing Σ Γ f T ->
  TT.typing_spine Σ Γ T u T' ->
  TT.typing Σ Γ (mkApps f u) T'.
Proof.
  intros hf hty hsp.
  depelim hsp. simpl; auto.
  rewrite mkApps_tApp.
  destruct f => //. congruence.
  econstructor; eauto.
  destruct f => //. congruence.
  econstructor; eauto.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).


(* This version of typing spine allows to not require [isType] assumptions at the end of the 
  application chain, which is crucial to be able to build a spine that both encompasses PCUIC's 
  applications and mimicks the typing rule of Template. Otherwise we would only model:

  |- tProd na A B : s
  |- f : tProd na A B
  |- u : A
  *** |- B [0 := u] : s ***  <- this last hypothesis is problematic, it's not present in PCUIC
  ------------------------      derivations for example.
  |- tApp f u : B [0 := u]

  The typing_spine_nil constructor allows to stack cumulativity steps using transitivity of cumulativity,
  following from confluence.

  In the end a typing derivation for an application that can mix application and cumulativity steps at any
  point: 

  tApp (tApp f u) v : T' can be translated to

  typing_spine fty [u; v] T'
*)  

Import PCUICAst PCUICLiftSubst PCUICTyping.
Inductive typing_spine {cf} (Σ : global_env_ext) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_eq ty : typing_spine Σ Γ ty [] ty

| type_spine_nil ty ty' :
  isType Σ Γ ty' ->
  Σ ;;; Γ |- ty <= ty' ->
  typing_spine Σ Γ ty [] ty'

| type_spine_cons hd tl na A B T B' :
  isType Σ Γ (tProd na A B) ->
  Σ ;;; Γ |- T <= tProd na A B ->
  Σ ;;; Γ |- hd : A ->
  typing_spine Σ Γ (subst10 hd B) tl B' ->
  typing_spine Σ Γ T (hd :: tl) B'.
Derive Signature for typing_spine.

(* The size of a spine is the maximal depth of any typing derivation appearing in it *)
Section Typing_Spine_size.
  Context `{checker_flags}.
  Context {Σ : global_env_ext} {Γ : context}.

  Fixpoint typing_spine_size {t T U} (s : typing_spine Σ Γ t T U) : size :=
  match s with
  | type_spine_eq ty => 0
  | type_spine_nil ty ty' ist cum => typing_size ist.π2
  | type_spine_cons hd tl na A B T B' typrod cumul ty s' =>
    (max (typing_size typrod.π2) (max (typing_size ty) (typing_spine_size s')))%nat
  end.
End Typing_Spine_size.

(* We can weaken a spine by cumulativity, using the type_spine_nil  *)
Lemma typing_spine_weaken_concl {cf:checker_flags} {Σ Γ T args S S'} {wfΣ : wf Σ.1} :
  typing_spine Σ Γ T args S ->
  isType Σ Γ T ->
  Σ ;;; Γ ⊢ S ≤ S' ->
  isType Σ Γ S' ->
  typing_spine Σ Γ T args S'.
Proof.
  intros sp.
  induction sp in S' => tyT cum.
  * constructor; auto. now eapply equality_forget in cum.
  * constructor; auto. eapply (into_equality (le:=true)) in c; fvs.
    eapply (equality_forget (le:=true)). now transitivity ty'.
  * intros isType. econstructor. eauto. eauto. eauto.
    apply IHsp; auto. eapply PCUICArities.isType_apply; tea.
Defined.

(* The size includes the new [isType] hypothesis  *)
Lemma typing_spine_weaken_concl_size {cf:checker_flags} {Σ Γ T args S S'} 
  (wf : wf Σ.1) 
  (sp  :typing_spine Σ Γ T args S)
  (tyT : isType Σ Γ T)
  (Hs : Σ ;;; Γ ⊢ S ≤ S')
  (ist : isType Σ Γ S') :
  typing_spine_size (typing_spine_weaken_concl sp tyT Hs ist) <= 
  max (typing_spine_size sp) (typing_size ist.π2).
Proof.
  induction sp; simpl; auto. lia.
  rewrite - !Nat.max_assoc. 
  specialize (IHsp (PCUICArities.isType_apply i t) Hs). lia.
Qed.

Ltac sig := unshelve eexists.

(** We can also append an argument to a spine *without* requiring a typing for the new conclusion type.
  This would be a derivation for a substitution of [B], hence incomparable in depth to the arguments.
  The invariant is witnessed by the spine size being lower than the arguments.
*)
Lemma typing_spine_app {cf:checker_flags} Σ Γ ty args na A B arg
  (wf : wf Σ.1) 
  (isty : isType Σ Γ (tProd na A B))
  (sp : typing_spine Σ Γ ty args (tProd na A B))
  (argd : Σ ;;; Γ |- arg : A) : 
  ∑ sp' : typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}), 
    typing_spine_size sp' <= max (typing_size isty.π2) (max (typing_spine_size sp) (typing_size argd)).
Proof.
  revert arg argd.
  depind sp.
  - intros arg Harg. simpl.
    sig.
    * econstructor; eauto. apply cumul_refl'. 
      constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    sig. 
    * econstructor; eauto. constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    specialize (IHsp wf isty _ Harg) as [sp' Hsp'].
    sig.
    * econstructor. apply i. auto. auto. exact sp'.
    * simpl. lia.
Qed.

(** Likewise, in Template-Coq, we can append without re-typing the result *)
Lemma TT_typing_spine_app {cf:checker_flags} Σ Γ ty T' args na A B arg s :
  TT.typing Σ Γ (T.tProd na A B) (T.tSort s) ->
  TT.typing_spine Σ Γ ty args T' ->
  TT.cumul Σ Γ T' (T.tProd na A B) ->
  TT.typing Σ Γ arg A ->
  TT.typing_spine Σ Γ ty (args ++ [arg]) (T.subst1 arg 0 B).
Proof.
  intros isty H; revert arg.
  remember (T.tProd na A B) as prod.
  revert na A B Heqprod.
  induction H.
  - intros na A B eq arg Harg. simpl. econstructor; eauto. now rewrite <-eq. rewrite <-eq.
    apply Harg.
    constructor.
  - intros na' A' B'' eq arg Harg. simpl.
    econstructor. apply t. auto. auto.
    eapply IHtyping_spine. now rewrite eq. exact eq. apply Harg. apply X.
Defined.

(** This is the central lemma for this translation: 
  any PCUIC typing of an application `t` can be decomposed as 
  a typing of the head of `t` followed by a typing spine for 
  its arguments `l`. *)

Lemma type_app {cf} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) :
  wf Σ.1 ->
  if isApp t then 
    let (f, l) := decompose_app t in 
    ∑ fty (d' : Σ ;;; Γ |- f : fty), 
      ((typing_size d' <= typing_size d) * 
      ∑ (sp : typing_spine Σ Γ fty l T),
        (typing_spine_size sp <= typing_size d))%type
  else True.
Proof.
  intros wfΣ.
  induction d; simpl; auto.
  - destruct (isApp t) eqn:isapp.
    destruct (decompose_app (tApp t u)) eqn:da.
    unfold decompose_app in da.
    simpl in da.
    apply decompose_app_rec_inv' in da as [n [napp [equ eqt]]].
    subst t. clear IHd1 IHd3.
    rewrite PCUICAstUtils.decompose_app_mkApps // in IHd2.
    destruct IHd2 as [fty [d' [sp hd']]].
    exists fty, d'.
    split. lia.
    destruct hd' as [sp' Hsp].
    destruct (typing_spine_app _ _ _ _ _ _ _ _ wfΣ (s; d1) sp' d3) as [appsp Happ].
    simpl in Happ.
    move: appsp Happ. rewrite equ firstn_skipn.
    intros app happ. exists app. lia.

    unfold decompose_app. simpl.
    rewrite PCUICAstUtils.atom_decompose_app. destruct t => /= //.
    eexists _, d2. split. lia.
    unshelve eexists.
    econstructor. exists s; eauto. reflexivity. assumption. constructor.
    simpl. lia.

  - destruct (isApp t) eqn:isapp => //.
    destruct (decompose_app t) eqn:da.
    assert (l <> []).
    { eapply decompose_app_nonnil in da => //. }
    destruct IHd1 as [fty [d' [? ?]]].
    exists fty, d'. split. lia.
    destruct s0 as [sp Hsp].
    unshelve eexists. eapply typing_spine_weaken_concl; eauto. exact (PCUICValidity.validity d').
    exact (into_equality (le:=true) c (wf_local_closed_context (typing_wf_local d'))
      (PCUICSpine.type_is_open_term d1) (PCUICSpine.subject_is_open_term d2)).
    exact (s; d2).
    epose proof (typing_spine_weaken_concl_size wfΣ sp (PCUICValidity.validity d')
      (into_equality (le:=true) c (wf_local_closed_context (typing_wf_local d'))
         (PCUICSpine.type_is_open_term d1) (PCUICSpine.subject_is_open_term d2)) (s; d2)).
    simpl in H0. lia.
Qed.

(** Finally, for each typing spine built above, assuming we can apply the induction hypothesis
  of the translation to any of the typing derivations in the spine, then we can produce a typing
  spine in the n-ary application template-coq spec.

  We have two cases to consider at the "end" of the spine: either we have the same translation of the 
  PCUIC conclusion type, or there is exactly one cumulativity step to get to this type. *)
Lemma make_typing_spine {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ fty l T} 
  (sp : PCUICToTemplateCorrectness.typing_spine Σ Γ fty l T) n 
  (IH : forall t' T' (Ht' : Σ ;;; Γ |- t' : T'), 
      typing_size Ht' <= n -> 
      TT.typing (trans_global Σ) (trans_local Γ) (trans t') (trans T')) :
  isType Σ Γ fty ->
  typing_spine_size sp <= n ->
  ∑ T', TT.typing_spine (trans_global Σ) (trans_local Γ) (trans fty) (map trans l) T' * 
    ((T' = trans T) +
      (TT.cumul (trans_global Σ) (trans_local Γ) T' (trans T) *
       ∑ s, TT.typing (trans_global Σ) (trans_local Γ) (trans T) (T.tSort s)))%type.
Proof.
  induction sp; simpl; intros.
  - exists (trans ty); split.
    * constructor.
    * left; auto.
  - exists (trans ty).
    split. constructor. right.
    split.
    eapply cumul_decorate in c; tea.
    now eapply trans_cumul in c.
    specialize (IH _ _ i.π2 H). now exists i.π1.

  - simpl; intros.
    forward IHsp.
    eapply isType_apply; tea.
    forward IHsp by lia.
    specialize (IH _ _ t) as IHt.
    forward IHt by lia.
    eapply cumul_decorate in c; tea.
    apply trans_cumul in c.
    specialize (IH _ _ i.π2) as IHi.
    forward IHi by lia.
    simpl in IHi.
    destruct IHsp as [T' [Hsp eq]].
    destruct eq. subst T'.
    exists (trans B'). split; auto.
    econstructor.
    eauto.
    apply c.
    apply IHt.
    now rewrite trans_subst in Hsp.
    exists T'. split; auto.
    econstructor.
    eauto. apply c. apply IHt.
    now rewrite trans_subst in Hsp.
Qed.

Lemma it_mkLambda_or_LetIn_app l l' t :
  T.Env.it_mkLambda_or_LetIn (l ++ l') t = T.Env.it_mkLambda_or_LetIn l' (T.Env.it_mkLambda_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma trans_it_mkLambda_or_LetIn Γ T : 
  trans (it_mkLambda_or_LetIn Γ T) = T.Env.it_mkLambda_or_LetIn (trans_local Γ) (trans T).
Proof.
  induction Γ using rev_ind.
  * cbn; auto.
  * rewrite /=. rewrite PCUICAstUtils.it_mkLambda_or_LetIn_app [trans_local _]map_app
      it_mkLambda_or_LetIn_app.
    destruct x as [na [b|] ty] => /=; cbn; now f_equal.
Qed.

Lemma All2i_All2_mapi {A B C D} P (f : nat -> A -> B) (g : nat -> C -> D) l l' : 
  All2i (fun i x y => P (f i x) (g i y)) 0 l l' ->  
  All2 P (mapi f l) (mapi g l').
Proof.
  rewrite /mapi. generalize 0.
  induction 1; constructor; auto.
Qed.

Lemma All2i_sym {A B} (P : nat -> A -> B -> Type) n l l' :
  All2i (fun i x y => P i y x) n l' l ->
  All2i P n l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma eq_names_subst_context_pcuic nas Γ s k : 
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * rewrite subst_context_nil. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance_pcuic nas (Γ : context) u : 
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma trans_case_branch_type {cf} {Σ : global_env_ext} {wfΣ : wf Σ} ci mdecl idecl cdecl i p br :
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_branch cdecl br ->
  All2 (compare_decls eq eq) (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  Ast.case_branch_type ci (trans_minductive_body mdecl)
  (trans_predicate
    (map_predicate id trans trans (map_context trans) p))
  (Env.it_mkLambda_or_LetIn
    (trans_local (case_predicate_context ci mdecl idecl p))
    (Ast.preturn
        (trans_predicate
          (map_predicate id trans trans (map_context trans) p))))
  i (trans_constructor_body cdecl)
  (trans_branch (map_branch trans (map_context trans) br)) =
  (trans_local (case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl),
   trans (case_branch_type ci mdecl idecl p br ptm i cdecl).2).
Proof.
  intros.
  rewrite /Ast.case_branch_type /Ast.case_branch_type_gen /=. f_equal.
  - rewrite [Ast.case_branch_context_gen _ _ _ _ _ _]trans_inst_case_branch_context => //.
    f_equal.
    rewrite /case_branch_context.
    symmetry. 
    erewrite <- PCUICCasesContexts.inst_case_branch_context_eq => //.
  - rewrite trans_mkApps !lengths.
    rewrite trans_lift /ptm trans_it_mkLambda_or_LetIn. f_equal.
    rewrite !map_app (map_map_compose _ _ _ _ trans). f_equal.
    setoid_rewrite trans_subst. 
    rewrite -(map_map_compose _ _ _ trans) map_rev. f_equal.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_expand_lets_k.
    rewrite /id trans_subst_instance_ctx.
    rewrite -(map_map_compose _ _ _ trans). f_equal.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_subst.
    rewrite trans_inds.
    rewrite -(map_map_compose _ _ _ trans). f_equal.
    rewrite !map_map_compose.
    now setoid_rewrite trans_subst_instance.
    cbn. rewrite trans_mkApps map_app; f_equal. f_equal.
    rewrite map_map_compose. setoid_rewrite <- trans_lift.
    rewrite -(map_map_compose _ _ _ _ trans). f_equal.
    now rewrite trans_to_extended_list.
Qed.

From MetaCoq.PCUIC Require Import PCUICClosed PCUICWeakeningEnv.

Theorem pcuic_to_template {cf} (Σ : SE.global_env_ext) Γ t T :
  ST.wf Σ ->
  ST.typing Σ Γ t T ->
  TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros X X0.
  revert Σ X Γ t T X0.
  (** We use an induction principle allowing to apply induction to any subderivation of 
    functions in applications. *)
  apply (typing_ind_env_app_size (fun Σ Γ t T =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ => 
    TT.All_local_env (TT.lift_typing TT.typing (trans_global Σ)) (trans_local Γ))
  );intros.
  - now eapply trans_wf_local_env, All_over_All.
  - rewrite trans_lift.
    rewrite trans_decl_type.
    eapply TT.type_Rel; eauto.
    + now apply map_nth_error.
  - econstructor; eauto.
    destruct u; auto. simpl in H |- *.
    intros l inl. now rewrite <-trans_global_ext_levels.
  - eapply TT.type_Prod;assumption.
  - eapply TT.type_Lambda;eassumption.
  - eapply TT.type_LetIn;eassumption.
  - simpl. rewrite trans_subst10.
    destruct (isApp t) eqn:isapp.
    move: (type_app Ht wfΣ). rewrite isapp.
    destruct (decompose_app t) eqn:da.
    intros [fty [d' [hd' [sp hsp]]]].
    assert (IHt := X3 _ _ d' hd').
    epose proof (make_typing_spine sp (typing_size Ht) X3 (validity d') hsp) as [T' [IH []]].
    * subst T'. rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps AstUtils.mkApps_nested.
      pose proof (AstUtils.mkApps_nested (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption. 
      eapply TT_typing_spine_app. simpl in X1. eapply X1.
      apply IH. apply TT.cumul_refl'.
      apply X5.
    * destruct p as [hcum _].
      rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps AstUtils.mkApps_nested.
      pose proof (AstUtils.mkApps_nested (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption. 
      eapply TT_typing_spine_app. simpl in X1. eapply X1.
      apply IH. apply hcum.
      apply X5.
    * rewrite mkApp_mkApps.
      eapply type_mkApps_napp.
      apply trans_isApp in isapp. rewrite isapp //.
      now simpl in X2.
      econstructor. simpl in X1. eapply X1.
      apply TT.cumul_refl'. assumption. constructor.
  - rewrite trans_subst_instance.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_subst_instance.
    rewrite trans_ind_type.
    eapply TT.type_Ind; eauto.
    + now apply trans_declared_inductive.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_type_of_constructor.
    eapply TT.type_Construct; auto.
    + destruct isdecl. 
      constructor.
      * now apply trans_declared_inductive. 
      * now apply map_nth_error. 
    + now apply trans_consistent_instance_ext.
  - rewrite trans_mkApps map_app.
    simpl.
    rewrite /ptm trans_it_mkLambda_or_LetIn.
    rewrite /predctx.
    have hty := validity X7.
    eapply isType_mkApps_Ind_smash in hty as []; tea.
    erewrite <- trans_case_predicate_context; tea.
    2:{ eapply (wf_predicate_length_pars H0). }
    eapply TT.type_Case; auto.
    + now apply trans_declared_inductive.
    + cbn. now apply trans_ind_predicate_context_eq.
    + cbn. rewrite PCUICToTemplateCorrectness.context_assumptions_map map_length.
      rewrite (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_npars isdecl).
    + cbn. rewrite /id.
      now apply trans_consistent_instance_ext.
    + cbn [Ast.pparams Ast.pcontext trans_predicate].
      rewrite (trans_case_predicate_context Γ); tea.
      now rewrite -trans_local_app. 
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + now rewrite trans_mkApps map_app in X8.
    + rewrite (trans_case_predicate_context Γ); tea.
      eapply All2i_map. eapply All2i_map_right.
      eapply Forall2_All2 in H4.
      eapply All2i_All2_mix_left in X9; tea.
      eapply All2i_impl ; tea.
      intros i cdecl br. cbv beta.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _).
      intros (wf & eqctx & Hbctx & Hb & IHb & Hbty & IHbty) brctxty.
      repeat split.
      * rewrite /brctxty.
        now eapply trans_cstr_branch_context_eq.
      * pose proof (trans_case_branch_type ci mdecl idecl cdecl i p br isdecl H1 wf eqctx).
        rewrite -/brctxty -/ptm in H5. cbn in H5. clearbody brctxty.
        subst brctxty. rewrite -trans_local_app. cbn. apply IHb.
      * pose proof (trans_case_branch_type ci mdecl idecl cdecl i p br isdecl H1 wf eqctx).
        rewrite -/brctxty -/ptm in H5. cbn in H5. clearbody brctxty.
        subst brctxty. rewrite -trans_local_app. cbn. apply IHbty.

  - rewrite trans_subst.
    rewrite trans_subst_instance.
    cbn.
    rewrite map_rev.
    change (trans ty) with ((on_snd trans pdecl).2).
    eapply TT.type_Proj.
    + now apply trans_declared_projection.
    + rewrite trans_mkApps in X2.
      assumption.
    + rewrite map_length.
      rewrite H.
      destruct mdecl.
      reflexivity.
  - rewrite trans_dtype. simpl.
    eapply TT.type_Fix; auto.
    + now rewrite fix_guard_trans.
    + erewrite map_nth_error. 
      2: apply H0.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + eapply All_map, (All_impl X0).
      intuition auto. destruct X2 as [s [? ?]].
      exists s; intuition auto.
    + fold trans.
      subst types.
      eapply trans_mfix_All2; eassumption.
    + now rewrite trans_wf_fixpoint. 
  - rewrite trans_dtype. simpl.
    eapply TT.type_CoFix; auto.
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error. 
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + fold trans.
      eapply All_map, (All_impl X0).
      intros x [s ?]; exists s; intuition auto.
    + fold trans;subst types.
      now apply trans_mfix_All2.
    + now rewrite trans_wf_cofixpoint.
  - eapply TT.type_Conv.
    + eassumption.
    + eassumption.
    + eapply cumul_decorate in X4; tea.
      2:eapply validity; tea.
      2:now exists s.
      now eapply trans_cumul.
Qed.

Print Assumptions pcuic_to_template.
