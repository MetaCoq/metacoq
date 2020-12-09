(* Distributed under the terms of the MIT license. *)
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICUnivSubst PCUICTyping PCUICGeneration.

Set Warnings "-notation-overridden".
From MetaCoq.Template Require Import config utils Ast TypingWf WfInv UnivSubst
     LiftSubst.

Set Warnings "+notation_overridden".

Require Import PCUICToTemplate.
From Coq Require Import ssreflect.

(* from Checker Generation to avoid dependencies *)

Derive Signature for Template.Typing.typing.
Derive NoConfusion for term.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

(** Source = PCUIC, Target = Coq *)
Module S := PCUICAst.
Module ST := PCUICTyping.
Module T := Template.Ast.
Module TT := Template.Typing.

Local Existing Instance default_checker_flags.

Module SL := PCUICLiftSubst.
Module TL := Template.LiftSubst.


Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mkAppMkApps s t:
  mkApp s t = mkApps s [t].
Proof.
  cbn. unfold mkApp.
  reflexivity.
Qed.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma trans_lift (t : S.term) n k:
  trans (SL.lift n k t) = TL.lift n k (trans t).
Proof.
  revert k. induction t using PCUICInduction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite IHt1 IHt2.
    rewrite mkAppMkApps.
    rewrite <- mapOne.
    rewrite <- TL.lift_mkApps.
    f_equal.
  - f_equal; auto. red in X. solve_list.
  - f_equal; auto; red in X; solve_list.
  - f_equal; auto; red in X; solve_list.
  - destruct p as [? []]; eauto.
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
ST.global_ext_levels Σ = TT.global_ext_levels (trans_global Σ).
Proof.
  unfold TT.global_ext_levels, ST.global_ext_levels.
  destruct Σ.
  cbn [trans_global fst snd].
  f_equal.
  induction g.
  - reflexivity.
  - unfold ST.global_levels in IHg.
    cbn.
    rewrite IHg.
    f_equal.
    destruct a.
    cbn.
    unfold TT.monomorphic_levels_decl, TT.monomorphic_udecl_decl, TT.on_udecl_decl.
    unfold ST.monomorphic_levels_decl, ST.monomorphic_udecl_decl, ST.on_udecl_decl.
    destruct g0.
    + cbn.
      destruct c.
      reflexivity.
    + cbn.
      destruct m.
      reflexivity.
Qed.

Lemma trans_global_ext_constraints Σ :
  ST.global_ext_constraints Σ = TT.global_ext_constraints (trans_global Σ).
Proof.
  destruct Σ.
  unfold ST.global_ext_constraints, trans_global.
  cbn [fst snd].
Admitted.

Lemma trans_mem_level_set l Σ:
LevelSet.mem l (ST.global_ext_levels Σ) ->
LevelSet.mem l (TT.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_in_level_set l Σ:
LevelSet.In l (ST.global_ext_levels Σ) ->
LevelSet.In l (TT.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.


Lemma trans_lookup Σ cst decl:
S.lookup_env Σ.1 cst = Some decl ->
Ast .lookup_env (trans_global Σ).1 cst =
Some (trans_global_decl decl).
Proof.
  intros H.
  destruct Σ.
  cbn in *.
  induction g;cbn in H.
  - discriminate H.
  - cbn.
    unfold eq_kername in *; destruct kername_eq_dec; subst.
    + destruct a.
      cbn in *.
      injection H as ->.
      reflexivity.
    + apply IHg, H.
Qed.

Lemma trans_declared_constant Σ cst decl:
ST.declared_constant Σ.1 cst decl ->
TT.declared_constant (trans_global Σ).1 cst (trans_constant_body decl).
Proof.
  intros H.
  unfold TT.declared_constant.
  unfold ST.declared_constant in H.
  apply trans_lookup in H as ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
ConstraintSet.In x (ST.global_ext_constraints Σ) ->
ConstraintSet.In x (TT.global_ext_constraints (trans_global Σ)).
Proof.
  rewrite trans_global_ext_constraints.
  trivial.
Qed.

Lemma trans_consistent_instance_ext Σ decl u:
ST.consistent_instance_ext Σ decl u ->
TT.consistent_instance_ext (trans_global Σ) decl u.
Proof.
  intros H.
  unfold consistent_instance_ext, ST.consistent_instance_ext in *.
  unfold consistent_instance, ST.consistent_instance in *.
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

Lemma trans_declared_inductive Σ mdecl ind idecl:
ST.declared_inductive Σ.1 mdecl ind idecl ->
TT.declared_inductive (trans_global Σ).1 (trans_minductive_body mdecl) ind (trans_one_ind_body idecl).
Proof.
  intros [].
  split.
  - unfold TT.declared_minductive, ST.declared_minductive in *.
    apply trans_lookup in H as ->.
    reflexivity.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
trans (PCUICAst.mkApps t args) =
mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity. 
  - cbn [map].
    rewrite <- LiftSubst.mkApps_mkApp.
    cbn.
    rewrite IHargs.
    reflexivity.
Qed.


Lemma trans_decl_type decl:
trans (PCUICAst.decl_type decl) =
decl_type (trans_decl decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma All_forall {X Y} (f:X->Y->Prop) xs: 
  All (fun a => forall b, f a b) xs ->
  (forall b, All (fun a => f a b) xs).
Proof.
  intros.
  induction X0.
  - constructor.
  - constructor.
    + apply p.
    + apply IHX0.
Qed.


Lemma trans_subst xs k t:
  trans (SL.subst xs k t) =
  TL.subst (map trans xs) k (trans t).
Proof.
  induction t in k |- * using PCUICInduction.term_forall_list_ind.
  all: cbn;try congruence.
  - destruct leb;trivial.
    rewrite nth_error_map.
    destruct nth_error;cbn.
    2: now rewrite map_length.
    rewrite trans_lift.
    reflexivity.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    eapply All_forall in X.
    apply X.
  - rewrite IHt1 IHt2.
    destruct (trans t1);cbn;trivial.
    rewrite AstUtils.mkApp_mkApps.
    do 2 f_equal.
    rewrite map_app.
    cbn.
    reflexivity.
  - f_equal;trivial.
    do 2 rewrite map_map.
    apply All_map_eq.
    induction X;trivial.
    constructor.
    + destruct x.
      unfold on_snd;cbn.
      rewrite p0.
      reflexivity.
    + apply IHX.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.  
    + apply IHX.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.  
    + apply IHX.
  - destruct p as [? []]; eauto.
Qed.


Lemma trans_subst10 u B:
trans (SL.subst1 u 0 B)=
TL.subst10 (trans u) (trans B).
Proof.
  unfold SL.subst1.
  rewrite trans_subst.
  reflexivity.
Qed.

Lemma trans_subst_instance_constr u t:
trans (PCUICUnivSubst.subst_instance_constr u t) =
Template.UnivSubst.subst_instance_constr u (trans t).
Proof.
  induction t using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map. 
    f_equal.
    apply All_map_eq.
    apply X.
  - rewrite IHt1 IHt2.
    do 2 rewrite mkAppMkApps.
    rewrite subst_instance_constr_mkApps.
    cbn.
    reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2. 
    + do 2 rewrite map_map.
      unfold tCaseBrsProp in X.
      apply All_map_eq.
      induction X.
      * constructor.
      * constructor;trivial.
        destruct x.
        cbn.
        unfold on_snd.
        cbn. cbn in p0.
        rewrite p0.
        reflexivity.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - destruct p as [? []]; eauto.
Qed.

Lemma trans_cst_type decl:
trans (PCUICAst.cst_type decl) =
cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type idecl:
trans (PCUICAst.ind_type idecl) =
ind_type (trans_one_ind_body idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_type_of_constructor mdecl cdecl ind i u:
trans (ST.type_of_constructor mdecl cdecl (ind, i) u) =
TT.type_of_constructor 
  (trans_minductive_body mdecl) 
  (trans_ctor cdecl)
  (ind,i)
  u.
Proof.
  unfold ST.type_of_constructor.
  rewrite trans_subst.
  unfold TT.type_of_constructor.
  f_equal.
  - cbn [fst].
    rewrite ST.inds_spec.
    rewrite TT.inds_spec.
    rewrite map_rev.
    rewrite map_mapi.
    destruct mdecl.
    cbn.
    f_equal.
    remember 0 as k.
    induction ind_bodies in k |- *.
    + reflexivity.
    + cbn.
      f_equal.
      apply IHind_bodies.
  - rewrite trans_subst_instance_constr.
    f_equal.
    destruct cdecl as [[? ?] ?].
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

Lemma trans_declared_projection Σ mdecl idecl p pdecl :
ST.declared_projection Σ.1 mdecl idecl p pdecl ->
TT.declared_projection (trans_global Σ).1 (trans_minductive_body mdecl) (trans_one_ind_body idecl) p (on_snd trans pdecl).
Proof.
  intros (?&?&?).
  split;[|split].
  - now apply trans_declared_inductive.
  - unfold on_snd.
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


Lemma trans_instantiate_params params pars ty:
  option_map trans 
  (ST.instantiate_params 
    params pars ty) = 
    TT.instantiate_params (trans_local params) (map trans pars) (trans ty).
Proof.
  rewrite TT.instantiate_params_ ST.instantiate_params_.
  rewrite option_map_two.
  match goal with
  |- option_map _ (_ _ _ ?A _) = option_map _ (_ _ _ ?B _) => change B with (map trans A)
  end.
  remember nil as xs.
  clear Heqxs.
  revert pars xs ty.
  induction params using rev_ind;intros pars xs ty.
  - cbn. destruct pars;trivial.
    cbn. now rewrite trans_subst.
  - unfold trans_local. 
    rewrite map_app. cbn.
    do 2 rewrite rev_unit. cbn.
    destruct x as [? [] ?];cbn.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. rewrite IHparams.
      cbn. now rewrite trans_subst.
      destruct prim as [? []]; eauto.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. destruct pars;trivial.
      cbn. now rewrite IHparams.
      destruct prim as [? []]; eauto.
Qed.


Lemma trans_instantiate_params' u mdecl idecl args npar x:
ST.instantiate_params
      (PCUICUnivSubst.subst_instance_context u (PCUICAst.ind_params mdecl))
      (firstn npar args)
      (PCUICUnivSubst.subst_instance_constr u (PCUICAst.ind_type idecl)) =
    Some x ->
 TT.instantiate_params
   (subst_instance_context u
      (trans_local (PCUICAst.ind_params mdecl)))
   (firstn npar (map trans args))
   (subst_instance_constr u (trans (PCUICAst.ind_type idecl))) =
   Some (trans x).
Proof.
  intros H.
  rewrite <- trans_subst_instance_constr.
  rewrite firstn_map.
  match goal with
  |- TT.instantiate_params ?A _ _ = _ =>
      replace A with (trans_local (PCUICUnivSubst.subst_instance_context u (PCUICAst.ind_params mdecl)))
  end.
  2: {
    unfold PCUICUnivSubst.subst_instance_context, trans_local.
    unfold PCUICAst.map_context.
    rewrite map_map.
    destruct mdecl.
    cbn. 
    clear H.
    induction ind_params;cbn in *;trivial.
    f_equal.
    - destruct a;cbn.
      unfold map_decl;cbn.
      do 2 rewrite option_map_two.
      f_equal.
      + destruct decl_body;cbn;trivial.
        now rewrite trans_subst_instance_constr.
      + now rewrite trans_subst_instance_constr.
    - apply IHind_params.
  }
  rewrite <- trans_instantiate_params.
  rewrite H.
  reflexivity.
Qed.

Lemma trans_destr_arity x:
TT.destArity [] (trans x) 
= option_map (fun '(xs,u) => (map trans_decl xs,u)) (PCUICAstUtils.destArity [] x).
Proof.
  remember (@nil PCUICAst.context_decl) as xs.
  replace (@nil context_decl) with (map trans_decl xs) by (now subst).
  clear Heqxs.
  induction x in xs |- *;cbn;trivial;unfold snoc, PCUICAst.snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
  - destruct (trans x1);cbn;trivial.
  - destruct prim as [? []]; eauto.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (PCUICAst.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (PCUICAst.it_mkProd_or_LetIn xs t) =
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

Lemma trans_iota_red pars c args brs :
  trans (iota_red pars c args brs) =
  TT.iota_red pars c (List.map trans args) (List.map (on_snd trans) brs).
Proof.
  unfold iota_red, TT.iota_red.
  rewrite trans_mkApps.
  f_equal. induction brs in c |- *; simpl; destruct c; trivial.
    now rewrite map_skipn.
Qed.

Lemma trans_isLambda t :
  T.isLambda (trans t) = S.isLambda t.
Proof.
  destruct t; cbnr.
  generalize (trans t1) (trans t2); clear.
  induction t; intros; cbnr.
  destruct prim as [? []]; cbnr.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  List.Forall (fun def : def S.term => S.isLambda (dbody def) = true) mfix ->
  unfold_fix mfix idx = Some (narg, fn) ->
  TT.unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_fix, unfold_fix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros [= <- <-]. simpl.
  eapply nth_error_forall in wffix; eauto. simpl in wffix.
  rewrite trans_isLambda wffix.
  repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef. simpl.
  unfold fix_subst, TT.fix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  TT.unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_cofix, unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef.
  unfold cofix_subst, TT.cofix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Definition isApp t := match t with tApp _ _ => true | _ => false end.

Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> TT.is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold TT.is_constructor, is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold AstUtils.isConstruct_app, isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite decompose_app_mkApps //. 
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.
Ltac wf_inv H := try apply wf_inv in H; simpl in H; rdest.

Lemma trans_red1 Σ Γ T U :
  red1 Σ Γ T U ->
  TT.red1 (map (on_snd trans_global_decl) Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *;
    try solve [econstructor; eauto].

  - simpl.
    rewrite trans_subst; auto. constructor.
    
  - rewrite trans_subst; eauto. repeat constructor.
  - rewrite trans_lift; eauto. repeat constructor.
    rewrite nth_error_map.
    destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.

  - rewrite trans_mkApps; eauto with wf; simpl.
    erewrite trans_iota_red; eauto. repeat constructor.

  - simpl. rewrite !trans_mkApps /=.
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. elimtype False; depelim H1.
    cbn -[mkApps].
    eapply refine_red1_r; cycle 1.
    eapply TT.red_fix. 
    apply trans_unfold_fix; eauto. admit.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    

  - apply wf_mkApps_napp in H1; auto.
    intuition.
    pose proof (unfold_cofix_wf _ _ _ _ H H3). wf_inv H3.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply red_cofix_case; eauto.

  - eapply wf_mkApps_napp in Hwf; auto.
    intuition. pose proof (unfold_cofix_wf _ _ _ _ H H0). wf_inv H0.
    rewrite !trans_mkApps; intuition eauto with wf.
    eapply red_cofix_proj; eauto.
    apply trans_unfold_cofix; eauto with wf.

  - rewrite trans_subst_instance_constr. econstructor.
    apply (forall_decls_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body.

  - rewrite trans_mkApps; eauto with wf.
    simpl. constructor. now rewrite nth_error_map H.

  - constructor. apply IHX. constructor; hnf; simpl; auto. hnf. auto.

  - constructor. apply IHX. constructor; hnf; simpl; auto. auto.

  - constructor. solve_all.
    apply OnOne2_map. apply (OnOne2_All_mix_left H1) in X. clear H1.
    solve_all. red. simpl in *.
    intuition eauto.
    apply b2. all: solve_all.

  - rewrite !trans_mkApps; auto with wf. eapply wf_red1 in X; auto.
    apply red1_mkApps_l. auto.

  - apply Forall_All in H2. clear H H0 H1. revert M1. induction X.
    simpl. intuition. inv H2. specialize (X H).
    apply red1_mkApps_l. apply app_red_r. auto.
    inv H2. specialize (IHX X0).
    simpl. intros.
    eapply (IHX (T.tApp M1 [hd])).

  - constructor. apply IHX. constructor; hnf; simpl; auto. auto.
  - constructor. induction X; simpl; repeat constructor. apply p; auto. now inv Hwf.
    apply IHX. now inv Hwf.

  - constructor. constructor. eapply IHX; auto.
  - eapply refine_red1_r; [|constructor]. unfold subst1. simpl. now rewrite lift0_p.

  - constructor. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody.
    inversion b0. clear b0.
    intuition eauto.
    + eapply b. all: solve_all.
    + unfold map_def. simpl.
      f_equal. 2: auto.
      f_equal. assumption.

  - apply fix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    + unfold Template.Ast.app_context, trans_local in b.
      simpl in a. rewrite -> map_app in b.
      unfold app_context. unfold TTy.fix_context in b.
      rewrite map_rev map_mapi in b. simpl in b.
      unfold fix_context. rewrite mapi_map. simpl.
      forward b.
      { clear b. solve_all. eapply All_app_inv; auto.
        apply All_rev. apply All_mapi.
        clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
        intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        now eapply LiftSubst.wf_lift.
        depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      }
      forward b by auto.
      eapply (refine_red1_Γ); [|apply b].
      f_equal. f_equal. apply mapi_ext; intros [] [].
      rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
      rewrite trans_lift. simpl. reflexivity.
    + simpl. inversion b0. reflexivity.

  - constructor. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody.
    inversion b0. clear b0.
    intuition eauto.
    + eapply b. all: solve_all.
    + unfold map_def. simpl.
      f_equal. 2: auto.
      f_equal. assumption.

  - apply cofix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    + unfold Template.Ast.app_context, trans_local in b.
      simpl in a. rewrite -> map_app in b.
      unfold app_context. unfold TTy.fix_context in b.
      rewrite map_rev map_mapi in b. simpl in b.
      unfold fix_context. rewrite mapi_map. simpl.
      forward b.
      { clear b. solve_all. eapply All_app_inv; auto.
        apply All_rev. apply All_mapi.
        clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
        intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        now eapply LiftSubst.wf_lift.
        depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      }
      forward b by auto.
      eapply (refine_red1_Γ); [|apply b].
      f_equal. f_equal. apply mapi_ext; intros [] [].
      rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
      rewrite trans_lift. simpl. reflexivity.
    + simpl. inversion b0. reflexivity.
Qed.



Lemma trans_build_case_predicate_type ind mdecl idecl npar args u ps pty:
ST.build_case_predicate_type ind mdecl idecl (firstn npar args) u ps = Some pty ->
TT.build_case_predicate_type ind (trans_minductive_body mdecl)
  (trans_one_ind_body idecl) (firstn npar (map trans args)) 
  u ps = Some (trans pty).
Proof.
  intros H.
  apply inv_opt_monad in H as (?&?&?&?&[=]).
  unfold TT.build_case_predicate_type.
  simpl in *.
  apply trans_instantiate_params' in H as ->.
  simpl.
  rewrite trans_destr_arity, H0. 
  simpl. f_equal.
  rewrite <- H2.
  rewrite trans_it_mkProd_or_LetIn,
  trans_mkProd_or_LetIn.
  f_equal.
  - now destruct x0.
  - f_equal. cbn.
    f_equal.
    rewrite trans_mkApps. cbn.
    f_equal.
    destruct x0;cbn.
    rewrite map_app.
    rewrite map_map.
    clear H2.
    f_equal.
    + rewrite firstn_map.
      induction (firstn npar args);cbn;trivial.
      now rewrite IHl0, map_length, trans_lift.
    + remember 0 as n;clear Heqn.
      remember (@nil PCUICAst.term) as xs.
      replace (@nil term) with (map trans xs) by (now subst).
      clear Heqxs.
      induction l in n, xs |- *;cbn;trivial.
      now destruct a as [? [] ?];rewrite <- IHl;cbn.
Qed.


Lemma trans_fix_context mfix:
map trans_decl (PCUICLiftSubst.fix_context mfix) =
TT.fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  destruct mfix;trivial.
  unfold TT.fix_context, PCUICLiftSubst.fix_context.
  rewrite map_rev, map_mapi.
  cbn. f_equal.
  2: {
    destruct d. cbn.
    rewrite lift0_p.
    rewrite SL.lift0_p.
    unfold vass.
    reflexivity.
  }
  f_equal.
  unfold vass.
  remember 1 as k.
  induction mfix in k |- *;trivial.
  cbn;f_equal.
  - now rewrite trans_lift.
  - apply IHmfix.
Qed.

Definition TTwf_local Σ Γ := TT.All_local_env (TT.lift_typing TT.typing Σ) Γ.

Lemma trans_wf_local':
  forall (Σ : PCUICAst.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
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

Lemma trans_wf_local_env Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : PCUICAst.global_env_ext) Γ b ty =>
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

Lemma trans_branches Σ Γ brs btys ps:
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

Lemma trans_mfix_All Σ Γ mfix:
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : PCUICEnvironment.global_env_ext)
          (Γ : PCUICEnvironment.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) mfix)).
Proof.
  intros.
  rewrite <- trans_fix_context.
  match goal with
  |- TTwf_local _ ?A =>
      replace A with (trans_local (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context mfix)))
  end.
  2: {
    unfold trans_local, PCUICAst.app_context.
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

Lemma trans_mfix_All2 Σ Γ mfix xfix:
  All
  (fun d : def PCUICAst.term =>
    (ST.typing Σ (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix))
    (dbody d)
    (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix| (dtype d))
    × PCUICAst.isLambda (dbody d) = true)
    × TT.typing (trans_global Σ)
      (trans_local (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix)))
      (trans (dbody d))
      (trans
          (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix|
            (dtype d)))) mfix ->
  All
    (fun d : def term =>
    TT.typing (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) xfix)) 
    (dbody d) (TL.lift0 #|TT.fix_context (map (map_def trans trans) xfix)| (dtype d))
    × isLambda (dbody d) = true) (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - simpl; constructor.
    + destruct p as [[]].
      unfold app_context, PCUICAst.app_context in *.
      split.
      * unfold trans_local in t0.
        rewrite map_app, trans_fix_context in t0.
        rewrite trans_dbody, trans_lift, trans_dtype in t0.
        replace(#|PCUICLiftSubst.fix_context xfix|) with
            (#|TT.fix_context (map(map_def trans trans) xfix)|) in t0.
        2:now rewrite TT.fix_context_length, map_length, fix_context_length.
        now destruct x.
      * destruct x; simpl in *; auto.
        now destruct dbody.
    + auto.
Qed.

Lemma trans_mfix_All2' Σ Γ mfix xfix:
  All
  (fun d : def PCUICAst.term =>
    (ST.typing Σ (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix))
    (dbody d)
    (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix| (dtype d)))
    × TT.typing (trans_global Σ)
      (trans_local (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix)))
      (trans (dbody d))
      (trans
          (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix|
            (dtype d)))) mfix ->
  All
    (fun d : def term =>
    TT.typing (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) xfix)) 
    (dbody d) (TL.lift0 #|TT.fix_context (map (map_def trans trans) xfix)| (dtype d))) 
    (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - simpl; constructor.
    + destruct p as [].
      unfold app_context, PCUICAst.app_context in *.
      unfold trans_local in t0.
      rewrite map_app, trans_fix_context in t0.
      rewrite trans_dbody, trans_lift, trans_dtype in t0.
      replace(#|PCUICLiftSubst.fix_context xfix|) with
          (#|TT.fix_context (map(map_def trans trans) xfix)|) in t0.
        2:now rewrite TT.fix_context_length, map_length, fix_context_length.
        now destruct x.
    + auto.
Qed.

Lemma All_over_All Σ Γ wfΓ :
  ST.All_local_env_over ST.typing
    (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Σ Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : PCUICAst.global_env_ext) (Γ0 : PCUICEnvironment.context)
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





Lemma invert_type_App `{checker_flags} Σ Γ f u T :
  TT.typing Σ Γ (tApp f u) T ->
  { T' : term & { U' & ((TT.typing Σ Γ f T') * TT.typing_spine Σ Γ T' u U' *
                        (isApp f = false) * (u <> []) *
                        (TT.cumul Σ Γ U' T))%type } }.
Proof.
  intros Hty.
  dependent induction Hty.
  - exists t_ty, t'. intuition.
  - edestruct IHHty1 as [T' [U' [H' H'']]].
    exists T', U'. split; auto.
    eapply TT.cumul_trans; eauto.
Qed.

Lemma type_mkApp `{checker_flags} Σ Γ f u T T' :
  TT.typing Σ Γ f T ->
  TT.typing_spine Σ Γ T [u] T' ->
  TT.typing Σ Γ (mkApp f u) T'.
Proof.
  intros Hf Hu. inv Hu.
  simpl. destruct (isApp f) eqn:Happ.
  destruct f; try discriminate. simpl.
  eapply invert_type_App in Hf.
  destruct Hf as (T'' & U' & (((Hf & HU) & Happf) & Hunil) & Hcumul).
  eapply TT.type_App; eauto. intro. destruct args; discriminate.
  inv X2. clear Happ Hf Hunil.
  induction HU. simpl. econstructor; eauto.
  eapply TT.cumul_trans; eauto.
  econstructor. econstructor. eapply t. eauto. eauto.
  apply IHHU; eauto.
  rewrite -> AstUtils.mkApp_tApp; eauto.
  econstructor; eauto. congruence.
  econstructor; eauto.
Qed.


(* from Checker Substitution *)



Lemma eq_term_upto_univ_refl Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  forall t, TT.eq_term_upto_univ Re Rle t t.
Proof.
  intros hRe hRle.
  induction t in Rle, hRle |- * using Induction.term_forall_list_rect; simpl;
    try constructor; try apply Forall_Forall2; try apply All_All2 ; try easy;
      try now (try apply Forall_All ; apply Forall_True).
  - eapply All_All2. 1: eassumption.
    intros. easy.
  - eapply All_All2. 1: eassumption.
    intros. easy.
  - destruct p. constructor; try easy.
    eapply All_All2. 1: eassumption.
    intros. split ; auto.
  - eapply All_All2. 1: eassumption.
    intros x [? ?]. repeat split ; auto.
  - eapply All_All2. 1: eassumption.
    intros x [? ?]. repeat split ; auto.
Qed.

Lemma leq_term_refl `{checker_flags} φ t : TT.leq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro; apply eq_universe_refl.
  - intro; apply leq_universe_refl.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).
  
Theorem template_to_pcuic (Σ : S.global_env_ext) Γ t T :
  ST .wf Σ ->
  ST.typing Σ Γ t T ->
  TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.

  intros X X0.
  revert Σ X Γ t T X0.
  apply (ST.typing_ind_env (fun Σ Γ t T =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ wfΓ => 
    TT.All_local_env (TT.lift_typing TT.typing (trans_global Σ)) (trans_local Γ))
  );intros.
  - now eapply trans_wf_local_env, All_over_All.
(*
typing_ind_env is like induction but with
additional assumptions for the nested typing 
in All (for wf_local assumptions)
*)
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
  - eapply type_mkApp.
    + eassumption.
    + econstructor.
      3: eassumption.
      3: {
        rewrite trans_subst10.
        constructor.
      }
      2: {
        cbn. constructor.
        apply leq_term_refl.
      }
      admit. 
      (* 
      tProd na (trans A) (trans B) has a type
      obtain with inversion from IHX0_1
      *)
  - rewrite trans_subst_instance_constr.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_subst_instance_constr.
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
  - replace (trans (PCUICAst.mkApps p (skipn npar args ++ [c])))
    with (mkApps (trans p) (skipn npar (map trans args) ++ [trans c])).
    2: {
      rewrite trans_mkApps.
      rewrite map_app.
      cbn.
      repeat f_equal.
      now rewrite map_skipn.
    }
    eapply TT.type_Case.
    + now apply trans_declared_inductive.
    + cbn. assumption.
    + apply trans_build_case_predicate_type.
      eassumption.
    + eassumption.
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + auto.
    + now rewrite trans_mkApps in X4.
    + admit. (* map_option_out build branche type *)
    (* this should be similar to trans_build_case_predicate_type *)
    + admit. (* now apply trans_branches.*)
  - rewrite trans_subst.
    rewrite trans_subst_instance_constr.
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
    + eapply All_map, (All_impl X0).
      intuition auto. destruct X2 as [s [? ?]].
      exists s; intuition auto.
    + fold trans.
      subst types.
      eapply trans_mfix_All2;eassumption.
    + admit.
  - rewrite trans_dtype. simpl.
    eapply TT.type_CoFix; auto.
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error. 
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + fold trans.
      eapply All_map, (All_impl X0).
      intros x [s ?]; exists s; intuition auto.
    + fold trans;subst types.
      (* like trans_mfix_All2 without isLambda *)
      now apply trans_mfix_All2'.
    + admit.
  - eapply TT.type_Conv.
    + eassumption.
    + admit. (* eapply trans_cumul. *)
Admitted.
