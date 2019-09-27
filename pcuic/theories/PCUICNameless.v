(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From MetaCoq.Template
Require Import config monad_utils utils AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICTyping PCUICPosition PCUICUnivSubst
     PCUICCumulativity.
From Equations Require Import Equations.
Local Set Keyed Unification.
Require Import Equations.Prop.DepElim.

Definition anon (na : name) : bool :=
  match na with
  | nAnon => true
  | nNamed s => false
  end.

Fixpoint nameless (t : term) : bool :=
  match t with
  | tRel n => true
  | tVar n => true
  | tEvar n l => forallb nameless l
  | tSort s => true
  | tProd na A B => anon na && nameless A && nameless B
  | tLambda na A b => anon na && nameless A && nameless b
  | tLetIn na b B t => anon na && nameless b && nameless B && nameless t
  | tApp u v => nameless u && nameless v
  | tConst c u => true
  | tInd i u => true
  | tConstruct i n u => true
  | tCase indn p c brs =>
    nameless p && nameless c && forallb (test_snd nameless) brs
  | tProj p c => nameless c
  | tFix mfix idx =>
    forallb (fun d => anon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tCoFix mfix idx =>
    forallb (fun d => anon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  end.

Definition map_def_anon {A B : Set} (tyf bodyf : A -> B) (d : def A) := {|
  dname := nAnon ;
  dtype := tyf d.(dtype) ;
  dbody := bodyf d.(dbody) ;
  rarg  := d.(rarg)
|}.

Fixpoint nl (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar n => tVar n
  | tEvar n l => tEvar n (map nl l)
  | tSort s => tSort s
  | tProd na A B => tProd nAnon (nl A) (nl B)
  | tLambda na A b => tLambda nAnon (nl A) (nl b)
  | tLetIn na b B t => tLetIn nAnon (nl b) (nl B) (nl t)
  | tApp u v => tApp (nl u) (nl v)
  | tConst c u => tConst c u
  | tInd i u => tInd i u
  | tConstruct i n u => tConstruct i n u
  | tCase indn p c brs => tCase indn (nl p) (nl c) (map (on_snd nl) brs)
  | tProj p c => tProj p (nl c)
  | tFix mfix idx => tFix (map (map_def_anon nl nl) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def_anon nl nl) mfix) idx
  end.

Ltac destruct_one_andb :=
  lazymatch goal with
  | h : is_true (_ && _) |- _ =>
    apply andP in h ; destruct h as [? ?]
  end.

Ltac destruct_andb :=
  repeat destruct_one_andb.

Local Ltac anonify :=
  repeat lazymatch goal with
  | h : is_true (anon ?na) |- _ =>
    destruct na ; [clear h | discriminate h]
  end.

Local Ltac ih :=
  lazymatch goal with
  | ih : forall v : term, _ -> _ -> eq_term_upto_univ _ _ _ _ -> ?u = _
    |- ?u = ?v =>
    eapply ih ; assumption
  end.

Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' h.
  revert u' h.
  induction u ; intros u' h.
  - destruct u' ; inversion h. reflexivity.
  - destruct u' ; inversion h. subst.
    f_equal.
    + inversion H2. reflexivity.
    + eapply IHu. assumption.
Qed.

Lemma nameless_eq_term_spec :
  forall u v,
    nameless u ->
    nameless v ->
    eq_term_upto_univ eq eq u v ->
    u = v.
Proof.
  intros u v hu hv e.
  revert v hu hv e.
  induction u using term_forall_list_ind ; intros v hu hv e.
  all: dependent destruction e.
  all: cbn in hu, hv ; destruct_andb ; anonify.
  all: try reflexivity.
  all: try solve [ f_equal ; try ih ; try assumption ].
  - f_equal. cbn in hu, hv.
    revert args' hu hv a. induction l ; intros args' hu hv h.
    + destruct args' ; try solve [ inversion h ].
      reflexivity.
    + destruct args' ; try solve [ inversion h ].
      inversion h. subst.
      inversion H. subst.
      cbn in hu, hv. destruct_andb.
      f_equal.
      * eapply H2 ; assumption.
      * eapply IHl ; assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    revert brs' H3 H0 a.
    induction l ; intros brs' h1 h2 h.
    + destruct brs' ; inversion h. reflexivity.
    + destruct brs' ; inversion h. subst.
      cbn in h1, h2. destruct_andb.
      inversion X. subst.
      f_equal.
      * destruct a, p0. cbn in *. destruct H6. subst.
        f_equal. eapply H11 ; assumption.
      * eapply IHl ; assumption.
  - f_equal ; try solve [ ih ].
    revert mfix' H1 H2 H H0 a.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct H2 as [[? ?] ?].
        destruct H1 as [Hty Hbod].
        unfold test_def in H7, H. cbn in H7, H.
        destruct_andb. anonify.
        f_equal.
        -- eapply Hty; assumption.
        -- eapply Hbod ; assumption.
        -- assumption.
      * eapply IHm ; assumption.
  - f_equal ; try solve [ ih ].
    revert mfix' H1 H2 H H0 a.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct H2 as [[? ?] ?].
        destruct H1 as [Hty Hbod].
        unfold test_def in H7, H. cbn in H7, H.
        destruct_andb. anonify.
        f_equal.
        -- eapply Hty; assumption.
        -- eapply Hbod ; assumption.
        -- assumption.
      * eapply IHm ; assumption.
Qed.

Lemma nl_spec :
  forall u, nameless (nl u).
Proof.
  intros u. induction u using term_forall_list_ind.
  all: try reflexivity.
  all: try (simpl ; repeat (eapply andb_true_intro ; split) ; assumption).
  - cbn. eapply All_forallb. eapply All_map. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    induction l.
    + reflexivity.
    + cbn. inversion X. subst.
      repeat (eapply andb_true_intro ; split) ; try assumption.
      eapply IHl. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H1.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H1.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
Qed.

Lemma nl_eq_term_upto_univ :
  forall Re Rle t t',
    eq_term_upto_univ Re Rle t t' ->
    eq_term_upto_univ Re Rle (nl t) (nl t').
Proof.
  intros Re Rle t t' h.
  revert t t' Rle h. fix aux 4.
  intros t t' Rle h.
  destruct h.
  all: simpl.
  all: try solve [ econstructor ; eauto ].
  - econstructor.
    induction a.
    + constructor.
    + simpl. econstructor. all: eauto.
  - econstructor. all: try solve [ eauto ].
    induction a.
    + constructor.
    + simpl. econstructor. 2: solve [ eauto ].
      destruct x, y, r. simpl in *.
      split. 1: assumption.
      eauto.
  - econstructor.
    induction a. 1: constructor.
    simpl. constructor.
    + destruct x, y, r as [[? ?] ?].
      simpl in *. eauto.
    + eauto.
  - econstructor.
    induction a. 1: constructor.
    simpl. constructor.
    + destruct x, y, r as [[? ?] ?].
      simpl in *. eauto.
    + eauto.
Qed.

Lemma nl_leq_term {cf:checker_flags} :
  forall φ t t',
    leq_term φ t t' ->
    leq_term φ (nl t) (nl t').
Proof.
  intros. apply nl_eq_term_upto_univ. assumption.
Qed.

Lemma nl_eq_term {cf:checker_flags} :
  forall φ t t',
    eq_term φ t t' ->
    eq_term φ (nl t) (nl t').
Proof.
  intros. apply nl_eq_term_upto_univ. assumption.
Qed.

Corollary eq_term_nl_eq :
  forall u v,
    eq_term_upto_univ eq eq u v ->
    nl u = nl v.
Proof.
  intros u v h.
  eapply nameless_eq_term_spec.
  - eapply nl_spec.
  - eapply nl_spec.
  - now eapply nl_eq_term_upto_univ.
Qed.

Local Ltac ih3 :=
  lazymatch goal with
  | ih : forall Rle v, eq_term_upto_univ _ _ (nl ?u) _ -> _
    |- eq_term_upto_univ _ _ ?u _ =>
    eapply ih ; assumption
  end.

Lemma eq_term_upto_univ_nl_inv :
  forall Re Rle u v,
    eq_term_upto_univ Re Rle (nl u) (nl v) ->
    eq_term_upto_univ Re Rle u v.
Proof.
  intros Re Rle u v h.
  induction u in v, h, Rle |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: destruct v ; try discriminate.
  all: try solve [
    try lazymatch goal with
    | h : nl _ = _ |- _ =>
      simpl in h ; inversion h ; subst
    end ;
    constructor ;
    try ih3 ;
    assumption
  ].
  - cbn in H. inversion H. subst. constructor.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
Qed.

Definition map_decl_anon f (d : context_decl) := {|
  decl_name := nAnon ;
  decl_body := option_map f d.(decl_body) ;
  decl_type := f d.(decl_type)
|}.

Definition nlctx (Γ : context) : context :=
  map (map_decl_anon nl) Γ.

(* TODO MOVE *)
Definition test_option {A} f (o : option A) : bool :=
  match o with
  | None => true
  | Some x => f x
  end.

Definition nameless_ctx (Γ : context) : bool :=
  forallb (fun d =>
    anon d.(decl_name) &&
    test_option nameless d.(decl_body) &&
    nameless d.(decl_type)
  ) Γ.

Lemma nlctx_spec :
  forall Γ, nameless_ctx (nlctx Γ).
Proof.
  intros Γ. induction Γ as [| [na [b|] B] Γ ih].
  - reflexivity.
  - simpl. rewrite 2!nl_spec, ih. reflexivity.
  - simpl. rewrite nl_spec, ih. reflexivity.
Qed.

Lemma eq_term_upto_univ_tm_nl :
  forall Re Rle u,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ Re Rle u (nl u).
Proof.
  intros Re Rle u hRe hRle.
  induction u in Rle, hRle |- * using term_forall_list_ind.
  all: try solve [
    simpl ; try apply eq_term_upto_univ_refl ; auto ; constructor ; eauto
  ].
  - simpl. constructor.
    induction l.
    + constructor.
    + simpl. inversion X. subst. constructor ; eauto.
  - simpl. destruct p. constructor ; eauto.
    induction l.
    + constructor.
    + simpl. inversion X. subst. constructor.
      * split ; auto.
      * eapply IHl. assumption.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply X0 ; eauto.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply X0 ; eauto.
Qed.

Corollary eq_term_tm_nl :
  forall `{checker_flags} G u, eq_term G u (nl u).
Proof.
  intros flags G u.
  eapply eq_term_upto_univ_tm_nl.
  - intro. eapply eq_universe_refl.
  - intro. eapply eq_universe_refl.
Qed.

Definition nl_constant_body c :=
  Build_constant_body
    (nl c.(cst_type)) (option_map nl c.(cst_body)) c.(cst_universes).

Definition nl_one_inductive_body o :=
  Build_one_inductive_body
    o.(ind_name)
    (nl o.(ind_type))
    o.(ind_kelim)
    (map (fun '((x,y),n) => ((x, nl y), n)) o.(ind_ctors))
    (map (fun '(x,y) => (x, nl y)) o.(ind_projs)).

Definition nl_mutual_inductive_body m :=
  Build_mutual_inductive_body
    m.(ind_finite)
    m.(ind_npars)
    (nlctx m.(ind_params))
    (map nl_one_inductive_body m.(ind_bodies))
    m.(ind_universes).

Definition nl_global_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl kn cb => ConstantDecl kn (nl_constant_body cb)
  | InductiveDecl kn mib => InductiveDecl kn (nl_mutual_inductive_body mib)
  end.

Definition nlg (Σ : global_env_ext) : global_env_ext :=
  let '(Σ, φ) := Σ in
  (map nl_global_decl Σ, φ).

Fixpoint nlstack (π : stack) : stack :=
  match π with
  | ε => ε
  | App u ρ =>
    App (nl u) (nlstack ρ)
  | Fix f n args ρ =>
    Fix (map (map_def_anon nl nl) f) n (map nl args) (nlstack ρ)
  | CoFix f n args ρ =>
    CoFix (map (map_def_anon nl nl) f) n (map nl args) (nlstack ρ)
  | Case indn p brs ρ =>
    Case indn (nl p) (map (on_snd nl) brs) (nlstack ρ)
  | Proj p ρ =>
    Proj p (nlstack ρ)
  | Prod_l na B ρ =>
    Prod_l nAnon (nl B) (nlstack ρ)
  | Prod_r na A ρ =>
    Prod_r nAnon (nl A) (nlstack ρ)
  | Lambda_ty na b ρ =>
    Lambda_ty nAnon (nl b) (nlstack ρ)
  | Lambda_tm na A ρ =>
    Lambda_tm nAnon (nl A) (nlstack ρ)
  | coApp t ρ =>
    coApp (nl t) (nlstack ρ)
  end.

Lemma nlstack_appstack :
  forall args ρ,
    nlstack (appstack args ρ) = appstack (map nl args) (nlstack ρ).
Proof.
  intros args ρ.
  induction args in ρ |- *.
  - reflexivity.
  - simpl. f_equal. eapply IHargs.
Qed.

Lemma nlstack_cat :
  forall ρ θ,
    nlstack (ρ +++ θ) = nlstack ρ +++ nlstack θ.
Proof.
  intros ρ θ.
  induction ρ in θ |- *.
  all: solve [ simpl ; rewrite ?IHρ ; reflexivity ].
Qed.

Lemma stack_position_nlstack :
  forall ρ,
    stack_position (nlstack ρ) = stack_position ρ.
Proof.
  intros ρ.
  induction ρ.
  all: (simpl ; rewrite ?IHρ ; reflexivity).
Qed.

Lemma nl_it_mkLambda_or_LetIn :
  forall Γ t,
    nl (it_mkLambda_or_LetIn Γ t) =
    it_mkLambda_or_LetIn (nlctx Γ) (nl t).
Proof.
  intros Γ t.
  induction Γ as [| [na [b|] B] Γ ih] in t |- *.
  - reflexivity.
  - simpl. cbn. rewrite ih. reflexivity.
  - simpl. cbn. rewrite ih. reflexivity.
Qed.

Lemma nl_mkApps :
  forall t l,
    nl (mkApps t l) = mkApps (nl t) (map nl l).
Proof.
  intros t l.
  induction l in t |- *.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma nlctx_app_context :
  forall Γ Δ,
    nlctx (Γ ,,, Δ) = nlctx Γ ,,, nlctx Δ.
Proof.
  intros Γ Δ.
  induction Δ as [| [na [b|] B] Δ ih] in Γ |- *.
  - reflexivity.
  - simpl. f_equal. apply ih.
  - simpl. f_equal. apply ih.
Qed.

Lemma nlctx_stack_context :
  forall ρ,
    nlctx (stack_context ρ) = stack_context (nlstack ρ).
Proof.
  intro ρ. induction ρ.
  all: (simpl ; rewrite ?IHρ ; reflexivity).
Qed.

Lemma nl_subst_instance_constr :
  forall u b,
    nl (subst_instance_constr u b) = subst_instance_constr u (nl b).
Proof.
  intros u b.
  induction b using term_forall_list_ind.
  all: try (simpl ; rewrite ?IHb, ?IHb1, ?IHb2, ?IHb3 ; reflexivity).
  - simpl. f_equal. induction H.
    + reflexivity.
    + simpl. rewrite p, IHAll. reflexivity.
  - simpl. rewrite IHb1, IHb2. f_equal.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold on_snd. destruct p, x. simpl in *.
        rewrite p0. reflexivity.
      * apply IHX.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1, h2. reflexivity.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1, h2. reflexivity.
Qed.

Lemma context_position_nlctx :
  forall Γ,
    context_position (nlctx Γ) = context_position Γ.
Proof.
  intros Γ. induction Γ as [| [na [b|] A] Γ ih ].
  - reflexivity.
  - simpl. rewrite ih. reflexivity.
  - simpl. rewrite ih. reflexivity.
Qed.

Lemma xposition_nlctx :
  forall Γ π,
    xposition (nlctx Γ) π = xposition Γ π.
Proof.
  intros Γ π.
  unfold xposition.
  rewrite context_position_nlctx.
  reflexivity.
Qed.

Lemma xposition_nlstack :
  forall Γ π,
    xposition Γ (nlstack π) = xposition Γ π.
Proof.
  intros Γ π.
  unfold xposition.
  rewrite stack_position_nlstack.
  reflexivity.
Qed.

Lemma nl_zipc :
  forall t π,
    nl (zipc t π) = zipc (nl t) (nlstack π).
Proof.
  intros t π.
  induction π in t |- *.
  all: try solve [ simpl ; rewrite ?IHπ ; reflexivity ].
  all: solve [
    simpl ; rewrite IHπ ; cbn ; f_equal ;
    rewrite nl_mkApps ; reflexivity
  ].
Qed.

Lemma nl_zipx :
  forall Γ t π,
    nl (zipx Γ t π) = zipx (nlctx Γ) (nl t) (nlstack π).
Proof.
  intros Γ t π.
  unfold zipx. rewrite nl_it_mkLambda_or_LetIn. f_equal.
  apply nl_zipc.
Qed.


Lemma global_ext_levels_nlg :
  forall Σ,
    global_ext_levels (nlg Σ) = global_ext_levels Σ.
Proof.
  intros [g ?].
  cbn. unfold global_ext_levels. f_equal.
  simpl. clear - g.
  induction g. 1: reflexivity.
  simpl. f_equal. 2: assumption.
  destruct a. all: reflexivity.
Qed.

Lemma global_ext_constraints_nlg :
  forall Σ,
    global_ext_constraints (nlg Σ) = global_ext_constraints Σ.
Proof.
  intros [g ?].
  cbn. unfold global_ext_constraints.
  f_equal. simpl. clear - g.
  induction g. 1: reflexivity.
  simpl. f_equal. 2: assumption.
  destruct a. all: reflexivity.
Qed.

Lemma nl_lookup_env :
  forall Σ c,
    lookup_env (map nl_global_decl Σ) c
    = option_map nl_global_decl (lookup_env Σ c).
Proof.
  intros Σ c.
  induction Σ. 1: reflexivity.
  simpl.
  replace (global_decl_ident (nl_global_decl a))
    with (global_decl_ident a)
    by (destruct a ; reflexivity).
  destruct (ident_eq c (global_decl_ident a)).
  - reflexivity.
  - assumption.
Qed.

Lemma lookup_env_nlg :
  forall Σ c decl,
    lookup_env Σ.1 c = Some decl ->
    lookup_env (nlg Σ) c = Some (nl_global_decl decl).
Proof.
  intros [g ?] c decl h.
  cbn. rewrite nl_lookup_env.
  rewrite h. reflexivity.
Qed.

Lemma nlg_wf_local {cf : checker_flags} :
  forall Σ Γ (hΓ : wf_local Σ Γ),
    All_local_env_over
      typing
      (fun Σ Γ (_ : wf_local Σ Γ) (t T : term) (_ : Σ ;;; Γ |- t : T) =>
         nlg Σ ;;; nlctx Γ |- nl t : nl T)
      Σ Γ hΓ ->
    wf_local (nlg Σ) (nlctx Γ).
Proof.
  intros Σ Γ hΓ h.
  induction h.
  - constructor.
  - simpl. unfold map_decl_anon. cbn. constructor. 1: assumption.
    eexists. eassumption.
  - simpl. unfold map_decl_anon. cbn. constructor.
    + assumption.
    + eexists. eassumption.
    + assumption.
Qed.

Lemma nl_lift :
  forall n k t,
    nl (lift n k t) = lift n k (nl t).
Proof.
  intros n k t.
  induction t in n, k |- * using term_forall_list_ind.
  all: simpl.
  all: try congruence.
  - destruct (_ <=? _). all: reflexivity.
  - f_equal. induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - f_equal. 1-2: solve [ auto ].
    induction X. 1: reflexivity.
    simpl. f_equal. 2: assumption.
    unfold on_snd. cbn. f_equal. auto.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
Qed.

Lemma nl_subst :
  forall s k u,
    nl (subst s k u) = subst (map nl s) k (nl u).
Proof.
  intros s k u.
  induction u in s, k |- * using term_forall_list_ind.
  all: simpl.
  all: try congruence.
  - destruct (_ <=? _). 2: reflexivity.
    rewrite nth_error_map. destruct (nth_error _ _).
    + simpl. apply nl_lift.
    + rewrite map_length. reflexivity.
  - f_equal. induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - f_equal. 1-2: solve [ auto ].
    induction X. 1: reflexivity.
    simpl. f_equal. 2: assumption.
    unfold on_snd. cbn. f_equal. auto.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
Qed.

Lemma nl_eq_decl {cf:checker_flags} :
  forall φ d d',
    eq_decl φ d d' ->
    eq_decl φ (map_decl nl d) (map_decl nl d').
Proof.
  intros φ d d' [h1 h2].
  split.
  - simpl. destruct d as [? [?|] ?], d' as [? [?|] ?].
    all: cbn in *.
    all: trivial.
    apply nl_eq_term. assumption.
  - apply nl_eq_term. assumption.
Qed.

Lemma nl_eq_decl' {cf:checker_flags} :
  forall φ d d',
    eq_decl φ d d' ->
    eq_decl φ (map_decl_anon nl d) (map_decl_anon nl d').
Proof.
  intros φ d d' [h1 h2].
  split.
  - simpl. destruct d as [? [?|] ?], d' as [? [?|] ?].
    all: cbn in *.
    all: trivial.
    apply nl_eq_term. assumption.
  - apply nl_eq_term. assumption.
Qed.

Lemma nl_eq_context {cf:checker_flags} :
  forall φ Γ Γ',
    eq_context φ Γ Γ' ->
    eq_context φ (nlctx Γ) (nlctx Γ').
Proof.
  intros φ Γ Γ' h.
  unfold eq_context, nlctx.
  eapply All2_map, All2_impl.
  - eassumption.
  - apply nl_eq_decl'.
Qed.

Lemma nl_decompose_app :
  forall t,
    decompose_app (nl t)
    = let '(u, vs) := decompose_app t in (nl u, map nl vs).
Proof.
  intro t.
  unfold decompose_app.
  change [] with (map nl []) at 1. generalize (@nil term).
  induction t. all: try reflexivity.
  intro l. cbn. change (nl t2 :: map nl l) with (map nl (t2 :: l)).
  apply IHt1.
Qed.

Lemma nl_fix_context :
  forall mfix,
    nlctx (fix_context mfix) = fix_context (map (map_def_anon nl nl) mfix).
Proof.
  intro mfix.
  unfold nlctx, fix_context, mapi.
  generalize 0 at 2 4.
  induction mfix.
  - reflexivity.
  - intro n. simpl. rewrite map_app. cbn. f_equal.
    + apply IHmfix.
    + unfold map_decl_anon. cbn. rewrite nl_lift. reflexivity.
Qed.

Lemma nl_red1 :
  forall Σ Γ M N,
    red1 Σ Γ M N ->
    red1 (map nl_global_decl Σ) (nlctx Γ) (nl M) (nl N).
Proof.
  intros Σ Γ M N h.
  induction h using red1_ind_all.
  all: simpl.
  all: rewrite ?nl_lift, ?nl_subst, ?nl_subst_instance_constr.
  all: try solve [ econstructor ; eauto ].
  - constructor. unfold nlctx. rewrite nth_error_map.
    destruct (nth_error Γ i). 2: discriminate.
    cbn in *. apply some_inj in H. rewrite H. reflexivity.
  - rewrite nl_mkApps. cbn.
    replace (nl (iota_red pars c args brs))
      with (iota_red pars c (map nl args) (map (on_snd nl) brs)).
    + eapply red_iota.
    + unfold iota_red. rewrite nl_mkApps.
      rewrite map_skipn. rewrite nth_map. all: reflexivity.
  - rewrite !nl_mkApps. cbn. eapply red_fix with (narg:=narg).
    + unfold unfold_fix in *. rewrite nth_error_map.
      destruct (nth_error mfix idx). 2: discriminate.
      cbn.
      replace (isLambda (nl (dbody d))) with (isLambda (dbody d))
        by (destruct (dbody d) ; reflexivity).
      destruct (isLambda (dbody d)). 2: discriminate.
      inversion H. subst. rewrite nl_subst.
      repeat f_equal. clear.
      unfold fix_subst. rewrite map_length.
      induction #|mfix|.
      * reflexivity.
      * cbn. rewrite IHn. reflexivity.
    + unfold is_constructor in *.
      rewrite nth_error_map. destruct (nth_error args narg) ; [| discriminate ].
      cbn. unfold isConstruct_app in *. rewrite nl_decompose_app.
      destruct (decompose_app t) as [u ?].
      destruct u. all: try discriminate.
      reflexivity.
  - rewrite !nl_mkApps. simpl. eapply red_cofix_case with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - rewrite !nl_mkApps. simpl. eapply red_cofix_proj with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - econstructor.
    + unfold declared_constant in *.
      rewrite nl_lookup_env, H. reflexivity.
    + destruct decl as [? [?|] ?].
      all: cbn in *.
      all: congruence.
  - rewrite nl_mkApps. cbn. constructor.
    rewrite nth_error_map, H. reflexivity.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split. all: assumption.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [? ?]. all: assumption.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split. 1: assumption.
    cbn. congruence.
  - apply fix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context, nl_fix_context in r0. assumption.
    + cbn. congruence.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split. 1: assumption.
    cbn. congruence.
  - apply cofix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context, nl_fix_context in r0. assumption.
    + cbn. congruence.
Qed.

Lemma nl_cumul {cf:checker_flags} :
  forall Σ Γ A B,
    Σ ;;; Γ |- A <= B ->
    nlg Σ ;;; nlctx Γ |- nl A <= nl B.
Proof.
  intros Σ Γ A B h.
  induction h.
  - constructor. rewrite global_ext_constraints_nlg. apply nl_leq_term.
    assumption.
  - eapply cumul_red_l. 2: eassumption.
    destruct Σ. apply nl_red1. assumption.
  - eapply cumul_red_r. 1: eassumption.
    destruct Σ. apply nl_red1. assumption.
Qed.

Lemma nl_destArity :
  forall Γ A Δ s,
    destArity Γ A = Some (Δ, s) ->
    destArity (nlctx Γ) (nl A) = Some (nlctx Δ, s).
Proof.
  intros Γ A Δ s h.
  induction A in Γ, h |- *.
  all: simpl in *. all: try discriminate.
  - inversion h. reflexivity.
  - apply (IHA2 (Γ ,, vass na A1) h).
  - apply (IHA3 (Γ ,, vdef na A1 A2) h).
Qed.

Lemma nl_instantiate_params :
  forall params args ty,
    option_map nl (instantiate_params params args ty) =
    instantiate_params (nlctx params) (map nl args) (nl ty).
Proof.
  intros params args ty.
  unfold instantiate_params.
  assert (e :
    option_map (fun '(s, ty0) => (map nl s, nl ty0))
               (instantiate_params_subst (List.rev params) args [] ty)
    = instantiate_params_subst (List.rev (nlctx params))
                               (map nl args) [] (nl ty)
  ).
  { replace (List.rev (nlctx params)) with (nlctx (List.rev params))
      by (unfold nlctx ; rewrite map_rev ; reflexivity).
    change [] with (map nl []) at 2.
    generalize (List.rev params), (@nil term). clear.
    intros params l.
    induction params in ty, args, l |- *.
    - destruct args. all: reflexivity.
    - simpl. destruct a as [? [?|] ?].
      + simpl. destruct ty. all: try reflexivity.
        simpl. rewrite IHparams. simpl.
        rewrite nl_subst. reflexivity.
      + destruct ty. all: try reflexivity.
        destruct args.
        * reflexivity.
        * rewrite IHparams. reflexivity.
  }
  rewrite <- e.
  destruct (instantiate_params_subst _ _ _) as [[? ?]|].
  - simpl. f_equal. apply nl_subst.
  - reflexivity.
Qed.

Lemma nl_inds :
  forall kn u bodies,
    map nl (inds kn u bodies) = inds kn u (map nl_one_inductive_body bodies).
Proof.
  intros kn u bodies.
  unfold inds. rewrite map_length.
  induction #|bodies|.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma nl_decompose_prod_assum :
  forall Γ t,
    decompose_prod_assum (nlctx Γ) (nl t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (nlctx Γ, nl t).
Proof.
  intros Γ t.
  induction t in Γ |- *. all: try reflexivity.
  - apply (IHt2 (Γ ,, vass na t1)).
  - apply (IHt3 (Γ ,, vdef na t1 t2)).
Qed.

Lemma nl_it_mkProd_or_LetIn :
  forall Γ A,
    nl (it_mkProd_or_LetIn Γ A) = it_mkProd_or_LetIn (nlctx Γ) (nl A).
Proof.
  intros Γ A.
  induction Γ in A |- *.
  - reflexivity.
  - simpl. rewrite IHΓ. f_equal.
    destruct a as [? [?|] ?].
    all: reflexivity.
Qed.

Lemma nl_to_extended_list:
  forall indctx : list context_decl,
    map nl (to_extended_list indctx) = to_extended_list (nlctx indctx).
Proof.
  intros indctx. unfold to_extended_list, to_extended_list_k.
  change [] with (map nl []) at 2.
  generalize (@nil term), 0.
  induction indctx.
  - reflexivity.
  - simpl. intros l n.
    destruct a as [? [?|] ?].
    all: cbn.
    all: apply IHindctx.
Qed.

Lemma subst_instance_context_nlctx u ctx :
  subst_instance_context u (nlctx ctx) = nlctx (subst_instance_context u ctx).
Proof.
  induction ctx; cbnr.
  f_equal. 2: apply IHctx.
  clear. destruct a as [? [] ?]; unfold map_decl, map_decl_anon; cbn; f_equal.
  all: now rewrite nl_subst_instance_constr.
Qed.


Lemma typing_nlg {cf : checker_flags} :
  env_prop (fun Σ Γ t T => nlg Σ ;;; nlctx Γ |- nl t : nl T).
Proof.
  clear.
  apply typing_ind_env; cbn; intros;
    rewrite ?nl_lift, ?nl_subst, ?nl_subst_instance_constr;
    try (econstructor; eauto using nlg_wf_local; fail).
  - replace (nl (decl_type decl)) with (decl_type (map_decl_anon nl decl));
      [|destruct decl; reflexivity].
    constructor. eauto using nlg_wf_local.
    unfold nlctx. rewrite nth_error_map. now rewrite H.
  - constructor; eauto using nlg_wf_local.
    now rewrite global_ext_levels_nlg.
  - replace (nl (cst_type decl)) with (cst_type (map_constant_body nl decl));
      [|destruct decl; reflexivity].
    constructor; eauto using nlg_wf_local.
    + unfold declared_constant in *. now erewrite lookup_env_nlg; tea.
    + red. rewrite global_ext_levels_nlg, global_ext_constraints_nlg; assumption.
  - replace (nl (ind_type idecl)) with (ind_type (nl_one_inductive_body idecl));
      [|destruct idecl; reflexivity].
    destruct isdecl as [H1 H2].
    econstructor; eauto using nlg_wf_local. split.
    + eapply lookup_env_nlg in H1. eapply H1.
    + replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
          (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
      rewrite nth_error_map, H2. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg, global_ext_constraints_nlg; assumption.
  - destruct cdecl as [[id t] n]. cbn.
    rewrite nl_inds.
    eapply type_Construct with (idecl0:=nl_one_inductive_body idecl)
                               (mdecl0:=nl_mutual_inductive_body mdecl)
                               (cdecl:=(id, nl t, n))
    ; eauto using nlg_wf_local.
    + destruct isdecl as [[H1 H2] H3]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map, H2. reflexivity.
      * rewrite nth_error_map, H3. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg, global_ext_constraints_nlg; assumption.
  - rewrite nl_mkApps, map_app, map_skipn. cbn.
    eapply type_Case with  (mdecl0:=nl_mutual_inductive_body mdecl)
                           (idecl0:=nl_one_inductive_body idecl)
                           (btys0:=map (on_snd nl) btys)
                           (indctx0:=nlctx indctx)
                           (pctx0:=nlctx pctx)
                           (u0:=u)
    ; tea.
    + destruct isdecl as [HH1 HH2]. split.
      * eapply lookup_env_nlg in HH1. eapply HH1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map, HH2. reflexivity.
    + clear -H0. unfold types_of_case in *.
      set (params := instantiate_params
                       (subst_instance_context u (ind_params mdecl))
                       (firstn npar args)
                       (subst_instance_constr u (ind_type idecl))) in H0.
      replace (instantiate_params _ _ _) with (option_map nl params).
      * destruct params; [|discriminate]. simpl.
        case_eq (destArity [] t);
          [|intro HH; rewrite HH in H0; discriminate].
        intros [Δ s] H. rewrite H in H0.
        apply nl_destArity in H. cbn in H; rewrite H; clear H.
        case_eq (destArity [] pty);
          [|intro HH; rewrite HH in H0; discriminate].
        intros [Δ' s'] H. rewrite H in H0.
        apply nl_destArity in H. cbn in H; rewrite H; clear H.
        case_eq (map_option_out (build_branches_type ind mdecl idecl
                                                     (firstn npar args) u p));
          [|intro HH; rewrite HH in H0; discriminate].
        intros tys H; rewrite H in H0.
        inversion H0; subst; clear H0.
        replace (map_option_out (build_branches_type ind (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl) (firstn npar (map nl args)) u (nl p)))
          with (option_map (map (on_snd nl)) (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p))).
        now rewrite H.
        rewrite <- map_option_out_map_option_map. f_equal.
        rewrite firstn_map. generalize (firstn npar args); intro args'. clear.
        unfold build_branches_type. simpl.
        rewrite mapi_map, map_mapi. apply mapi_ext.
        intros n [[id t] k].
        rewrite <- nl_subst_instance_constr, <- nl_inds, <- nl_subst.
        rewrite subst_instance_context_nlctx.
        rewrite <- nl_instantiate_params.
        destruct (instantiate_params _ _ _); [|reflexivity].
        cbn. change (@nil context_decl) with (nlctx []) at 2.
        rewrite nl_decompose_prod_assum.
        destruct (decompose_prod_assum [] t0); cbn.
        rewrite nl_decompose_app.
        destruct (decompose_app t1) as [t11 t12]; cbn.
        case_eq (chop (ind_npars mdecl) t12).
        intros paramrels args eq.
        erewrite chop_map; tea. cbn.
        unfold on_snd. cbn. f_equal. f_equal.
        rewrite nl_it_mkProd_or_LetIn, nl_mkApps, nl_lift.
        unfold nlctx at 3; rewrite map_length. f_equal. f_equal.
        rewrite map_app. cbn. rewrite nl_mkApps. cbn. repeat f_equal.
        rewrite map_app. f_equal. apply nl_to_extended_list.
      * rewrite firstn_map. cbn. subst params.
        rewrite nl_instantiate_params. f_equal.
        now rewrite <- subst_instance_context_nlctx.
        apply nl_subst_instance_constr.
    + clear -H1. unfold check_correct_arity in *.
      rewrite global_ext_constraints_nlg.
      inversion H1; subst. cbn. constructor.
      * clear -H2. destruct H2 as [H1 H2]; cbn in *.
        destruct y as [? [?|] ?]; cbn in *; [contradiction|].
        split; cbn; tas. apply nl_eq_term in H2.
        refine (eq_rect _ (fun d => eq_term _ d _) H2 _ _).
        clear. rewrite nl_mkApps, map_app, firstn_map, !map_map.
        f_equal. rewrite nl_to_extended_list. f_equal.
        apply map_ext. intro; rewrite nl_lift; cbn.
        unfold nlctx; now rewrite map_length.
      * eapply All2_map, All2_impl; tea.
        apply nl_eq_decl'.
    + rewrite nl_mkApps in *; eassumption.
    + clear -X5. eapply All2_map, All2_impl; tea. cbn.
      clear. intros x y [[[? ?] ?] ?]. intuition eauto.
  - destruct pdecl as [pdecl1 pdecl2]; simpl.
    rewrite map_rev.
    eapply type_Proj with (mdecl0:=nl_mutual_inductive_body mdecl)
                          (idecl0:=nl_one_inductive_body idecl)
                          (pdecl:=(pdecl1, nl pdecl2)).
    + destruct isdecl as [[H1 H2] [H3 H4]]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map, H2. reflexivity.
      * rewrite nth_error_map, H3. reflexivity.
      * assumption.
    + now rewrite nl_mkApps in X2.
    + now rewrite map_length.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor.
    + eapply fix_guard_eq_term with (idx:=n). eassumption.
      constructor. clear. induction mfix. constructor.
      simpl. constructor; tas. cbn.
      repeat split; now apply eq_term_upto_univ_tm_nl.
    + now rewrite nth_error_map, H.
    + rewrite XX. revert X. clear.
      induction 1; simpl; econstructor; tas; cbn in *.
      1-2: destruct t0 as [? [? ?]]; eauto.
      now destruct t1.
    + rewrite XX. clear -X0.
      apply All_map. eapply All_impl; tea.
      clear. intros [na bd ty] [[H1 H2] H3]; simpl in *.
      split; cbn. rewrite <- nl_lift.
      rewrite fix_context_length in H3.
      now rewrite fix_context_length, map_length.
      now destruct ty.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor.
    + assumption.
    + now rewrite nth_error_map, H.
    + rewrite XX. revert X. clear.
      induction 1; simpl; econstructor; tas; cbn in *.
      1-2: destruct t0 as [? [? ?]]; eauto.
      now destruct t1.
    + rewrite XX. clear -X0.
      apply All_map. eapply All_impl; tea.
      clear. intros [na bd ty] [H1 H3]; simpl in *.
      red. cbn. rewrite <- nl_lift.
      rewrite fix_context_length in H3.
      now rewrite fix_context_length, map_length.
  - econstructor; tea.
    + destruct X2 as [[[Δ [s [H1 H2]]] HH]|?]; [left|right].
      * exists (nlctx Δ), s. split. apply nl_destArity in H1 as H1'; assumption.
        cbn in *. rewrite <- nlctx_app_context.
        eapply nlg_wf_local. eassumption.
      * destruct s as [? [? ?]]; eauto.
    + now apply nl_cumul.
Qed.

Corollary reflect_nleq_term :
  forall t t',
    reflect (nl t = nl t') (nleq_term t t').
Proof.
  intros t t'.
  destruct (reflect_upto_names t t').
  - constructor. eapply eq_term_nl_eq. assumption.
  - constructor. intro bot. apply f.
    apply eq_term_upto_univ_nl_inv.
    rewrite bot.
    apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma nleq_term_it_mkLambda_or_LetIn :
  forall Γ u v,
    nleq_term u v ->
    nleq_term (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v).
Proof.
  intros Γ u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih.
    eapply ssrbool.introT.
    + eapply reflect_nleq_term.
    + cbn. f_equal.
      eapply ssrbool.elimT.
      * eapply reflect_nleq_term.
      * assumption.
  - simpl. cbn. apply ih.
    eapply ssrbool.introT.
    + eapply reflect_nleq_term.
    + cbn. f_equal.
      eapply ssrbool.elimT.
      * eapply reflect_nleq_term.
      * assumption.
Qed.

Lemma nl_two M :
  nl (nl M) = nl M.
Proof.
  induction M using term_forall_list_ind; cbnr.
  all: rewrite ?IHM1, ?IHM2, ?IHM3, ?IHM; cbnr.
  - f_equal. induction H; cbnr. congruence.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct x; unfold on_snd; simpl in *. congruence.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *. congruence.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *. congruence.
Qed.


Local Ltac aa :=
  match goal with
  | |- ∑ _ : _, _ × ?t = _ => exists t
  end; split; [|symmetry; apply nl_two]; simpl;
  rewrite ?nl_lift, ?nl_subst, ?nl_subst_instance_constr.

Local Ltac bb :=
  repeat match goal with
  | H : ∑ _ : _, _ × ?t = _ |- _ => destruct H as [? [? ?]]
  end;
  eexists; split.

Local Ltac bb' := bb; [econstructor|]; tea; cbn.

Arguments on_snd {_ _ _} _ _/.
Arguments map_def_anon {_ _} _ _ _/.


Lemma nl_red1' Σ Γ M N :
    red1 Σ Γ M N ->
    ∑ N', red1 Σ (nlctx Γ) (nl M) N' × nl N = nl N'.
Proof.
  assert (maptwo : forall brs, map (on_snd (A:=nat) nl) (map (on_snd nl) brs)
                          = map (on_snd nl) brs). {
    intro. rewrite map_map.
    apply map_ext. intros; simpl; now rewrite nl_two. }
  intros h.
  induction h using red1_ind_all.
  all: try solve [ bb'; pose proof nl_two; congruence ].
  all: try solve [ aa; econstructor; eauto ].

  - aa. constructor. unfold nlctx. rewrite nth_error_map.
    destruct (nth_error Γ i). 2: discriminate.
    cbn in *. apply some_inj in H. rewrite H. reflexivity.
  - aa. rewrite nl_mkApps. cbn.
    replace (nl (iota_red pars c args brs))
      with (iota_red pars c (map nl args) (map (on_snd nl) brs)).
    + eapply red_iota.
    + unfold iota_red. rewrite nl_mkApps.
      rewrite map_skipn. rewrite nth_map. all: reflexivity.
  - aa. rewrite !nl_mkApps. cbn. eapply red_fix with (narg:=narg).
    + unfold unfold_fix in *. rewrite nth_error_map.
      destruct (nth_error mfix idx). 2: discriminate.
      cbn.
      replace (isLambda (nl (dbody d))) with (isLambda (dbody d))
        by (destruct (dbody d) ; reflexivity).
      destruct (isLambda (dbody d)). 2: discriminate.
      inversion H. subst. rewrite nl_subst.
      repeat f_equal. clear.
      unfold fix_subst. rewrite map_length.
      induction #|mfix|.
      * reflexivity.
      * cbn. rewrite IHn. reflexivity.
    + unfold is_constructor in *.
      rewrite nth_error_map. destruct (nth_error args narg) ; [| discriminate ].
      cbn. unfold isConstruct_app in *. rewrite nl_decompose_app.
      destruct (decompose_app t) as [u ?].
      destruct u. all: try discriminate.
      reflexivity.
  - aa. rewrite !nl_mkApps. simpl. eapply red_cofix_case with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - aa. rewrite !nl_mkApps. simpl. eapply red_cofix_proj with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - aa. rewrite nl_mkApps. constructor.
    rewrite nth_error_map, H. reflexivity.
  - assert (Y : ∑ brs'', map (on_snd nl) brs' = map (on_snd nl) brs''
    × OnOne2 (on_Trel_eq (red1 Σ (nlctx Γ)) snd fst) (map (on_snd nl) brs) brs''). {
      induction X.
      + destruct p0 as [[? [hd'' [? ?]]] ?].
        eexists ((hd'.1, hd'') :: map (on_snd nl) tl); cbn; split. congruence.
        constructor; cbn. split; tas.
      + destruct IHX as [brs'' [? ?]]. exists ((hd.1, nl hd.2) :: brs''); cbn; split.
        rewrite nl_two. congruence. now constructor. }
    destruct Y as [brs'' [? ?]].
    exists (tCase ind (nl p) (nl c) brs''); cbn; split; [|rewrite !nl_two; congruence].
    now constructor.
  - assert (Y : ∑ l'', map nl l' = map nl l''
                           × OnOne2 (red1 Σ (nlctx Γ)) (map nl l) l''). {
      induction X.
      + destruct p as [? [hd'' [? ?]]].
        eexists (hd'' :: map nl tl); cbn; split. f_equal; tas.
        rewrite map_map; apply map_ext; intro; now rewrite nl_two.
        now constructor.
      + destruct IHX as [l'' [? ?]]. exists (nl hd :: l''); cbn; split.
        rewrite nl_two. congruence. now constructor. }
    destruct Y as [l'' [? ?]].
    exists (tEvar ev l''); cbn; split. now constructor. congruence.
  - assert (Y : ∑ mfix'', map (map_def_anon nl nl) mfix1
                          = map (map_def_anon nl nl) mfix''
    × OnOne2 (fun x y => red1 Σ (nlctx Γ) (dtype x) (dtype y)
     × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y))
    (map (map_def_anon nl nl) mfix0) mfix''). {
      induction X.
      + destruct p as [[? [typ'' [? ?]]] ?]. cbn.
        eexists ({|dname:=nAnon; dtype:=typ''; dbody:=nl (dbody hd');
                   rarg:=rarg hd' |}
                   :: map (map_def_anon nl nl) tl); cbn; split.
        f_equal; simpl. rewrite nl_two. congruence.
        rewrite map_map; apply map_ext; intros []; simpl; now rewrite !nl_two.
        constructor. cbn. split; auto. congruence.
      + destruct IHX as [mfix'' [? ?]].
        exists (map_def_anon nl nl hd :: mfix''); cbn; split.
        rewrite !nl_two. congruence. now constructor. }
    destruct Y as [mfix'' [? ?]].
    exists (tFix mfix'' idx); cbn; split. now constructor. congruence.
  - assert (Y : ∑ mfix'', map (map_def_anon nl nl) mfix1
                          = map (map_def_anon nl nl) mfix''
    × OnOne2 (fun x y : def term =>
     red1 Σ (nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix0))
       (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y))
    (map (map_def_anon nl nl) mfix0) mfix''). {
 (*      induction mfix1 in mfix0, X |- *; inversion X; subst. *)
 (*      + destruct X0 as [[X1 [hd'' [X3 X4]]] X5]. *)
 (*        eexists ({|dname:=nAnon; dtype:=nl (dtype a); dbody:=hd''; *)
 (*                   rarg:=rarg a |} :: map (map_def_anon nl nl) mfix1). *)
 (*        split. cbn. f_equal. rewrite nl_two. f_equal; tas. *)
 (*        rewrite map_map; apply map_ext; intros []; simpl; now rewrite !nl_two. *)
 (*        constructor. split. *)
 (*      now rewrite nlctx_app_context, nl_fix_context in X3. *)
 (*      cbn. congruence. *)
 (*      + specialize (IHmfix1 _ X0); clear X0. *)

 (* simpl. exact X3. *)

 (*      + *)



 (*      rewrite nlctx_app_context in X. rewrite <- nl_fix_context. *)
 (*      set (c := fix_context mfix0) in *. cut (c = fix_context mfix0); cbnr. *)
 (*      clearbody c. *)
 (*      induction X; intro; subst c. *)
 (*      + destruct p as [[? [bo'' [? ?]]] ?]. simpl. *)
 (*        eexists ({|dname:=nAnon; dtype:=nl (dtype hd'); dbody:=bo''; *)
 (*                   rarg:=rarg hd' |} *)
 (*                   :: map (map_def_anon nl nl) tl); simpl; split. *)
 (*        f_equal; simpl. rewrite nl_two. congruence. *)
 (*        rewrite map_map; apply map_ext; intros []; simpl; now rewrite !nl_two. *)
 (*        constructor. simpl. split; auto. congruence. *)
 (*        (* now rewrite nlctx_app_context, nl_fix_context in r0. *) *)
 (*      + destruct IHX as [mfix'' [? ?]]. *)
 (*        exists (map_def_anon nl nl hd :: mfix''); cbn; split. *)
 (*        rewrite !nl_two. congruence. now constructor. } *)


 (* } *)
 (*    destruct Y as [mfix'' [? ?]]. *)
 (*    exists (tFix mfix'' idx); cbn; split. apply fix_red_body; tas. *)
 (*    congruence. *)



(*   - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [[? ?] ?]. split. all: assumption. *)
(*   - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [? ?]. all: assumption. *)
(*   - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [[? ?] ?]. split. 1: assumption. *)
(*     cbn. congruence. *)
(*   - apply fix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [[? ?] ?]. split. *)
(*     + rewrite nlctx_app_context, nl_fix_context in r0. assumption. *)
(*     + cbn. congruence. *)
(*   - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [[? ?] ?]. split. 1: assumption. *)
(*     cbn. congruence. *)
(*   - apply cofix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption. *)
(*     cbn. intros x y [[? ?] ?]. split. *)
(*     + rewrite nlctx_app_context, nl_fix_context in r0. assumption. *)
(*     + cbn. congruence. *)
(* Qed. *)
Admitted.
