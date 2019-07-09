(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From MetaCoq.Template
Require Import config monad_utils utils AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICCumulativity PCUICPosition PCUICUnivSubst.
From Equations Require Import Equations.
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

Definition map_def_anon {A B : Set} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := nAnon ;
     dtype := tyf d.(dtype) ;
     dbody := bodyf d.(dbody) ;
     rarg := d.(rarg) |}.

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

Derive Signature for eq_term_upto_univ.
Derive NoConfusion NoConfusionHom for term.

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

Lemma All2_Forall2 {A} (P : A -> A -> Prop) l l' :
  All2 P l l' -> Forall2 P l l'.
Proof. induction 1; constructor; auto. Qed.

Lemma nameless_eq_term_spec :
  forall `{checker_flags} u v,
    nameless u ->
    nameless v ->
    eq_term_upto_univ eq eq u v ->
    u = v.
Proof.
  intros flags u v hu hv e.
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
    eapply eq_univ_make. eapply All2_Forall2. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. apply All2_Forall2; assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. apply All2_Forall2; assumption.
  - f_equal ; try solve [ ih ].
    revert brs' H3 H0 a.
    induction l ; intros brs' h1 h2 h.
    + destruct brs' ; inversion h. reflexivity.
    + destruct brs' ; inversion h. subst.
      cbn in h1, h2. destruct_andb.
      inversion X. subst.
      f_equal.
      * destruct a, p. cbn in *. destruct H6. subst.
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

Local Ltac ih2 :=
  lazymatch goal with
  | ih : forall Rle v, _ -> eq_term_upto_univ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (nl ?u) _ =>
    eapply ih ; assumption
  end.

(* TODO Instead prove eq_term t (nl t) + symmetry and transitivity *)
Lemma eq_term_upto_univ_nl :
  forall `{checker_flags} Re Rle u v,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ Re Rle u v ->
    eq_term_upto_univ Re Rle (nl u) (nl v).
Proof.
  intros flags Re Rle u v hRe hRle h.
  induction u in v, h, Rle, hRle |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: try (simpl ; constructor ; try ih2 ; assumption).
  + cbn. constructor.
    eapply All2_map. solve_all.
  + cbn. constructor ; try ih2. solve_all.
  + cbn. constructor ; try ih2. solve_all.
  + cbn. constructor ; try ih2. solve_all.
Qed.

Corollary eq_term_nl_eq :
  forall `{checker_flags} u v,
    eq_term_upto_univ eq eq u v ->
    nl u = nl v.
Proof.
  intros flags u v h.
  eapply nameless_eq_term_spec.
  - eapply nl_spec.
  - eapply nl_spec.
  - eapply eq_term_upto_univ_nl.
    + intro. reflexivity.
    + intro. reflexivity.
    + assumption.
Qed.

Local Ltac ih3 :=
  lazymatch goal with
  | ih : forall Rle v, _ -> eq_term_upto_univ _ _ (nl ?u) _ -> _
    |- eq_term_upto_univ _ _ ?u _ =>
    eapply ih ; assumption
  end.

(* TODO Move *)
Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x => R (f x) ∘ g) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  - constructor.
  - constructor.
    + inversion h. subst. assumption.
    + eapply IHl. inversion h. assumption.
Qed.

Lemma eq_term_upto_univ_nl_inv :
  forall `{checker_flags} Re Rle u v,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ Re Rle (nl u) (nl v) ->
    eq_term_upto_univ Re Rle u v.
Proof.
  intros flags Re Rle u v hRe hRle h.
  induction u in v, h, Rle, hRle |- * using term_forall_list_ind.
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

Definition map_decl_anon f (d : context_decl) :=
  {| decl_name := nAnon ;
     decl_body := option_map f d.(decl_body) ;
     decl_type := f d.(decl_type)
  |}.

Definition nlctx (Γ : context) : context :=
  map (map_decl_anon nl) Γ.

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
  forall `{checker_flags} Re Rle u,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ Re Rle u (nl u).
Proof.
  intros flags Re Rle u hRe hRle.
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
  forall `{checker_flags} G u,
    eq_term G u (nl u).
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
    m.(ind_npars)
    (nlctx m.(ind_params))
    (map nl_one_inductive_body m.(ind_bodies))
    m.(ind_universes).

Definition nl_global_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl kn cb => ConstantDecl kn (nl_constant_body cb)
  | InductiveDecl kn mib => InductiveDecl kn (nl_mutual_inductive_body mib)
  end.

Definition nlg (Σ : global_context) : global_context :=
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