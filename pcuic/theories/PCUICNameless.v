(* Distributed under the terms of the MIT license. *)
From Coq Require Import RelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICTyping PCUICPosition PCUICUnivSubst
     PCUICContextRelation
     PCUICSigmaCalculus (* for context manipulations *).
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Implicit Types cf : checker_flags.

(** Typing / conversion does not rely on name annotations of binders.

  We prove this by constructing a type-preserving translation to 
  terms where all binders are anonymous. An alternative would be to 
  be parametrically polymorphic everywhere on the binder name type.
  This would allow to add implicit information too. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Definition anon (na : name) : bool :=
  match na with
  | nAnon => true
  | nNamed s => false
  end.

Definition banon (na : binder_annot name) : bool := anon na.(binder_name).

Definition nameless_decl nameless (d : context_decl) :=
  banon (decl_name d) && nameless d.(decl_type) &&
  option_default nameless d.(decl_body) true.

Fixpoint nameless (t : term) : bool :=
  match t with
  | tRel n => true
  | tVar n => true
  | tEvar n l => forallb nameless l
  | tSort s => true
  | tProd na A B => banon na && nameless A && nameless B
  | tLambda na A b => banon na && nameless A && nameless b
  | tLetIn na b B t => banon na && nameless b && nameless B && nameless t
  | tApp u v => nameless u && nameless v
  | tConst c u => true
  | tInd i u => true
  | tConstruct i n u => true
  | tCase ci p c brs =>
    forallb nameless p.(pparams) && 
    forallb (nameless_decl nameless) p.(pcontext) &&
    nameless p.(preturn) && nameless c && 
    forallb (fun b => forallb (nameless_decl nameless) b.(bcontext) && nameless b.(bbody)) brs
  | tProj p c => nameless c
  | tFix mfix idx =>
    forallb (fun d => banon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tCoFix mfix idx =>
    forallb (fun d => banon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tPrim _ => true
  end.

Notation nameless_ctx := (forallb (nameless_decl nameless)).

Definition anonymize (b : binder_annot name) : binder_annot name :=  
  map_binder_annot (fun _ => nAnon) b.

Definition map_def_anon {A B} (tyf bodyf : A -> B) (d : def A) := {|
  dname := anonymize d.(dname) ;
  dtype := tyf d.(dtype) ;
  dbody := bodyf d.(dbody) ;
  rarg  := d.(rarg)
|}.

Definition map_decl_anon (f : term -> term) (d : context_decl) := {|
  decl_name := anonymize d.(decl_name) ;
  decl_body := option_map f d.(decl_body) ;
  decl_type := f d.(decl_type)
|}.

Definition nl_predicate (nl : term -> term) (p : predicate term) : predicate term :=
  {| pparams := map nl p.(pparams);
     puinst := p.(puinst);
     pcontext := map (map_decl_anon nl) p.(pcontext);
     preturn := nl p.(preturn); |}.

Definition nl_branch (nl : term -> term) (b : branch term) : branch term :=
  {| bcontext := map (map_decl_anon nl) b.(bcontext);
     bbody := nl b.(bbody); |}.

Fixpoint nl (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar n => tVar n
  | tEvar n l => tEvar n (map nl l)
  | tSort s => tSort s
  | tProd na A B => tProd (anonymize na) (nl A) (nl B)
  | tLambda na A b => tLambda (anonymize na) (nl A) (nl b)
  | tLetIn na b B t => tLetIn (anonymize na) (nl b) (nl B) (nl t)
  | tApp u v => tApp (nl u) (nl v)
  | tConst c u => tConst c u
  | tInd i u => tInd i u
  | tConstruct i n u => tConstruct i n u
  | tCase ci p c brs => tCase ci (nl_predicate nl p) (nl c) (map (nl_branch nl) brs)
  | tProj p c => tProj p (nl c)
  | tFix mfix idx => tFix (map (map_def_anon nl nl) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def_anon nl nl) mfix) idx
  | tPrim p => tPrim p
  end.

Definition nlctx (Γ : context) : context :=
  map (map_decl_anon nl) Γ.

Definition nl_constant_body c :=
  Build_constant_body
    (nl c.(cst_type)) (option_map nl c.(cst_body)) c.(cst_universes).

Definition nl_constructor_body c :=
  {| cstr_name := c.(cstr_name) ;   
     cstr_args := nlctx c.(cstr_args);
     cstr_indices := map nl c.(cstr_indices);
     cstr_type := nl c.(cstr_type);
     cstr_arity := c.(cstr_arity) |}.

Definition nl_one_inductive_body o :=
  Build_one_inductive_body
    o.(ind_name)
    (nlctx o.(ind_indices))
    o.(ind_sort)
    (nl o.(ind_type))
    o.(ind_kelim)
    (map nl_constructor_body o.(ind_ctors))
    (map (fun '(x,y) => (x, nl y)) o.(ind_projs))
    o.(ind_relevance).

Definition nl_mutual_inductive_body m :=
  Build_mutual_inductive_body
    m.(ind_finite)
    m.(ind_npars)
    (nlctx m.(ind_params))
    (map nl_one_inductive_body m.(ind_bodies))
    m.(ind_universes) m.(ind_variance).

Definition nl_global_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cb => ConstantDecl (nl_constant_body cb)
  | InductiveDecl mib => InductiveDecl (nl_mutual_inductive_body mib)
  end.

Definition nl_global_env (Σ : global_env) : global_env :=
  (map (on_snd nl_global_decl) Σ).

Definition nlg (Σ : global_env_ext) : global_env_ext :=
  let '(Σ, φ) := Σ in
  (nl_global_env Σ, φ).

Ltac destruct_one_andb :=
  lazymatch goal with
  | h : is_true (_ && _) |- _ =>
    apply andb_and in h ; destruct h as [? ?]
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
  | ih : forall (v : term) (napp : nat), _ -> _ -> eq_term_upto_univ_napp _ _ _ _ _ _ -> ?u = _
    |- ?u = ?v =>
    eapply ih ; eassumption
  end.

Lemma banon_spec na : banon na -> na = {| binder_name := nAnon; binder_relevance := na.(binder_relevance) |}.
Proof.
  unfold banon, anon; destruct na; simpl; try congruence.
  destruct binder_name; auto. congruence.
Qed.

Lemma banon_eq_binder_annot na na' : banon na -> banon na' -> eq_binder_annot na na' -> na = na'.
Proof.
  intros ->%banon_spec ->%banon_spec.
  now unfold eq_binder_annot; simpl; intros ->.
Qed.

Lemma nameless_eqctx_IH P ctx ctx' :
  nameless_ctx ctx -> nameless_ctx ctx' ->
  eq_context_gen upto_names' upto_names' ctx ctx' ->
  onctx P ctx ->
  (forall napp x, P x ->
    forall y, nameless x -> nameless y ->
    eq_term_upto_univ_napp [] eq eq napp x y -> x = y) ->
  ctx = ctx'.
Proof.
  solve_all.
  induction X; auto.
  all:destruct p; depelim H0; depelim X0; auto; f_equal; auto.
  - destruct p.
    unfold nameless_decl in i, i0; rtoProp.
    f_equal.
    * eapply banon_eq_binder_annot; eauto.
    * simpl in *.
      eapply H1; eauto. apply o.
  - destruct p as [? [? ?]].
    unfold nameless_decl in i, i0; rtoProp.
    f_equal.
    * eapply banon_eq_binder_annot; eauto.
    * simpl in *.
      eapply H1; eauto. 
    * simpl in *. eapply H1; eauto.
Qed.

Lemma nameless_eq_term_spec :
  forall u v napp,
    nameless u ->
    nameless v ->
    eq_term_upto_univ_napp [] eq eq napp u v ->
    u = v.
Proof.
  intros u v napp hu hv e.
  revert v napp hu hv e.
  induction u using term_forall_list_ind ; intros v napp hu hv e.
  all: dependent destruction e.
  all: cbn in hu, hv ; destruct_andb ; anonify.
  all: try reflexivity.
  all: try solve [ f_equal ; try ih ; try assumption; try now apply banon_eq_binder_annot].
  - f_equal. cbn in hu, hv.
    revert args' hu hv a. induction l ; intros args' hu hv h.
    + destruct args' ; try solve [ inversion h ].
      reflexivity.
    + destruct args' ; try solve [ inversion h ].
      inversion h. subst.
      inversion X. subst.
      cbn in hu, hv. destruct_andb.
      f_equal.
      * eapply H0 ; eauto.
      * eapply IHl ; assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    * destruct e as [eqpar [eqinst [eqctx eqret]]].
      destruct X as [? [? ?]]. 
      destruct p, p'; simpl in *. f_equal.
      + apply All2_eq; solve_all.
      + red in eqinst.
        apply Forall2_eq. eapply Forall2_map_inv in eqinst.
        eapply (Forall2_impl eqinst); solve_all.
        now apply Universe.make_inj in H.
      + simpl in *.
        eapply nameless_eqctx_IH; eauto.
      + ih.
    * revert brs' H3 H0 a.
      induction l ; intros brs' h1 h2 h.
      + destruct brs' ; inversion h. reflexivity.
      + destruct brs' ; inversion h. subst.
        cbn in h1, h2. destruct_andb.
        inversion X. subst. simpl in H5.
        move/andb_and: H5 => [/andb_and [Hac Hab] Hl].
        apply forallb_All in Hac.
        f_equal.
        ++ destruct a, b. cbn in *. destruct X1.
           depelim h. destruct p0. depelim X0. simpl in *.
           destruct p0 as [].
           destruct X4.
           f_equal; try ih.
           { eapply nameless_eqctx_IH; eauto; solve_all. } 
        ++ eapply IHl ; tas. now depelim X0.
  - f_equal ; try solve [ ih ].
    revert mfix' H1 H2 H H0 a.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct X0 as [[[? ?] ?] ?].
        destruct H0 as [Hty Hbod].
        unfold test_def in H4, H. cbn in H4, H.
        destruct_andb.
        f_equal.
        -- now apply banon_eq_binder_annot.
        -- eapply Hty; eassumption.
        -- eapply Hbod ; eassumption.
        -- eassumption.
      * eapply IHm ; assumption.
  - f_equal ; try solve [ ih ].
    revert mfix' H1 H2 H H0 a.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct X0 as [[[? ?] ?] ?].
        destruct H0 as [Hty Hbod].
        unfold test_def in H4, H. cbn in H4, H.
        destruct_andb. anonify.
        f_equal.
        -- now apply banon_eq_binder_annot.
        -- eapply Hty; eassumption.
        -- eapply Hbod ; eassumption.
        -- assumption.
      * eapply IHm ; assumption.
Qed.

Lemma banon_list l : forallb (banon ∘ anonymize) l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma nl_spec :
  forall u, nameless (nl u).
Proof.
  intros u. induction u using term_forall_list_ind.
  all: try reflexivity.
  all: try (simpl ; repeat (eapply andb_true_intro ; split) ; assumption).
  - cbn. eapply All_forallb. eapply All_map. assumption.
  - destruct X as [? [? ?]].
    simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    * eapply All_forallb, All_map; assumption.
    * rewrite forallb_map.
      eapply All_forallb. unfold ondecl in *. solve_all.
      rewrite /nameless_decl /= a0.
      destruct (decl_body x); simpl in *; auto.
    * induction l.
      + reflexivity.
      + cbn. depelim X0. destruct p0.
        repeat (eapply andb_true_intro ; split) ; try assumption.
        ++ rewrite forallb_map.
           eapply All_forallb. unfold ondecl in *; solve_all.
           rewrite /nameless_decl /= a2.
          destruct (decl_body x); simpl in *; auto.
        ++ eapply IHl. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H0.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H0.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
Qed.

Lemma nl_lookup_env :
  forall Σ c,
    lookup_env (nl_global_env Σ) c
    = option_map nl_global_decl (lookup_env Σ c).
Proof.
  intros Σ c.
  induction Σ. 1: reflexivity.
  simpl.
  unfold eq_kername; destruct kername_eq_dec; subst.
  - reflexivity.
  - assumption.
Qed.

Lemma nl_destArity :
  forall Γ A,
    destArity (nlctx Γ) (nl A) =
    option_map (fun '(ctx, s) => (nlctx ctx, s)) (destArity Γ A).
Proof.
  intros Γ A.
  induction A in Γ |- *.
  all: simpl in *. all:auto.
  - apply (IHA2 (Γ ,, vass na A1)).
  - apply (IHA3 (Γ ,, vdef na A1 A2)).
Qed.

Lemma nl_context_assumptions ctx : context_assumptions (nlctx ctx) = context_assumptions ctx.
Proof.
  induction ctx; simpl; auto.
  destruct a as [na [b|] ty] => /= //.
  f_equal; auto.
Qed.

Lemma global_variance_nl_sigma_mon {Σ gr napp} :
  global_variance (nl_global_env Σ) gr napp =
  global_variance Σ gr napp.
Proof.
  rewrite /global_variance /lookup_constructor /lookup_inductive /lookup_minductive.
  destruct gr as [|ind|[ind i]|] => /= //.
  - rewrite nl_lookup_env.
    destruct lookup_env => /= //.
    destruct g; simpl => //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite (nl_destArity []).
    destruct (destArity [] (ind_type o)) as [[ctx s]|] eqn:da => /= //.
    now rewrite nl_context_assumptions.
  - rewrite nl_lookup_env.
    destruct lookup_env => /= //.
    destruct g; simpl => //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed.

Lemma R_global_instance_nl Σ Re Rle gr napp :
  CRelationClasses.subrelation (R_global_instance Σ Re Rle gr napp)
       (R_global_instance (nl_global_env Σ) Re Rle gr napp).
Proof.
  intros t t'.
  unfold R_global_instance.
  now rewrite global_variance_nl_sigma_mon.
Qed.

Lemma eq_context_nl_IH Σ Re Rle ctx ctx' :
  (forall (napp : nat) (t t' : term)
        (Rle : Universe.t -> Universe.t -> Prop),
      eq_term_upto_univ_napp Σ Re Rle napp t t' ->
      eq_term_upto_univ_napp (nl_global_env Σ) Re Rle napp
        (nl t) (nl t')) ->
  eq_context_gen (eq_term_upto_univ Σ Re Re)
    (eq_term_upto_univ Σ Re Rle) ctx ctx' ->
  eq_context_gen (eq_term_upto_univ (nl_global_env Σ) Re Re)
    (eq_term_upto_univ (nl_global_env Σ) Re Rle)
    (map (map_decl_anon nl) ctx)
    (map (map_decl_anon nl) ctx').
Proof.
  intros aux H.
  induction H; simpl; constructor; simpl; destruct p; simpl; 
  intuition (constructor; auto).
Defined.

Lemma nl_eq_term_upto_univ :
  forall Σ Re Rle napp t t',
    eq_term_upto_univ_napp Σ Re Rle napp t t' ->
    eq_term_upto_univ_napp (nl_global_env Σ) Re Rle napp (nl t) (nl t').
Proof.
  intros Σ Re Rle napp t t' h.
  revert napp t t' Rle h. fix aux 5.
  intros napp t t' Rle h.
  destruct h.
  all: simpl.
  all: try solve [ econstructor ; eauto ].
  - econstructor.
    induction a.
    + constructor.
    + simpl. econstructor. all: eauto.
  - econstructor. all: try solve [ eauto ].
    eapply R_global_instance_nl; eauto.
  - econstructor. all: try solve [ eauto ].
    eapply R_global_instance_nl; eauto.
  - econstructor; eauto.
    + red. destruct e; intuition auto; simpl.
      * induction a0; constructor; auto.
      * apply eq_context_nl_IH; tas.
      * apply aux. auto.
    + induction a; constructor; auto.
      intuition auto; simpl.
      * apply eq_context_nl_IH; tas.
      * destruct x, y; simpl in *. apply aux; auto.
  - econstructor; eauto.
    induction a; constructor; auto.
    intuition auto.
    * destruct x, y; simpl in *. apply aux; auto.
    * destruct x, y; simpl in *. apply aux; auto.
  - econstructor; eauto.
    induction a; constructor; auto.
    intuition auto.
    * destruct x, y; simpl in *. apply aux; auto.
    * destruct x, y; simpl in *. apply aux; auto.
Qed.

Lemma eq_context_nl Σ Re Rle ctx ctx' :
  eq_context_gen (eq_term_upto_univ Σ Re Re)
    (eq_term_upto_univ Σ Re Rle) ctx ctx' ->
  eq_context_gen
    (eq_term_upto_univ (nl_global_env Σ) Re Re)
    (eq_term_upto_univ (nl_global_env Σ) Re Rle)
    (nlctx ctx) (nlctx ctx').
Proof.
  intros H.
  induction H; constructor; simpl; destruct p; intuition 
    (constructor; auto using nl_eq_term_upto_univ).
Qed.

Lemma nl_leq_term {cf:checker_flags} Σ:
  forall φ t t',
    leq_term Σ φ t t' ->
    leq_term (nl_global_env Σ) φ (nl t) (nl t').
Proof.
  intros. apply nl_eq_term_upto_univ. assumption.
Qed.

Lemma nl_eq_term {cf:checker_flags} Σ:
  forall φ t t',
    eq_term Σ φ t t' ->
    eq_term (nl_global_env Σ) φ (nl t) (nl t').
Proof.
  intros. apply nl_eq_term_upto_univ. assumption.
Qed.

Lemma nl_compare_term {cf:checker_flags} le Σ:
  forall φ t t',
    compare_term le Σ φ t t' ->
    compare_term le (nl_global_env Σ) φ (nl t) (nl t').
Proof.
  destruct le; intros.
  - apply nl_leq_term. assumption.
  - apply nl_eq_term. assumption.
Qed.

Corollary eq_term_nl_eq :
  forall u v,
    eq_term_upto_univ [] eq eq u v ->
    nl u = nl v.
Proof.
  intros u v h.
  eapply nameless_eq_term_spec.
  - eapply nl_spec.
  - eapply nl_spec.
  - now eapply (nl_eq_term_upto_univ []).
Qed.

Local Ltac ih3 :=
  lazymatch goal with
  | ih : forall Rle napp v, eq_term_upto_univ_napp _ _ _ _ (nl ?u) _ -> _
    |- eq_term_upto_univ_napp _ _ _ _ ?u _ =>
    eapply ih ; assumption
  end.

Lemma eq_context_nl_inv_IH Σ Re ctx ctx' :
  onctx
  (fun u : term =>
 forall (Rle : Universe.t -> Universe.t -> Prop) 
   (napp : nat) (v : term),
 eq_term_upto_univ_napp Σ Re Rle napp (nl u) (nl v) ->
 eq_term_upto_univ_napp Σ Re Rle napp u v) ctx ->
 eq_context_gen 
 (eq_term_upto_univ Σ Re Re)
 (eq_term_upto_univ Σ Re Re)
 (map (map_decl_anon nl) ctx)
 (map (map_decl_anon nl) ctx') ->
 eq_context_gen (eq_term_upto_univ Σ Re Re)
    (eq_term_upto_univ Σ Re Re) ctx ctx'.
Proof.
  intros Hctx. unfold ondecl in *.
  induction ctx as [|[na [b|] ty] Γ] in ctx', Hctx |- *; 
  destruct ctx' as [|[na' [b'|] ty'] Δ]; simpl; intros H;
  depelim H; constructor; simpl in *; depelim Hctx; intuition eauto.
  * depelim c; constructor; auto.
  * depelim c.
  * depelim c.
  * depelim c; constructor; auto.
Qed.

Lemma eq_term_upto_univ_nl_inv :
  forall Σ Re Rle napp u v,
    eq_term_upto_univ_napp Σ Re Rle napp (nl u) (nl v) ->
    eq_term_upto_univ_napp Σ Re Rle napp u v.
Proof.
  intros Σ Re Rle napp u v h.
  induction u in napp, v, h, Rle |- * using term_forall_list_ind.
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
    + red. destruct e; solve_all.
      * simpl in a0. eapply All2_map_inv in a0. solve_all.
      * eapply eq_context_nl_inv_IH; tea.
    + apply All2_map_inv in a. solve_all.
      eapply eq_context_nl_inv_IH; tea.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
Qed.

Lemma nlctx_spec :
  forall Γ, nameless_ctx (nlctx Γ).
Proof.
  intros Γ. induction Γ as [| [na [b|] B] Γ ih].
  - reflexivity.
  - simpl. rewrite /nameless_decl /= 2!nl_spec ih. reflexivity.
  - simpl. rewrite /nameless_decl /= nl_spec ih. reflexivity.
Qed.

Lemma binder_anonymize n : eq_binder_annot n (anonymize n).
Proof. destruct n; reflexivity. Qed.
Hint Resolve binder_anonymize : core.
Hint Constructors compare_decls : core.
Local Hint Unfold map_decl_anon : core.

Lemma eq_term_upto_univ_tm_nl :
  forall Σ Re Rle napp u,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ_napp Σ Re Rle napp u (nl u).
Proof.
  intros Σ Re Rle napp u hRe hRle.
  induction u in napp, Rle, hRle |- * using term_forall_list_ind.
  all: try solve [
    simpl ; try apply eq_term_upto_univ_refl ; auto ; constructor ; eauto
  ].
  - simpl. constructor.
    induction l.
    + constructor.
    + simpl. inversion X. subst. constructor ; eauto.
  - simpl. destruct p. constructor ; eauto.
    * destruct X; red; simpl in *; intuition auto.
      + induction a; constructor; auto.
      + reflexivity.
      + clear -a0 hRe hRle. induction a0.
        { constructor; auto. }
        destruct x as [na [b|] ty]; simpl; constructor; auto; 
          destruct p; simpl in *; intuition (simpl; auto);
          constructor; auto.
    * induction l.
      + constructor.
      + simpl. depelim X0. destruct p.
        simpl in *. repeat constructor.
        ++ simpl.
          clear -hRe hRle a0.
          induction a0; [constructor; auto|].
          destruct x as [na [b|] ty]; simpl; constructor; auto; 
          destruct p; simpl in *; intuition auto; constructor; auto.
        ++ auto.
        ++ eapply IHl. assumption.
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
  forall `{checker_flags} Σ G u, eq_term Σ G u (nl u).
Proof.
  intros flags Σ G u.
  eapply eq_term_upto_univ_tm_nl.
  - intro. eapply eq_universe_refl.
  - intro. eapply eq_universe_refl.
Qed.

(*
Fixpoint nlstack (π : stack) : stack :=
  match π with
  | ε => ε
  | App u ρ =>
    App (nl u) (nlstack ρ)
  | Fix f n args ρ =>
    Fix (map (map_def_anon nl nl) f) n (map nl args) (nlstack ρ)
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ =>
    Fix_mfix_ty (anonymize na) (nl bo) ra (map (map_def_anon nl nl) mfix1) (map (map_def_anon nl nl) mfix2) idx (nlstack ρ)
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ =>
    Fix_mfix_bd (anonymize na) (nl ty) ra (map (map_def_anon nl nl) mfix1) (map (map_def_anon nl nl) mfix2) idx (nlstack ρ)
  | CoFix f n args ρ =>
    CoFix (map (map_def_anon nl nl) f) n (map nl args) (nlstack ρ)
  | CoFix_mfix_ty na bo ra mfix1 mfix2 idx ρ =>
    CoFix_mfix_ty (anonymize na) (nl bo) ra (map (map_def_anon nl nl) mfix1) (map (map_def_anon nl nl) mfix2) idx (nlstack ρ)
  | CoFix_mfix_bd na ty ra mfix1 mfix2 idx ρ =>
    CoFix_mfix_bd (anonymize na) (nl ty) ra (map (map_def_anon nl nl) mfix1) (map (map_def_anon nl nl) mfix2) idx (nlstack ρ)
  | Case_pars ci pars1 pars2 pinst pctx pret c brs ρ =>
    Case_pars ci (map nl pars1) (map nl pars2) pinst (nlctx pctx) (nl pret) 
    (nl c) (map (nl_branch nl) brs) (nlstack ρ)
  | Case_p ci pars pinst pctx c brs ρ =>
    Case_p ci (map nl pars) pinst (nlctx pctx) (nl c) (map (nl_branch nl) brs) (nlstack ρ)
  | Case ci p brs ρ =>
    Case ci (nl_predicate nl p) (map (nl_branch nl) brs) (nlstack ρ)
  | Case_brs ci p c m brs1 brs2 ρ =>
    Case_brs
      ci (nl_predicate nl p) (nl c) (nlctx m)
      (map (nl_branch nl) brs1) (map (nl_branch nl) brs2) (nlstack ρ)
  | Proj p ρ =>
    Proj p (nlstack ρ)
  | Prod_l na B ρ =>
    Prod_l (anonymize na) (nl B) (nlstack ρ)
  | Prod_r na A ρ =>
    Prod_r (anonymize na) (nl A) (nlstack ρ)
  | Lambda_ty na b ρ =>
    Lambda_ty (anonymize na) (nl b) (nlstack ρ)
  | Lambda_tm na A ρ =>
    Lambda_tm (anonymize na) (nl A) (nlstack ρ)
  | LetIn_bd na B u ρ =>
    LetIn_bd (anonymize na) (nl B) (nl u) (nlstack ρ)
  | LetIn_ty na b u ρ =>
    LetIn_ty (anonymize na) (nl b) (nl u) (nlstack ρ)
  | LetIn_in na b B ρ =>
    LetIn_in (anonymize na) (nl b) (nl B) (nlstack ρ)
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
  all: try solve [ simpl ; rewrite ?IHρ ; reflexivity ].
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
  - simpl. rewrite IHρ. rewrite map_length. reflexivity.
Qed.
*)

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

Lemma nl_subst_instance :
  forall u b,
    nl (subst_instance u b) = subst_instance u (nl b).
Proof.
  intros u b.
  rewrite /subst_instance /=.
  induction b using term_forall_list_ind.
  all: try (simpl ; rewrite ?IHb ?IHb1 ?IHb2 ?IHb3 ; reflexivity).
  - simpl. f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. rewrite p IHAll. reflexivity.
  - simpl. rewrite IHb. f_equal.
    * unfold nl_predicate, map_predicate. simpl. f_equal; solve_all. simpl.
      unfold ondecl in *; solve_all.
      unfold map_decl_anon, map_decl; destruct x as [na [bod|] ty]; simpl in *;
        f_equal; auto. f_equal; auto.
    * induction X0.
      + reflexivity.
      + simpl. f_equal.
        ++ destruct x. simpl in *. unfold nl_branch, map_branch.
          simpl. f_equal; solve_all.
          unfold ondecl in *; solve_all.
          unfold map_decl_anon, map_decl; destruct x as [na [bod|] ty]; simpl in *;
            f_equal; auto. f_equal; auto.
        ++ apply IHX0.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1 h2. reflexivity.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1 h2. reflexivity.
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

(*
Lemma xposition_nlstack :
  forall Γ π,
    xposition Γ (nlstack π) = xposition Γ π.
Proof.
  intros Γ π.
  unfold xposition.
  rewrite stack_position_nlstack.
  reflexivity.
Qed.
*)

(*
Lemma nl_zipc :
  forall t π,
    nl (zipc t π) = zipc (nl t) (nlstack π).
Proof.
  intros t π.
  induction π in t |- *.
  all: try solve [ simpl ; rewrite ?IHπ ; reflexivity ].
  all: try solve [
    simpl ; rewrite IHπ ; cbn ; f_equal ;
    rewrite nl_mkApps ; reflexivity
  ].
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite map_app. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite map_app. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite map_app. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite map_app. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal.
    f_equal. unfold nl_predicate; simpl; f_equal; solve_all.
    rewrite map_app. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal.
    f_equal. unfold nl_predicate, nlctx; simpl; f_equal; solve_all.
    now rewrite map_app /=. 
Qed.

Lemma nl_zipx :
  forall Γ t π,
    nl (zipx Γ t π) = zipx (nlctx Γ) (nl t) (nlstack π).
Proof.
  intros Γ t π.
  unfold zipx. rewrite nl_it_mkLambda_or_LetIn. f_equal.
  apply nl_zipc.
Qed.
*)

Lemma global_ext_levels_nlg :
  forall Σ,
    global_ext_levels (nlg Σ) = global_ext_levels Σ.
Proof.
  intros [g ?].
  cbn. unfold global_ext_levels. f_equal.
  simpl. clear - g.
  induction g. 1: reflexivity.
  simpl. f_equal. 2: assumption.
  destruct a. simpl. destruct g0. all: reflexivity.
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
  destruct a as [kn []]; reflexivity.
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
    eexists. exact p.
  - simpl. unfold map_decl_anon. cbn. constructor.
    + assumption.
    + eexists. exact p0.
    + assumption.
Qed.

Lemma All_mapi_spec {A B} {P : A -> Type} {l} {f g : nat -> A -> B} {n} :
  All P l -> (forall n x, P x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1 in n |- *; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.
Hint Resolve All_mapi_spec : all.

Lemma nl_lift :
  forall n k t,
    nl (lift n k t) = lift n k (nl t).
Proof.
  intros n k t.
  induction t in n, k |- * using term_forall_list_ind.
  all: simpl.
  all: try congruence.
  - f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - rewrite /map_predicate_k /= map_length.
    f_equal; auto.
    * unfold nl_predicate, map_predicate; simpl; f_equal; solve_all.
      eapply All_mapi_spec; [tea|].
      intros i x []. rewrite /map_decl_anon /map_decl /shiftf /=.
      f_equal; auto. rewrite !option_map_two.
      destruct (decl_body x) => /= //. f_equal; auto.
    * induction X0. 1: reflexivity.
      simpl. f_equal. 2: assumption.
      unfold nl_branch, map_branch_k. cbn. f_equal; auto; solve_all.
      eapply All_mapi_spec; [tea|].
      intros i' x' []. rewrite /map_decl_anon /map_decl /shiftf /=.
      f_equal; auto. rewrite !option_map_two.
      destruct (decl_body x') => /= //. f_equal; auto.
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

Lemma nlctx_fix_context_alt :
  forall l,
    nlctx (fix_context_alt l) =
    fix_context_alt (map (fun d => (anonymize d.1, nl d.2)) l).
Proof.
  intro l.
  unfold fix_context_alt. unfold nlctx.
  rewrite map_rev. f_equal.
  rewrite map_mapi. rewrite mapi_map.
  eapply mapi_ext.
  intros n [na t]. simpl.
  unfold map_decl_anon. unfold vass.
  simpl.
  rewrite nl_lift. reflexivity.
Qed.

Lemma map_def_sig_nl :
  forall m,
    map (fun d : aname × term => (anonymize d.1, nl d.2)) (map def_sig m) =
    map def_sig (map (map_def_anon nl nl) m).
Proof.
  intro m.
  rewrite 2!map_map. eapply map_ext.
  intros [na ty bo ra]. simpl.
  unfold def_sig, map_def_anon. simpl.
  reflexivity.
Qed.

(*
Lemma nlctx_stack_context :
  forall ρ,
    nlctx (stack_context ρ) = stack_context (nlstack ρ).
Proof.
  intro ρ. induction ρ.
  all: try (simpl ; rewrite ?IHρ ; reflexivity).
  - simpl. rewrite nlctx_app_context. rewrite IHρ.
    rewrite nlctx_fix_context_alt.
    rewrite map_app. simpl.
    rewrite 2!map_def_sig_nl.
    reflexivity.
  - simpl. rewrite nlctx_app_context. rewrite IHρ.
    rewrite nlctx_fix_context_alt.
    rewrite map_app. simpl.
    rewrite 2!map_def_sig_nl.
    reflexivity.
  - simpl. rewrite nlctx_app_context. now rewrite IHρ.
  - simpl. rewrite nlctx_app_context. now rewrite IHρ.
Qed.
*)

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
  - f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - f_equal; auto.
    * unfold nl_predicate, map_predicate_k; simpl; f_equal;
      rewrite ?map_map_compose ?map_length; solve_all.
      eapply All_mapi_spec; eauto.
      rewrite /ondecl /map_decl_anon /map_decl /=. intuition auto.
      rewrite !option_map_two; f_equal; solve_all.
      destruct (decl_body x) => /= //. f_equal; eauto.
    * induction X0. 1: reflexivity.
      simpl. f_equal. 2: assumption.
      unfold nl_branch, map_branch_k. cbn.
      rewrite map_length. f_equal; solve_all.
      eapply All_mapi_spec; eauto.
      rewrite /ondecl /map_decl_anon /map_decl /=. intuition auto.
      rewrite !option_map_two; f_equal; solve_all.
      destruct (decl_body x0) => /= //. f_equal; eauto.
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
  forall le Σ φ d d',
    eq_decl le Σ φ d d' ->
    eq_decl le (nl_global_env Σ) φ (map_decl nl d) (map_decl nl d').
Proof.
  intros le Σ φ d d' []; constructor; destruct le; 
  intuition auto using nl_eq_term, nl_leq_term.
Qed.

Lemma nl_eq_decl' {cf:checker_flags} :
  forall le Σ φ d d',
    eq_decl le Σ φ d d' ->
    eq_decl le (nl_global_env Σ) φ (map_decl_anon nl d) (map_decl_anon nl d').
Proof.
  intros le Σ φ d d' []; constructor; destruct le;
  intuition auto using nl_eq_term, nl_leq_term.
Qed.

Lemma nl_eq_context {cf:checker_flags} :
  forall le Σ φ Γ Γ',
    eq_context le Σ φ Γ Γ' ->
    eq_context le (nl_global_env Σ) φ (nlctx Γ) (nlctx Γ').
Proof.
  intros le Σ φ Γ Γ' h.
  unfold eq_context, nlctx.
  destruct le; now eapply eq_context_nl.
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

Lemma nl_pred_set_pcontext p pcontext : 
  nl_predicate nl (set_pcontext p pcontext) = 
  set_pcontext (nl_predicate nl p) (nlctx pcontext).
Proof. reflexivity. Qed.

Lemma nl_pred_set_preturn p pret : nl_predicate nl (set_preturn p pret) = 
  set_preturn (nl_predicate nl p) (nl pret).
Proof. reflexivity. Qed.

Lemma nl_pred_set_pparams p pret : nl_predicate nl (set_pparams p pret) = 
  set_pparams (nl_predicate nl p) (map nl pret).
Proof. reflexivity. Qed.

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

From MetaCoq.PCUIC Require Import PCUICCases.

Lemma nl_declared_inductive Σ ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  declared_inductive (nl_global_env Σ) ind
    (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl).
Proof.
  intros []. split.
  - unfold declared_minductive.
    rewrite nl_lookup_env H.
    simpl. reflexivity.
  - simpl. now rewrite nth_error_map H0.
Qed.

Lemma nl_declared_constructor Σ c mdecl idecl cdecl :
  declared_constructor Σ c mdecl idecl cdecl ->
  declared_constructor (nl_global_env Σ) c
    (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl)
    (nl_constructor_body cdecl).
Proof.
  intros []. split.
  - now eapply nl_declared_inductive.
  - simpl. now rewrite nth_error_map H0.
Qed.

Lemma nl_case_predicate_context ind mdecl idecl p :
  nlctx (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl) 
    (nl_predicate nl p).
Proof.
  unfold case_predicate_context, case_predicate_context_gen.
  simpl.
  + todo "ind_case_predicate_context".
Qed.

Lemma nlctx_subst_instance :
  forall u Γ,
    nlctx (subst_instance u Γ) = subst_instance u (nlctx Γ).
Proof.
  intros u Γ.
  rewrite /subst_instance /=.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?subst_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - f_equal; auto.
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal;
    now rewrite nl_subst_instance.
  - f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal;
    now rewrite nl_subst_instance.
Qed.

Lemma nlctx_subst_context :
  forall s k Γ,
    nlctx (subst_context s k Γ) = subst_context (map nl s) k (nlctx Γ).
Proof.
  intros s k Γ.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?subst_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - simpl. f_equal; auto.
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    * now rewrite nl_subst; len.
    * now rewrite nl_subst; len. 
  - simpl. f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    now rewrite nl_subst; len.
Qed.


Lemma nlctx_lift_context :
  forall n k Γ,
    nlctx (lift_context n k Γ) = lift_context n k (nlctx Γ).
Proof.
  intros s k Γ.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?lift_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - simpl. f_equal; auto.
    rewrite /lift_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    * now rewrite nl_lift; len.
    * now rewrite nl_lift; len. 
  - simpl. f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    now rewrite nl_lift; len.
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
  unf_term. generalize (@nil term), 0.
  induction indctx.
  - reflexivity.
  - simpl. intros l n.
    destruct a as [? [?|] ?].
    all: cbn.
    all: apply IHindctx.
Qed.

Lemma nl_extended_subst Γ k :
  map nl (extended_subst Γ k) = extended_subst (nlctx Γ) k.
Proof.
  revert k; induction Γ as [|[? [] ?] ?]; intros k; simpl; f_equal; auto;
     rewrite ?nl_subst ?nl_lift ?nl_context_assumptions ?IHΓ; len => //.
Qed.

Hint Rewrite nl_context_assumptions : len.

Lemma nl_expand_lets_k Γ k t : 
  nl (expand_lets_k Γ k t) = 
  expand_lets_k (nlctx Γ) k (nl t).
Proof.
  rewrite /expand_lets_k.
  now rewrite nl_subst nl_extended_subst nl_lift; len.
Qed.

Lemma nl_expand_lets Γ t : 
  nl (expand_lets Γ t) = 
  expand_lets (nlctx Γ) (nl t).
Proof.
  now rewrite /expand_lets nl_expand_lets_k.
Qed.

Lemma subst_instance_nlctx u ctx :
  subst_instance u (nlctx ctx) = nlctx (subst_instance u ctx).
Proof.
  induction ctx; cbnr.
  f_equal. 2: apply IHctx.
  clear. destruct a as [? [] ?]; unfold map_decl, map_decl_anon; cbn; f_equal.
  all: now rewrite nl_subst_instance.
Qed.

Lemma map_anon_fold_context_k g g' ctx : 
  (forall i, nl ∘ g i =1 g' i ∘ nl) ->
  map (map_decl_anon nl) (fold_context_k g ctx) = 
  fold_context_k g' (map (map_decl_anon nl) ctx).
Proof.
  intros hg.
  rewrite !fold_context_k_alt map_mapi mapi_map. 
  apply mapi_ext => i d.
  rewrite /map_decl /map_decl_anon. len.
  f_equal.
  - destruct (decl_body d) => /= //.
    f_equal. apply hg.
  - apply hg.
Qed.

Lemma nl_subst_context s k ctx :
  nlctx (subst_context s k ctx) = 
  subst_context (map nl s) k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_context.
  apply map_anon_fold_context_k. 
  intros i x. now rewrite nl_subst.
Qed.

Lemma nl_subst_telescope s k ctx :
  nlctx (subst_telescope s k ctx) = 
  subst_telescope (map nl s) k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_telescope.
  rewrite map_mapi mapi_map. apply mapi_ext => i d.
  rewrite /map_decl_anon /map_decl; destruct d as [na [b|] ty]; cbn; f_equal;
    now rewrite nl_subst.
Qed.

Lemma nl_lift_context n k ctx :
  nlctx (lift_context n k ctx) = 
  lift_context n k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_context.
  apply map_anon_fold_context_k. 
  intros i x. now rewrite nl_lift.
Qed.

Lemma nl_expand_lets_ctx Γ Δ : 
  nlctx (expand_lets_ctx Γ Δ) = 
  expand_lets_ctx (nlctx Γ) (nlctx Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  now rewrite nl_subst_context nl_extended_subst nl_lift_context; len.
Qed.

Lemma nl_inds ind puinst bodies :
 map nl (inds ind puinst bodies) =
  inds ind puinst (map nl_one_inductive_body bodies).
Proof.
  rewrite /inds; len.
  induction #|bodies|; simpl; f_equal; auto.
Qed.


Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' : 
  map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma map2_map {A A' B B' C} (f : A -> B) (f' : A' -> B') (g : B -> B' -> C) l l' : 
  map2 g (map f l) (map f' l') = map2 (fun x y => g (f x) (f' y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma nlctx_length Γ : #|nlctx Γ| = #|Γ|.
Proof. now rewrite map_length. Qed.
Hint Rewrite nlctx_length : len.

Lemma nl_case_branch_context ind mdecl p br cdecl :
  nlctx (case_branch_context ind mdecl p br cdecl) =
  case_branch_context ind (nl_mutual_inductive_body mdecl)
    (nl_predicate nl p) (map anonymize br) 
    (nl_constructor_body cdecl).
Proof.
  unfold case_branch_context, case_branch_context_gen. simpl.
  rewrite nlctx_subst_context map_rev. f_equal.
  rewrite nl_expand_lets_ctx nlctx_subst_instance.
  f_equal.
  rewrite nl_subst_context nl_inds nlctx_subst_instance; len.
  f_equal. f_equal.
  now rewrite /nlctx map_map2 map2_map. 
Qed.

Lemma nl_case_branch_type ci mdecl idecl p br i cdecl : 
  let ptm :=
    it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p)
      (preturn p) in
  case_branch_type ci (nl_mutual_inductive_body mdecl)
    (nl_one_inductive_body idecl) (nl_predicate nl p) 
    (nl_branch nl br)
    (nl ptm) i (nl_constructor_body cdecl) = 
  map_pair nlctx nl (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros ptm.
  unfold case_branch_type, case_branch_type_gen.
  simpl. unfold map_pair. simpl. f_equal.
  - rewrite nl_case_branch_context.
    now rewrite /forget_types !map_map_compose.
  - rewrite nl_mkApps nl_lift; len. f_equal.
    rewrite !map_map_compose map_app /= !map_map_compose nl_mkApps.
    f_equal.
    * apply map_ext => idx. rewrite nl_subst nl_expand_lets_k map_rev.
      now rewrite nlctx_subst_instance nl_subst nl_inds nl_subst_instance.
    * f_equal.
      simpl. f_equal.
      rewrite map_app !map_map_compose.
      setoid_rewrite nl_lift.
      now rewrite nl_to_extended_list.
Qed.

Lemma nl_forget_types ctx : 
  forget_types (map (map_decl_anon nl) ctx) = 
  map anonymize (forget_types ctx).
Proof.
  now rewrite /forget_types !map_map_compose.
Qed.

Lemma nl_wf_predicate mdecl idecl p : 
  wf_predicate mdecl idecl p ->
  wf_predicate (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl) (nl_predicate nl p).
Proof.
  intros []; split. 
  { len => //. }
  depelim H0.
  simpl. rewrite nl_forget_types H2 /=. constructor; auto.
  eapply Forall2_map. solve_all.
Qed.

Lemma nl_wf_branch cdecl br :
  wf_branch cdecl br ->
  wf_branch (nl_constructor_body cdecl) (nl_branch nl br).  
Proof.
  unfold wf_branch, wf_branch_gen.
  simpl.
  rewrite nl_forget_types /=.
  intros H; apply Forall2_map; solve_all.
Qed.

Lemma nl_wf_branches idecl brs :
  wf_branches idecl brs ->
  wf_branches (nl_one_inductive_body idecl) (map (nl_branch nl) brs).  
Proof.
  unfold wf_branches, wf_branches_gen.
  simpl. intros H; apply Forall2_map.
  eapply (Forall2_impl H).
  apply nl_wf_branch.
Qed.

Lemma nl_red1 :
  forall Σ Γ M N,
    red1 Σ Γ M N ->
    red1 (nl_global_env Σ) (nlctx Γ) (nl M) (nl N).
Proof.
  intros Σ Γ M N h.
  induction h using red1_ind_all.
  all: simpl.
  all: rewrite ?nl_lift ?nl_subst ?nl_subst_instance.
  all: try solve [ econstructor ; eauto ].
  - constructor. unfold nlctx. rewrite nth_error_map.
    destruct (nth_error Γ i). 2: discriminate.
    cbn in *. apply some_inj in H. rewrite H. reflexivity.
  - rewrite nl_mkApps. cbn.
    rewrite map_rev map_skipn nl_extended_subst nl_lift.
    rewrite -(nl_context_assumptions (bcontext br)).
    change (nl (bbody br)) with (bbody (nl_branch nl br)).
    rewrite -(nlctx_length (bcontext br)).
    change (subst0 (extended_subst (nlctx br.(bcontext)) 0)
    (lift (context_assumptions (nlctx br.(bcontext))) #|
       nlctx br.(bcontext)| (bbody (nl_branch nl br)))) with
     (expand_lets (nlctx br.(bcontext)) (bbody (nl_branch nl br))).
    epose proof (nth_error_map (nl_branch nl) c brs).
    change (nlctx (bcontext br)) with (bcontext (nl_branch nl br)).
    eapply red_iota => //.
    * rewrite H1 H //.
    * now rewrite !List.skipn_length in H0 |- *; len.
  - rewrite !nl_mkApps. cbn. eapply red_fix with (narg:=narg).
    + unfold unfold_fix in *. rewrite nth_error_map.
      destruct (nth_error mfix idx). 2: discriminate.
      cbn.
      replace (isLambda (nl (dbody d))) with (isLambda (dbody d))
        by (destruct (dbody d) ; reflexivity).
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
      rewrite nl_lookup_env H. reflexivity.
    + destruct decl as [? [?|] ?].
      all: cbn in *.
      * f_equal. f_equal. congruence.
      * discriminate.
  - rewrite nl_mkApps. cbn. constructor.
    rewrite nth_error_map H. reflexivity.
  - rewrite nl_pred_set_pparams.
    econstructor; tea.
    eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    solve_all.
  - rewrite nl_pred_set_pcontext. econstructor.
    simpl. eapply OnOne2_local_env_map, OnOne2_local_env_impl; tea.
    unfold on_Trel; intros ? ?; intuition eauto.
    eapply on_one_decl_map_na.
    eapply on_one_decl_impl; tea.
    intros Γ' x' y'. now rewrite nlctx_app_context.
  - rewrite nl_pred_set_preturn. econstructor.
    rewrite -nlctx_app_context. apply IHh.
  - econstructor; tea.
    simpl.
    eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?]|]; cbn; solve_all.
    * red; simpl; left. solve_all.
      rewrite e. now rewrite -nlctx_app_context.
    * right. simpl. rewrite -b; intuition auto.
      eapply OnOne2_local_env_map, OnOne2_local_env_impl; tea.
      unfold on_Trel; intros ? ?; intuition eauto.
      eapply on_one_decl_map_na.
      eapply on_one_decl_impl; tea.
      intros Γ' x' y'. now rewrite nlctx_app_context.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [? ?]; auto.
  - constructor. apply OnOne2_map. eapply OnOne2_impl; [eassumption|].
    cbn. intros x y [? ?]; auto. red; simpl; intuition auto. congruence.
  - apply fix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context nl_fix_context in r0. assumption.
    + cbn. congruence.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split. 1: assumption.
    cbn. congruence.
  - apply cofix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context nl_fix_context in r0. assumption.
    + cbn. congruence.
Qed.

Lemma nl_conv {cf:checker_flags} :
  forall Σ Γ A B,
    Σ ;;; Γ |- A = B ->
    nlg Σ ;;; nlctx Γ |- nl A = nl B.
Proof.
  intros Σ Γ A B h.
  induction h.
  - constructor. rewrite global_ext_constraints_nlg.
    unfold nlg. destruct Σ. apply nl_eq_term.
    assumption.
  - eapply conv_red_l. 2: eassumption.
    destruct Σ. apply nl_red1. assumption.
  - eapply conv_red_r. 1: eassumption.
    destruct Σ. apply nl_red1. assumption.
Qed.

Lemma nl_cumul {cf:checker_flags} :
  forall Σ Γ A B,
    Σ ;;; Γ |- A <= B ->
    nlg Σ ;;; nlctx Γ |- nl A <= nl B.
Proof.
  intros Σ Γ A B h.
  induction h.
  - constructor. rewrite global_ext_constraints_nlg.
    unfold nlg. destruct Σ. apply nl_leq_term.
    assumption.
  - eapply cumul_red_l. 2: eassumption.
    destruct Σ. apply nl_red1. assumption.
  - eapply cumul_red_r. 1: eassumption.
    destruct Σ. apply nl_red1. assumption.
Qed.

Notation nldecl := (map_decl_anon nl).

Lemma nl_conv_decls {cf} {Σ Γ Γ'} {d d'} :
  conv_decls Σ Γ Γ' d d' ->
  conv_decls (nlg Σ) (nlctx Γ) (nlctx Γ') (nldecl d) (nldecl d').
Proof.
  intros Hd; depelim Hd; constructor; tas;
    eapply nl_conv; tea.
Qed.

Lemma nl_cumul_decls {cf} {Σ Γ Γ' d d'} :
   cumul_decls Σ Γ Γ' d d' ->
   cumul_decls (nlg Σ) (nlctx Γ) (nlctx Γ') (nldecl d) (nldecl d').
Proof.
  intros Hd; depelim Hd; constructor; tas;
    (eapply nl_conv || eapply nl_cumul); tea.
Qed.

Lemma nl_conv_ctx {cf} {Σ Γ Δ} :
  conv_context Σ Γ Δ ->
  conv_context (nlg Σ) (nlctx Γ) (nlctx Δ).
Proof.
  intros.
  induction X; simpl; constructor; eauto; simpl; now eapply nl_conv_decls in p.
Qed.
Hint Resolve @nl_conv_ctx : nl.

Lemma nl_cumul_ctx {cf} {Σ Γ Δ} :
  cumul_context Σ Γ Δ ->
  cumul_context (nlg Σ) (nlctx Γ) (nlctx Δ).
Proof.
  intros.
  induction X; simpl; constructor; eauto; simpl; now 
    (eapply nl_conv_decls in p || eapply nl_cumul_decls in p).
Qed.
Hint Resolve @nl_cumul_ctx : nl.

(*
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
*)

Lemma nl_check_one_fix d : check_one_fix d = check_one_fix (map_def_anon nl nl d).
Proof.
  destruct d; simpl.
  rewrite (nl_decompose_prod_assum [] dtype).
  destruct decompose_prod_assum.
Admitted.

Lemma nl_wf_fixpoint Σ mfix :
  wf_fixpoint Σ.1 mfix = wf_fixpoint (nlg Σ).1 (map (map_def_anon nl nl) mfix).
Proof.
  unfold wf_fixpoint.
  destruct (map check_one_fix mfix) eqn:hmap.
Admitted.

Lemma nl_wf_cofixpoint Σ mfix :
  wf_cofixpoint Σ.1 mfix = wf_cofixpoint (nlg Σ).1 (map (map_def_anon nl nl) mfix).
Proof.
  unfold wf_fixpoint.
Admitted.

Lemma nl_monomorphic_levels_decl g : monomorphic_levels_decl (nl_global_decl g) = monomorphic_levels_decl g.
Proof.
  destruct g; simpl.
  - destruct c; cbn. reflexivity.
  - destruct m; reflexivity.
Qed.

Lemma nl_global_levels Σ : global_levels (nl_global_env Σ) = global_levels Σ.
Proof.
  induction Σ; simpl; auto.
  destruct a; simpl. now rewrite IHΣ nl_monomorphic_levels_decl.
Qed.

Lemma nl_global_ext_levels Σ :
  LevelSet.Equal (global_ext_levels (nlg Σ)) (global_ext_levels Σ).
Proof.
  destruct Σ as [Σ univ].
  unfold global_ext_levels; simpl.
  intros x. now rewrite !LevelSet.union_spec nl_global_levels.
Qed.

Lemma wf_universe_nl Σ u : wf_universe Σ u -> wf_universe (nlg Σ) u.
Proof.
  destruct u; simpl; auto.
  intros.
  now rewrite nl_global_ext_levels.
Qed.

Lemma All2i_map {A B C D} (f : A -> B) (g : C -> D) P n l l' : 
  All2i (fun i x y => P i (f x) (g y)) n l l' <~>
  All2i P n (map f l) (map g l').
Proof.
  split.
  - induction 1; constructor; auto.
  - induction l in n, l' |- *; destruct l'; intros H; depelim H; constructor; auto.
Qed.

Lemma nl_is_allowed_elimination {cf:checker_flags} (Σ : global_env_ext) ps kelim :
  is_allowed_elimination Σ ps kelim ->
  is_allowed_elimination (nlg Σ) ps kelim.
Proof.
  now rewrite global_ext_constraints_nlg.
Qed.

Axiom nl_fix_guard : forall Σ Γ mfix,
  fix_guard Σ Γ mfix -> fix_guard (nlg Σ) (nlctx Γ) (map (map_def_anon nl nl) mfix).
Axiom nl_cofix_guard : forall Σ Γ mfix,
  cofix_guard Σ Γ mfix -> cofix_guard (nlg Σ) (nlctx Γ) (map (map_def_anon nl nl) mfix).

Lemma typing_nlg {cf : checker_flags} :
  env_prop (fun Σ Γ t T => nlg Σ ;;; nlctx Γ |- nl t : nl T)
    (fun Σ Γ => wf_local (nlg Σ) (nlctx Γ)).
Proof.
  clear.
  apply typing_ind_env; intros; cbn in *;
    rewrite ?nl_lift ?nl_subst ?nl_subst_instance;
    try (econstructor; eauto using nlg_wf_local; fail).
  - induction X; simpl; constructor; auto.
    * now exists (tu.π1).
    * now exists (tu.π1).

  - replace (nl (decl_type decl)) with (decl_type (map_decl_anon nl decl));
      [|destruct decl; reflexivity].
    constructor. 1: eauto using nlg_wf_local.
    unfold nlctx. rewrite nth_error_map. now rewrite H.
  - constructor; eauto using nlg_wf_local.
    now apply wf_universe_nl.
  - replace (nl (cst_type decl)) with (cst_type (map_constant_body nl decl));
      [|destruct decl; reflexivity].
    constructor; eauto using nlg_wf_local.
    + unfold declared_constant in *. now erewrite lookup_env_nlg; tea.
    + red. rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - replace (nl (ind_type idecl)) with (ind_type (nl_one_inductive_body idecl));
      [|destruct idecl; reflexivity].
    destruct isdecl as [H1 H2].
    econstructor; eauto using nlg_wf_local. 1: split.
    + eapply lookup_env_nlg in H1. eapply H1.
    + replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
          (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
      rewrite nth_error_map H2. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - cbn.
    rewrite nl_inds.
    eapply type_Construct with (idecl0:=nl_one_inductive_body idecl)
                               (mdecl0:=nl_mutual_inductive_body mdecl)
                               (cdecl0:=nl_constructor_body cdecl);
    eauto using nlg_wf_local.
    + destruct isdecl as [[H1 H2] H3]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map H2. reflexivity.
      * rewrite nth_error_map H3. reflexivity.
    + unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
  - rewrite nl_mkApps map_app nl_it_mkLambda_or_LetIn. cbn.
    rewrite nl_case_predicate_context.
    eapply type_Case with  (mdecl0:=nl_mutual_inductive_body mdecl)
                           (idecl0:=nl_one_inductive_body idecl)
                           (p0:=nl_predicate nl p); tea.
    + destruct isdecl as [HH1 HH2]. split.
      * eapply lookup_env_nlg in HH1. eapply HH1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map HH2. reflexivity.
    + destruct H0 as [wfpars wfpctx].
      split; simpl; rewrite ?map_length //.
      clear -wfpctx. depelim wfpctx.
      rewrite nl_forget_types H0 /=.
      simpl. constructor => //.
      eapply Forall2_map; solve_all.
    + simpl. tas.
      unfold consistent_instance_ext.
      rewrite global_ext_levels_nlg global_ext_constraints_nlg; assumption.
    + now rewrite -nlctx_app_context.
    + simpl.
      rewrite -nl_case_predicate_context.
      rewrite - !nlctx_app_context.
      eapply nl_conv_ctx; tea.
    + now rewrite -nl_case_predicate_context - !nlctx_app_context.
    + now apply nl_is_allowed_elimination.
    + revert X6. simpl.
      rewrite -map_app -nlctx_app_context.
      rewrite -nlctx_subst_instance.
      rewrite -[List.rev (nlctx _)]map_rev.
      clear. induction 1; simpl; constructor; eauto.
      * now rewrite -(nl_subst_telescope [i] 0 Δ).
      * now rewrite -(nl_subst_telescope [b] 0 Δ).
    + now rewrite nl_mkApps map_app in X8.
    + now eapply nl_wf_branches.
    + eapply All2i_map, (All2i_impl X9).
      intros i cdecl br.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _) in *.
      intros ((wfctx & convctx) & (bbodyty & wfbctx) & IHbody & bty & IHbty).
      rewrite -nl_case_predicate_context.
      simpl preturn. rewrite -nl_it_mkLambda_or_LetIn.
      rewrite nl_case_branch_type.
      rewrite -/cbt. unfold map_pair. cbn.
      repeat split.
      * now rewrite -[_ ++ _]nlctx_app_context.
      * rewrite - ![_ ++ _]nlctx_app_context.
        now eapply nl_conv_ctx.
      * now rewrite nlctx_app_context in IHbody.
      * now rewrite nlctx_app_context in IHbty.
  - destruct pdecl as [pdecl1 pdecl2]; simpl.
    rewrite map_rev.
    eapply type_Proj with (mdecl0:=nl_mutual_inductive_body mdecl)
                          (idecl0:=nl_one_inductive_body idecl)
                          (pdecl:=(pdecl1, nl pdecl2)).
    + destruct isdecl as [[H1 H2] [H3 H4]]. repeat split.
      * eapply lookup_env_nlg in H1. eapply H1.
      * replace (ind_bodies (nl_mutual_inductive_body mdecl)) with
            (map nl_one_inductive_body (ind_bodies mdecl)); [|now destruct mdecl].
        rewrite nth_error_map H2. reflexivity.
      * rewrite nth_error_map H3. reflexivity.
      * assumption.
    + now rewrite nl_mkApps in X2.
    + now rewrite map_length.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor.
    + now eapply nl_fix_guard.
    + now rewrite nth_error_map H0.
    + rewrite nlctx_app_context in X. now eapply wf_local_app_inv in X.
    + clear -X0.
      apply All_map. eapply All_impl; tea.
      simpl. intros x [s Hs]. now exists s.
    + apply All_map. eapply All_impl; tea.
      simpl. intros [] [s Hs].
      simpl in *; intuition auto.
      * rewrite fix_context_length map_length.
        rewrite fix_context_length in Hs.
        now rewrite -> XX, <- nl_lift.
    + now rewrite <-nl_wf_fixpoint.
  - replace (nl (dtype decl)) with (dtype (map_def_anon nl nl decl));
      [|destruct decl; reflexivity].
    assert (XX: nlctx Γ ,,, fix_context (map (map_def_anon nl nl) mfix)
                = nlctx (Γ ,,, fix_context mfix))
      by now rewrite <- nl_fix_context, <- nlctx_app_context.
    constructor; auto.
    + now apply nl_cofix_guard.
    + now rewrite nth_error_map H0.
    + now rewrite nlctx_app_context in X; apply wf_local_app_inv in X.
    + clear -X0.
      apply All_map. eapply All_impl; tea.
      simpl. intros x [s Hs]. now exists s.
    + apply All_map. eapply All_impl; tea.
      simpl. intros [] [s Hs].
      simpl in *; intuition auto.
      * rewrite fix_context_length map_length.
        rewrite fix_context_length in Hs.
        now rewrite -> XX, <- nl_lift.
    + now rewrite <-nl_wf_cofixpoint.
  - econstructor; tea.
    now apply nl_cumul.
Qed.

(* Corollary reflect_nleq_term : *)
(*   forall t t', *)
(*     reflect (nl t = nl t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. *)
(*   destruct (reflect_upto_names t t'). *)
(*   - constructor. eapply eq_term_nl_eq. assumption. *)
(*   - constructor. intro bot. apply f. *)
(*     apply eq_term_upto_univ_nl_inv. *)
(*     rewrite bot. *)
(*     apply eq_term_upto_univ_refl. *)
(*     all: auto. *)
(* Qed. *)

(* Lemma nleq_term_it_mkLambda_or_LetIn : *)
(*   forall Γ u v, *)
(*     nleq_term u v -> *)
(*     nleq_term (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v). *)
(* Proof. *)
(*   intros Γ u v h. *)
(*   induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *. *)
(*   - assumption. *)
(*   - simpl. cbn. apply ih. *)
(*     eapply ssrbool.introT. *)
(*     + eapply reflect_nleq_term. *)
(*     + cbn. f_equal. *)
(*       eapply ssrbool.elimT. *)
(*       * eapply reflect_nleq_term. *)
(*       * assumption. *)
(*   - simpl. cbn. apply ih. *)
(*     eapply ssrbool.introT. *)
(*     + eapply reflect_nleq_term. *)
(*     + cbn. f_equal. *)
(*       eapply ssrbool.elimT. *)
(*       * eapply reflect_nleq_term. *)
(*       * assumption. *)
(* Qed. *)

Lemma anonymize_two na : anonymize (anonymize na) = anonymize na.
Proof.
  destruct na; simpl; reflexivity.
Qed.

Lemma nl_two M :
  nl (nl M) = nl M.
Proof.
  induction M using term_forall_list_ind; cbnr.
  all: rewrite ?IHM1 ?IHM2 ?IHM3 ?IHM; cbnr.
  - f_equal. induction X; cbnr. congruence.
  - destruct X; cbnr.
    f_equal; solve_all.
    * unfold nl_predicate; cbn; f_equal; solve_all.
      unfold ondecl in *; solve_all.
      unfold nldecl; destruct x as [na [bod|] ty]; simpl in *; f_equal; auto.
      f_equal; eauto.
    * unfold nl_branch; destruct x; cbn. f_equal; auto.
      unfold ondecl in *; solve_all.
      unfold nldecl; destruct x as [na [bod|] ty]; simpl; f_equal; auto.
      f_equal; eauto.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *.
    rewrite anonymize_two; congruence.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *. 
    rewrite anonymize_two; congruence.
Qed.


Local Ltac aa :=
  match goal with
  | |- ∑ _ : _, _ × ?t = _ => exists t
  end; split; [|symmetry; apply nl_two]; simpl;
  rewrite ?nl_lift ?nl_subst ?nl_subst_instance.

Local Ltac bb :=
  repeat match goal with
  | H : ∑ _ : _, _ × ?t = _ |- _ => destruct H as [? [? ?]]
  end;
  eexists; split.

Local Ltac bb' := bb; [econstructor|]; tea; cbn.

Arguments on_snd {_ _ _} _ _/.
Arguments map_def_anon {_ _} _ _ _/.

(*
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
    × OnOne2 (on_Trel_eq (red1 Σ (nlctx Γ)) snd fst) (map (on_snd nl) brs) brs'').
    {
      induction X.
      + destruct p0 as [[? [hd'' [? ?]]] ?].
        eexists ((hd'.1, hd'') :: map (on_snd nl) tl); cbn; split.
        1: congruence.
        constructor; cbn. split; tas.
      + destruct IHX as [brs'' [? ?]]. exists ((hd.1, nl hd.2) :: brs''); cbn; split.
        * rewrite nl_two. congruence.
        * now constructor.
    }
    destruct Y as [brs'' [? ?]].
    exists (tCase ind (nl p) (nl c) brs''); cbn; split; [|rewrite !nl_two; congruence].
    now constructor.
  - assert (Y : ∑ l'', map nl l' = map nl l''
                           × OnOne2 (red1 Σ (nlctx Γ)) (map nl l) l'').
    {
      induction X.
      + destruct p as [? [hd'' [? ?]]].
        eexists (hd'' :: map nl tl); cbn; split.
        * f_equal; tas.
          rewrite map_map; apply map_ext; intro; now rewrite nl_two.
        * now constructor.
      + destruct IHX as [l'' [? ?]]. exists (nl hd :: l''); cbn; split.
        * rewrite nl_two. congruence.
        * now constructor.
    }
    destruct Y as [l'' [? ?]].
    exists (tEvar ev l''); cbn; split. 1: now constructor. congruence.
  - assert (Y : ∑ mfix'', map (map_def_anon nl nl) mfix1
                          = map (map_def_anon nl nl) mfix''
    × OnOne2 (fun x y => red1 Σ (nlctx Γ) (dtype x) (dtype y)
     × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y))
    (map (map_def_anon nl nl) mfix0) mfix'').
    {
      induction X.
      + destruct p as [[? [typ'' [? ?]]] ?]. cbn.
        eexists ({|dname:=nAnon; dtype:=typ''; dbody:=nl (dbody hd');
                   rarg:=rarg hd' |}
                   :: map (map_def_anon nl nl) tl); cbn; split.
        * f_equal; simpl.
          -- rewrite nl_two. congruence.
          -- rewrite map_map; apply map_ext; intros []; simpl; now rewrite !nl_two.
        * constructor. cbn. split; auto. congruence.
      + destruct IHX as [mfix'' [? ?]].
        exists (map_def_anon nl nl hd :: mfix''); cbn; split.
        * rewrite !nl_two. congruence.
        * now constructor.
    }
    destruct Y as [mfix'' [? ?]].
    exists (tFix mfix'' idx); cbn; split. 1: now constructor. congruence.
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
*)

  (* Lemma nleq_term_zipc : *)
  (*   forall u v π, *)
  (*     nleq_term u v -> *)
  (*     nleq_term (zipc u π) (zipc v π). *)
  (* Proof. *)
  (*   intros u v π h. *)
  (*   eapply ssrbool.introT. *)
  (*   - eapply reflect_nleq_term. *)
  (*   - cbn. rewrite 2!nl_zipc. f_equal. *)
  (*     eapply ssrbool.elimT. *)
  (*     + eapply reflect_nleq_term. *)
  (*     + assumption. *)
  (* Qed. *)

  (* Lemma nleq_term_zipx : *)
  (*   forall Γ u v π, *)
  (*     nleq_term u v -> *)
  (*     nleq_term (zipx Γ u π) (zipx Γ v π). *)
  (* Proof. *)
  (*   intros Γ u v π h. *)
  (*   unfold zipx. *)
  (*   eapply nleq_term_it_mkLambda_or_LetIn. *)
  (*   eapply nleq_term_zipc. *)
  (*   assumption. *)
  (* Qed. *)

  (* Corollary type_nameless : *)
  (*   forall Σ Γ u A, *)
  (*     wf Σ.1 -> *)
  (*     Σ ;;; Γ |- u : A -> *)
  (*     Σ ;;; Γ |- nl u : A. *)
  (* Proof. *)
  (*   intros Σ Γ u A hΣ h. *)
  (*   eapply typing_alpha ; eauto. *)
  (*   eapply eq_term_upto_univ_tm_nl. all: auto. *)
  (* Qed. *)

  (* Lemma upto_names_nl t *)
  (*   : t ≡ nl t. *)
  (* Proof. *)
  (*   eapply eq_term_upto_univ_tm_nl; exact _. *)
  (* Qed. *)

  (* Lemma upto_names_nlctx Γ *)
  (*   : Γ ≡Γ nlctx Γ. *)
  (* Proof. *)
  (*   induction Γ as [|a Γ]; try constructor. *)
  (*   destruct a as [na [bo|] ty]; simpl; constructor; cbn; tas. *)
  (*   all: apply upto_names_nl. *)
  (* Qed. *)

  (* Lemma wellformed_nlctx Γ u : *)
  (*     wellformed Σ Γ u -> *)
  (*     wellformed Σ (nlctx Γ) u. *)
  (* Proof. *)
  (*   destruct hΣ as [hΣ']. *)
  (*   assert (Γ ≡Γ nlctx Γ) by apply upto_names_nlctx. *)
  (*   intros [[A hu]|[[ctx [s [X1 X2]]]]]; [left|right]. *)
  (*   - exists A. eapply context_conversion'. all: try eassumption. *)
  (*     1:{ eapply wf_local_alpha with Γ. all: try eassumption. *)
  (*         eapply typing_wf_local. eassumption. *)
  (*     } *)
  (*     eapply upto_names_conv_context. assumption. *)
  (*   - constructor. exists ctx, s. split; tas. *)
  (*     eapply wf_local_alpha; tea. *)
  (*     now eapply eq_context_upto_cat. *)
  (* Qed. *)

  (* Lemma fresh_global_nl : *)
  (*   forall Σ k, *)
  (*     fresh_global k Σ -> *)
  (*     fresh_global k (nl_global_env Σ). *)
  (* Proof. *)
  (*   intros Σ k h. eapply Forall_map. *)
  (*   eapply Forall_impl ; try eassumption. *)
  (*   intros x hh. cbn in hh. *)
  (*   destruct x ; assumption. *)
  (* Qed. *)
