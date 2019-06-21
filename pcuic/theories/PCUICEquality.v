(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template Require Import config utils Universes BasicAst AstUtils
     UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNameless
     PCUICCumulativity PCUICPosition.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

Fixpoint eqb_term_upto_univ (equ lequ : universe -> universe -> bool) (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ equ equ) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    lequ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ equ lequ u u' &&
    eqb_term_upto_univ equ equ v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 lequ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    forallb2 lequ (map Universe.make u) (map Universe.make u')

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    forallb2 lequ (map Universe.make u) (map Universe.make u')

  | tLambda na A t, tLambda na' A' t' =>
    eqb_term_upto_univ equ equ A A' &&
    eqb_term_upto_univ equ lequ t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_term_upto_univ equ equ A A' &&
    eqb_term_upto_univ equ lequ B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_term_upto_univ equ equ B B' &&
    eqb_term_upto_univ equ equ b b' &&
    eqb_term_upto_univ equ lequ u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_term_upto_univ equ equ p p' &&
    eqb_term_upto_univ equ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      eqb_term_upto_univ equ equ (snd x) (snd y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ equ equ c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | _, _ => false
  end.

(* Definition eqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

(* Definition leqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

Inductive reflectT (A : Type) : bool -> Type :=
| ReflectT : A -> reflectT A true
| ReflectF : (A -> False) -> reflectT A false.

Lemma reflectT_reflect (A : Prop) b : reflectT A b -> reflect A b.
Proof.
  destruct 1; now constructor.
Qed.

Lemma reflect_reflectT (A : Prop) b : reflect A b -> reflectT A b.
Proof.
  destruct 1; now constructor.
Qed.

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_spec u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ h :=
  repeat lazymatch goal with
  | |- context [ equ ?x ?y ] =>
    destruct (h x y) ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall lequ Rle hle t', reflectT (eq_term_upto_univ _ _ ?t _) _,
    hle : forall u u', reflectT (?Rle u u') (?lequ u u')
    |- context [ eqb_term_upto_univ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle hle t') ; nodec ; subst
  end.

Lemma reflect_eq_term_upto_univ :
  forall equ lequ Re Rle,
    (forall u u', reflectT (Re u u') (equ u u')) ->
    (forall u u', reflectT (Rle u u') (lequ u u')) ->
    forall t t',
      reflectT (eq_term_upto_univ Re Rle t t')
              (eqb_term_upto_univ equ lequ t t').
Proof.
  intros equ lequ Re Rle he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  (* all: try solve [ *)
  (*   cbn - [eqb] ; eqspecs ; equspec equ h ; ih ; *)
  (*   constructor ; constructor ; assumption *)
  (* ]. *)
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn.
    induction X in l0 |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst.
        inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst.
        inversion X0.
      * cbn. destruct (p _ _ he t).
        -- destruct (IHX l0).
           ++ constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb].
    pose proof (eqb_spec s k) as H.
    match goal with
    | |- context G[ eqb ?x ?y ] =>
      set (toto := eqb x y) in * ;
      let G' := context G[toto] in
      change G'
    end.
    destruct H ; nodec. subst.
    equspec equ he. equspec lequ hle. ih.
    cbn. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion X.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion X.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion X.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion X.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion X.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion X.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb].
    destruct indn as [i n].
    induction l in brs, X |- *.
    + destruct brs.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion X2.
    + destruct brs.
      * constructor. intro bot. inversion bot. subst. inversion X2.
      * cbn - [eqb]. inversion X. subst.
        destruct a, p. cbn - [eqb]. eqspecs.
        -- cbn - [eqb]. pose proof (X0 equ Re he t0) as hh. cbn in hh.
           destruct hh.
           ++ cbn - [eqb].
              destruct (IHl X1 brs).
              ** constructor. constructor ; try assumption.
                 constructor ; try easy.
                 inversion e2. subst. assumption.
              ** constructor. intro bot. apply f. inversion bot. subst.
                 constructor ; try assumption.
                 inversion X4. subst. assumption.
           ++ constructor. intro bot. apply f. inversion bot. subst.
              inversion X4. subst. destruct X5. assumption.
        -- constructor. intro bot. inversion bot. subst.
           inversion X4. subst. destruct X5. cbn in e1. subst.
           apply n2. reflexivity.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
Qed.

(* Syntactical equality *)
Definition nleq_term t t' :=
  eqb_term_upto_univ eqb eqb t t'.

Corollary reflect_eq_term_upto_univ_eqb :
  forall t t',
    reflectT (eq_term_upto_univ eq eq t t') (nleq_term t t').
Proof.
  intros t t'. eapply reflect_eq_term_upto_univ.
  all: intros u u'; eapply reflect_reflectT, eqb_spec.
Qed.

Corollary reflect_nleq_term :
  forall `{checker_flags} t t',
    reflect (nl t = nl t') (nleq_term t t').
Proof.
  intros flags t t'.
  destruct (reflect_eq_term_upto_univ_eqb t t').
  - constructor. eapply eq_term_nl_eq. assumption.
  - constructor. intro bot. apply f.
    apply eq_term_upto_univ_nl_inv ; auto.
    rewrite bot.
    apply eq_term_upto_univ_refl ; auto.
Qed.

Local Ltac ih2 :=
  lazymatch goal with
  | ih : forall Rle v, _ -> _ -> eq_term_upto_univ _ _ ?u _
    |- eq_term_upto_univ _ _ ?u _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_eq_eq_term_upto_univ :
  forall Re Rle u v,
    Reflexive Re ->
    Reflexive Rle ->
    eq_term_upto_univ eq eq u v ->
    eq_term_upto_univ Re Rle u v.
Proof.
  intros Re Rle u v he hle h.
  induction u using term_forall_list_ind in v, h, Rle, hle |- *.
  all: dependent destruction h.
  all: try solve [ constructor ; try ih2 ; try assumption ;
                   try subst ; try reflexivity ].
  - constructor. solve_all.
  - constructor. eapply All2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor. eapply All2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor. eapply All2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor ; try ih2 ; try assumption. solve_all.
  - constructor ; try ih2 ; try assumption. solve_all.
  - constructor ; try ih2 ; try assumption. solve_all.
Qed.

Lemma eq_term_upto_univ_eq_eq_term :
  forall φ u v,
    eq_term_upto_univ eq eq u v ->
    eq_term φ u v.
Proof.
  intros φ u v h.
  eapply eq_term_upto_univ_eq_eq_term_upto_univ ; auto.
  all: intro x ; eapply eq_universe_refl.
Qed.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift :
  forall Re Rle u v n k,
    eq_term_upto_univ Re Rle u v ->
    eq_term_upto_univ Re Rle (lift n k u) (lift n k v).
Proof.
  intros Re Rle u v n k e.
  induction u in v, n, k, e, Rle |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try (cbn ; constructor ; try lih ; assumption).
  - cbn. destruct (Nat.leb_spec0 k n0).
    + constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn. constructor ; try lih ; try assumption. solve_all.
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
Qed.

Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_subst :
  forall (Re Rle : universe -> universe -> Type) u v n x y,
    (forall u u' : universe, Re u u' -> Rle u u') ->
    eq_term_upto_univ Re Rle u v ->
    eq_term_upto_univ Re Re x y ->
    eq_term_upto_univ Re Rle (u{n := x}) (v{n := y}).
Proof.
  intros Re Rle u v n x y hR e1 e2.
  induction u in v, n, x, y, e1, e2, Rle, hR |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + destruct (eqb_spec n0 n).
      * subst. replace (n - n) with 0 by omega. cbn.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq ; eauto.
      * replace (n0 - n) with (S (n0 - (S n))) by omega. cbn.
        rewrite nth_error_nil. constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn. constructor ; try sih ; eauto. solve_all.
  - cbn. constructor.
    pose proof (All2_length _ _ a). solve_all. rewrite H; eauto.
  - cbn. constructor.
    pose proof (All2_length _ _ a). solve_all. rewrite H; eauto.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv :
  forall Re Rle u l t,
    eq_term_upto_univ Re Rle (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ Re Rle u u' *
      All2 (eq_term_upto_univ Re Re) l l' *
      (t = mkApps u' l').
Proof.
  intros Re Rle u l t h.
  induction l in u, t, h, Rle |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps :
  forall Re Rle u1 l1 u2 l2,
    eq_term_upto_univ Re Rle u1 u2 ->
    All2 (eq_term_upto_univ Re Re) l1 l2 ->
    eq_term_upto_univ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros Re Rle u1 l1 u2 l2 hu hl.
  induction l1 in u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_subst_instance_constr :
  forall (Re Rle : universe -> universe -> Type) u b u' b',
    (forall s s',
        Re s s' ->
        Re (subst_instance_univ u s) (subst_instance_univ u' s')
    ) ->
    (forall s s',
        Rle s s' ->
        Rle (subst_instance_univ u s) (subst_instance_univ u' s')
    ) ->
    All2 Rle (map Universe.make u) (map Universe.make u') ->
    eq_term_upto_univ Re Rle b b' ->
    eq_term_upto_univ Re Rle (subst_instance_constr u b)
                      (subst_instance_constr u' b').
Proof.
  intros Re Rle u b u' b' hRe hRle hu hb.
  induction b in b', hb, Rle, hRle |- * using term_forall_list_ind.
  all: try solve [ dependent destruction hb ; constructor ; eauto ].
  - dependent destruction hb. cbn. constructor.
    solve_all.
  - dependent destruction hb. cbn. constructor.
    eapply All2_map_inv in a. eapply All2_map.
    eapply All2_map. solve_all. unfold Universe.make.
    unfold subst_instance_univ in *.
    specialize (hRle _ _ X). eapply hRle.
  - dependent destruction hb. cbn. constructor.
    eapply All2_map_inv in a. eapply All2_map.
    eapply All2_map. solve_all. unfold Universe.make.
    unfold subst_instance_univ in *.
    specialize (hRle _ _ X). eapply hRle.
  - dependent destruction hb. cbn. constructor.
    eapply All2_map_inv in a. eapply All2_map.
    eapply All2_map. solve_all. unfold Universe.make.
    unfold subst_instance_univ in *.
    specialize (hRle _ _ X). eapply hRle.
  - dependent destruction hb. cbn. constructor; solve_all.
  - dependent destruction hb. cbn.
    constructor; solve_all.
  - dependent destruction hb. cbn.
    constructor; solve_all.
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

Lemma eq_term_it_mkLambda_or_LetIn_inv :
  forall (Σ : global_context) Γ u v,
    eq_term (snd Σ) (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term (snd Σ) u v.
Proof.
  intros Σ Γ.
  induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma eq_term_zipc_inv :
  forall (Σ : global_context) u v π,
    eq_term (snd Σ) (zipc u π) (zipc v π) ->
    eq_term (snd Σ) u v.
Proof.
  intros Σ u v π h.
  revert u v h. induction π ; intros u v h.
  all: solve [
           simpl in h ; try apply IHπ in h ;
           cbn in h ; inversion h ; subst ; assumption
         ].
Qed.

Lemma eq_term_zipx_inv :
  forall (Σ : global_context) Γ u v π,
    eq_term (snd Σ) (zipx Γ u π) (zipx Γ v π) ->
    eq_term (snd Σ) u v.
Proof.
  intros Σ Γ u v π h.
  eapply eq_term_zipc_inv.
  eapply eq_term_it_mkLambda_or_LetIn_inv.
  eassumption.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn :
  forall (Σ : global_context) Γ u v,
    eq_term (snd Σ) u v ->
    eq_term (snd Σ) (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v).
Proof.
  intros Σ Γ.
  induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_refl. assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_refl. assumption.
Qed.

Lemma eq_term_zipc :
  forall (Σ : global_context) u v π,
    eq_term (snd Σ) u v ->
    eq_term (snd Σ) (zipc u π) (zipc v π).
Proof.
  intros Σ u v π h.
  revert u v h. induction π ; intros u v h.
  all: try solve [
             simpl ; try apply IHπ ;
             cbn ; constructor ; try apply eq_term_refl ; assumption
           ].
  - assumption.
  - simpl. apply IHπ. destruct indn as [i n].
    constructor.
    + apply eq_term_refl.
    + assumption.
    + eapply All2_same.
      intros. split ; auto. apply eq_term_refl.
Qed.

Lemma eq_term_zipx :
  forall (Σ : global_context) Γ u v π,
    eq_term (snd Σ) u v ->
    eq_term (snd Σ) (zipx Γ u π) (zipx Γ v π).
Proof.
  intros Σ Γ u v π h.
  eapply eq_term_it_mkLambda_or_LetIn.
  eapply eq_term_zipc.
  eassumption.
Qed.

Lemma eq_term_upto_univ_isApp :
  forall Re Rle u v,
    eq_term_upto_univ Re Rle u v ->
    isApp u = isApp v.
Proof.
  intros Re Rle u v h.
  induction h.
  all: reflexivity.
Qed.

Inductive eq_context_upto Re : context -> context -> Type :=
| eq_context_nil : eq_context_upto Re [] []
| eq_context_vass na A Γ nb B Δ :
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vass na A) (Δ ,, vass nb B)
| eq_context_vdef na u A Γ nb v B Δ :
    eq_term_upto_univ Re Re u v ->
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vdef na u A) (Δ ,, vdef nb v B).

Definition eq_def_upto Re d d' : Type :=
  (eq_term_upto_univ Re Re d.(dtype) d'.(dtype)) *
  (eq_term_upto_univ Re Re d.(dbody) d'.(dbody)) *
  (d.(rarg) = d'.(rarg)).

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Definition eq_decl_upto Re d d' : Type :=
  rel_option (eq_term_upto_univ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Re Re d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto :
  forall Re Γ Δ,
    All2 (eq_decl_upto Re) Γ Δ ->
    eq_context_upto Re Γ Δ.
Proof.
  intros Re Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [h1 h2].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h1.
    + constructor ; eauto.
    + constructor ; eauto.
Qed.

Lemma eq_context_upto_refl :
  forall Re Γ,
    Reflexive Re ->
    eq_context_upto Re Γ Γ.
Proof.
  intros Re Γ hRe.
  induction Γ as [| [na [bo |] ty] Γ ih].
  - constructor.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
Qed.

Lemma eq_context_upto_cat :
  forall Re Γ Δ Γ' Δ',
    eq_context_upto Re Γ Γ' ->
    eq_context_upto Re Δ Δ' ->
    eq_context_upto Re (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros Re Γ Δ Γ' Δ' h1 h2.
  induction h2 in Γ, Γ', h1 |- *.
  - assumption.
  - simpl. constructor ; eauto.
  - simpl. constructor ; eauto.
Qed.

Lemma eq_context_upto_rev :
  forall Re Γ Δ,
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (rev Γ) (rev Δ).
Proof.
  intros Re Γ Δ h.
  induction h.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Definition SubstUnivPreserving R :=
  forall u u' s s',
    R s s' ->
    R (subst_instance_univ u s) (subst_instance_univ u' s').

Lemma eq_term_upto_univ_substs :
  forall (Re Rle : universe -> universe -> Type) u v n l l',
    (forall u u' : universe, Re u u' -> Rle u u') ->
    eq_term_upto_univ Re Rle u v ->
    All2 (eq_term_upto_univ Re Re) l l' ->
    eq_term_upto_univ Re Rle (subst l n u) (subst l' n v).
Proof.
  intros Re Rle u v n l l' hR hu hl.
  induction u in v, n, l, l', hu, hl, Rle, hR |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq ; eauto.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn. constructor ; try sih ; eauto. solve_all.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. now rewrite H.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. now rewrite H.
Qed.

Derive Signature for All2.

Lemma All2_trans {A} (P : A -> A -> Type) :
  CRelationClasses.Transitive P ->
  CRelationClasses.Transitive (All2 P).
Proof.
  intros HP x y z H. induction H in z |- *.
  intros Hyz. depelim Hyz. constructor.
  intros Hyz. depelim Hyz. constructor; auto.
  now transitivity y.
Qed.

Lemma eq_term_upto_univ_trans :
  forall Re Rle,
    CRelationClasses.Transitive Re ->
    CRelationClasses.Transitive Rle ->
    CRelationClasses.Transitive (eq_term_upto_univ Re Rle).
Proof.
  intros Re Rle he hle u v w e1 e2.
  induction u in Rle, hle, v, w, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try eapply All2_trans ; eauto
  ].
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, args'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 h2]. eauto.
  - dependent destruction e2.
    econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, brs'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 [h2 h3]]. eauto.
      destruct p as [? ?]. split; eauto.
      transitivity (fst y); auto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
Qed.

Lemma eq_term_trans :
  forall G u v w,
    eq_term G u v ->
    eq_term G v w ->
    eq_term G u w.
Proof.
  intros G u v w h1 h2.
  eapply eq_term_upto_univ_trans ; eauto.
  all: clear.
  all: intros x y z h1 h2.
  all: eapply eq_universe_trans ; eauto.
Qed.

Lemma leq_term_trans :
  forall G u v w,
    leq_term G u v ->
    leq_term G v w ->
    leq_term G u w.
Proof.
  intros G u v w h1 h2.
  eapply eq_term_upto_univ_trans ; eauto.
  all: clear.
  all: intros x y z h1 h2.
  - eapply eq_universe_trans ; eauto.
  - eapply leq_universe_trans ; eauto.
Qed.

Lemma eq_term_upto_univ_mkApps_inv :
  forall Re u l u' l',
    isApp u = false ->
    isApp u' = false ->
    eq_term_upto_univ Re Re (mkApps u l) (mkApps u' l') ->
    eq_term_upto_univ Re Re u u' * All2 (eq_term_upto_univ Re Re) l l'.
Proof.
  intros Re u l u' l' hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.