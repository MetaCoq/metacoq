(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
     PCUICContextRelation PCUICSigmaCalculus PCUICContextReduction
     PCUICParallelReduction PCUICParallelReductionConfluence
     PCUICRedTypeIrrelevance.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Instance red_Refl Σ Γ : Reflexive (red Σ Γ) := refl_red Σ Γ.
Instance red_Trans Σ Γ : Transitive (red Σ Γ) := red_trans Σ Γ.

Instance All_decls_refl P : 
  Reflexive P ->
  Reflexive (All_decls P).
Proof. intros hP d; destruct d as [na [b|] ty]; constructor; auto. Qed.
  
Instance All_decls_sym P : 
  Symmetric P ->
  Symmetric (All_decls P).
Proof. intros hP d d' []; constructor; now symmetry. Qed.

Instance All_decls_trans P : 
  Transitive P ->
  Transitive (All_decls P).
Proof. intros hP d d' d'' [] h; depelim h; constructor; now etransitivity. Qed.

Instance All_decls_equivalence P : 
  Equivalence P ->
  Equivalence (All_decls P).
Proof.
  intros []; split; tc.
Qed.

Instance All_decls_preorder P : 
  PreOrder P ->
  PreOrder (All_decls P).
Proof.
  intros []; split; tc.
Qed.

Instance All_decls_alpha_refl P : 
  Reflexive P ->
  Reflexive (All_decls_alpha P).
Proof. intros hP d; destruct d as [na [b|] ty]; constructor; auto. Qed.
  
Instance All_decls_alpha_sym P : 
  Symmetric P ->
  Symmetric (All_decls_alpha P).
Proof. intros hP d d' []; constructor; now symmetry. Qed.

Instance All_decls_alpha_trans P : 
  Transitive P ->
  Transitive (All_decls_alpha P).
Proof. intros hP d d' d'' [] h; depelim h; constructor; now etransitivity. Qed.

Instance All_decls_alpha_equivalence P : 
  Equivalence P ->
  Equivalence (All_decls_alpha P).
Proof.
  intros []; split; tc.
Qed.

Lemma All2_fold_refl P : 
  (forall Γ, Reflexive (P Γ Γ)) ->
  Reflexive (All2_fold P).
Proof.
  intros HR x.
  apply All2_fold_refl; intros. apply HR.
Qed.

Lemma OnOne2_prod {A} (P Q : A -> A -> Type) l l' : 
  OnOne2 (fun x y => P x y × Q x y) l l' ->
  OnOne2 P l l' × OnOne2 Q l l'.
Proof.
  induction 1; split; constructor; intuition eauto.
Qed.

Lemma OnOne2_prod_assoc {A} (P Q R : A -> A -> Type) l l' : 
  OnOne2 (fun x y => (P x y × Q x y) × R x y) l l' ->
  OnOne2 P l l' × OnOne2 (fun x y => Q x y × R x y) l l'.
Proof.
  induction 1; split; constructor; intuition eauto.
Qed.

Lemma OnOne2_apply {A B} (P : B -> A -> A -> Type) l l' : 
  OnOne2 (fun x y => forall a : B, P a x y) l l' ->
  forall a : B, OnOne2 (P a) l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_sigma {A B} (P : B -> A -> A -> Type) l l' : 
  OnOne2 (fun x y => ∑ a : B, P a x y) l l' ->
  ∑ a : B, OnOne2 (P a) l l'.
Proof.
  induction 1.
  - exists p.π1. constructor; auto. exact p.π2.
  - exists IHX.π1. constructor; auto. exact IHX.π2.
Qed.

Lemma OnOne2_local_env_apply {B} {P : B -> context -> term -> term -> Type} {l l'}
  (f : context -> term -> term -> B) : 
  OnOne2_local_env (on_one_decl (fun Γ x y => forall a : B, P a Γ x y)) l l' ->
  OnOne2_local_env (on_one_decl (fun Γ x y => P (f Γ x y) Γ x y)) l l'.
Proof.
  intros; eapply OnOne2_local_env_impl; tea.
  intros Δ x y. eapply on_one_decl_impl; intros Γ ? ?; eauto.
Qed.

Lemma OnOne2_local_env_apply_dep {B : context -> term -> term -> Type} 
  {P : context -> term -> term -> Type} {l l'} :
  (forall Γ' x y, B Γ' x y) ->
  OnOne2_local_env (on_one_decl (fun Γ x y => B Γ x y -> P Γ x y)) l l' ->
  OnOne2_local_env (on_one_decl (fun Γ x y => P Γ x y)) l l'.
Proof.
  intros; eapply OnOne2_local_env_impl; tea.
  intros Δ x y. eapply on_one_decl_impl; intros Γ ? ?; eauto.
Qed.

Lemma OnOne2_exist' {A} (P Q R : A -> A -> Type) (l l' : list A) :
  OnOne2 P l l' ->
  (forall x y : A, P x y -> ∑ z : A, Q x z × R y z) ->
  ∑ r : list A, OnOne2 Q l r × OnOne2 R l' r.
Proof.
  intros o Hp. induction o.
  - specialize (Hp _ _ p) as [? []].
    eexists; split; constructor; eauto.
  - exists (hd :: IHo.π1). split; constructor; auto; apply IHo.π2.
Qed.

Lemma OnOne2_local_env_exist' (P Q R : context -> term -> term -> Type) (l l' : context) :
  OnOne2_local_env (on_one_decl P) l l' ->
  (forall Γ x y, P Γ x y -> ∑ z : term, Q Γ x z × R Γ y z) ->
  ∑ r : context, OnOne2_local_env (on_one_decl Q) l r × OnOne2_local_env (on_one_decl R) l' r.
Proof.
  intros o Hp. induction o.
  - destruct p; subst. specialize (Hp _ _ _ p) as [? []].
    eexists; split; constructor; red; cbn; eauto.
  - destruct p; subst.
    destruct s as [[p ->]|[p ->]]; specialize (Hp _ _ _ p) as [? []];
    eexists; split; constructor; red; cbn; eauto. 
  - exists (d :: IHo.π1). split; constructor; auto; apply IHo.π2.
Qed.

Lemma OnOne2_local_env_All2_fold (P : context -> term -> term -> Type) 
  (Q : context -> context -> context_decl -> context_decl -> Type)
  (l l' : context) :
  OnOne2_local_env (on_one_decl P) l l' ->
  (forall Γ x y, on_one_decl P Γ x y -> Q Γ Γ x y) ->
  (forall Γ Γ' d, OnOne2_local_env (on_one_decl P) Γ Γ' -> Q Γ Γ' d d) ->
  (forall Γ x, Q Γ Γ x x) ->
  All2_fold Q l l'.
Proof.
  intros onc HP IHQ HQ. induction onc; simpl; try constructor; eauto.
  now eapply All2_fold_refl.
  now eapply All2_fold_refl.
Qed.

Lemma on_one_decl_compare_decl Σ Re Rle Γ x y :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  on_one_decl
    (fun (_ : context) (y0 v' : term) => eq_term_upto_univ Σ Re Rle y0 v') Γ x y ->
  compare_decls (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle) x y.
Proof.
  intros heq hle.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; cbn; intuition (subst; auto);
  constructor; auto; reflexivity.
Qed.

Lemma OnOne2_disj {A} (P Q : A -> A -> Type) (l l' : list A) :
  OnOne2 (fun x y => P x y + Q x y)%type l l' <~>
  OnOne2 P l l' + OnOne2 Q l l'.
Proof.
  split.
  - induction 1; [destruct p|destruct IHX]; try solve [(left + right); constructor; auto].
  - intros []; eapply OnOne2_impl; tea; eauto. 
Qed.

Notation red1_ctx_rel Σ Δ := 
  (OnOne2_local_env
    (on_one_decl
      (fun (Γ : context) (x0 y0 : term) => red1 Σ (Δ,,, Γ) x0 y0))).

Notation eq_one_decl Σ Re Rle := 
  (OnOne2_local_env
    (on_one_decl
      (fun _ (x0 y0 : term) => 
        eq_term_upto_univ Σ Re Rle x0 y0))).

Lemma red1_eq_context_upto_l Σ Rle Re Γ Δ u v :
  RelationClasses.Reflexive Rle ->
  SubstUnivPreserving Rle ->
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  red1 Σ Γ u v ->
  eq_context_upto Σ Re Rle Γ Δ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ Re Re v v'.
Proof.
  intros hle hle' he he' hlee h e.
  induction h in Δ, e |- * using red1_ind_all.
  all: try solve [
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    destruct (IHh _ e) as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    match goal with
    | r : red1 _ (?Γ ,, ?d) _ _ |- _ =>
      assert (e' : eq_context_upto Σ Re Rle (Γ,, d) (Δ,, d))
      ; [
        constructor ; [ eauto | constructor; eauto ] ;
        eapply eq_term_upto_univ_refl ; eauto
      |
      ]
    end;
    destruct (IHh _ e') as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  - assert (h : ∑ b',
                (option_map decl_body (nth_error Δ i) = Some (Some b')) *
                eq_term_upto_univ Σ Re Re body b').
    { induction i in Γ, Δ, H, e |- *.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. depelim c; noconf H.
          simpl. eexists; split; eauto.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. eapply IHi in H ; eauto.
    }
    destruct h as [b' [e1 e2]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_lift ; eauto.
  - eapply OnOne2_prod in X as [_ X].
    eapply OnOne2_apply, OnOne2_apply in X; tea.
    eapply OnOne2_exist' in X as [pars' [parred pareq]]; intros; tea.
    eexists. split. eapply case_red_param; tea.
    econstructor; eauto.
    red. intuition; eauto. reflexivity.
    apply All2_same; intros. intuition eauto; reflexivity.
  - eapply (OnOne2_local_env_apply (fun Γ' u v => (Δ ,,, Γ'))) in X.
    cbn in X.
    eapply (OnOne2_local_env_apply_dep) in X; cycle 1.
    intros. eapply eq_context_upto_cat; eauto. reflexivity.
    eapply (OnOne2_local_env_exist' _ (fun Γ x y => red1 Σ (Δ ,,, Γ) x y)) in X; intros; tea.
    2:{ exact X0. }
    destruct X as [ocontext'' [red eq]]. eexists; split.
    * eapply case_red_pcontext; tea.
    * econstructor; eauto; try reflexivity.
      red; intuition; simpl; eauto.
      eapply OnOne2_local_env_All2_fold; tea => /= //; try reflexivity.
      + intros *. now eapply on_one_decl_compare_decl.
      + eapply All2_same; split; reflexivity.
  - specialize (IHh (Δ ,,, pcontext p)).
    forward IHh. now apply eq_context_upto_cat.
    destruct IHh as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try red; intuition (simpl; eauto); try reflexivity.
      * now eapply All2_same.
      * eapply All2_same. split; reflexivity.
  - specialize (IHh _ e) as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try red; intuition (simpl; eauto); try reflexivity.
      * now eapply All2_same.
      * eapply All2_same. split; reflexivity.
  - eapply OnOne2_disj in X.
    destruct X as [X|X].
    * eapply (OnOne2_impl (Q:=fun x y => (∑ v', _) × bcontext x = bcontext y)) in X; tea.
      2:{ intros x y [[red IH] eq]. split; tas. 
          specialize (IH (Δ ,,, bcontext x)).
          forward IH by now apply eq_context_upto_cat. exact IH. }
      eapply (OnOne2_exist' _ (fun x y => on_Trel_eq (red1 Σ (Δ ,,, bcontext x)) bbody bcontext x y)
        (fun x y => on_Trel_eq (eq_term_upto_univ Σ Re Re) bbody bcontext x y)) in X as [brr [Hred Heq]]; tea.
      2:{ intros x y [[v' [redv' eq]] eqctx].
          exists {| bcontext := bcontext x; bbody := v' |}.
          intuition auto. }
      eexists; split.
      eapply case_red_brs.
      + eapply OnOne2_disj. left; tea.
      + econstructor; eauto; try reflexivity.
        eapply OnOne2_All2; tea => /=; intuition eauto; try reflexivity.
        now rewrite b.
    * eapply (OnOne2_impl (Q:=fun x y => (∑ v', _) × bbody x = bbody y)) in X; tea.
      2:{ intros x y [red eq]. split => //.
        eapply (OnOne2_local_env_apply (fun Γ' u v => (Δ ,,, Γ'))) in red.
        cbn in red.
        eapply (OnOne2_local_env_apply_dep) in red; cycle 1.
        intros. eapply eq_context_upto_cat; eauto. now reflexivity.
        eapply (OnOne2_local_env_exist' _ (fun Γ x y => red1 Σ (Δ ,,, Γ) x y)) in red; intros.
        2:{ exact X0. }
        exact red. }
    eapply (OnOne2_exist' _ 
      (fun x y => on_Trel_eq (red1_ctx_rel Σ Δ) bcontext bbody x y)
      (fun x y => on_Trel_eq (eq_one_decl Σ Re Re) bcontext bbody x y)) in X as [brr [Hred Heq]]; tea.
    2:{ intros x y [[v' [redv' eqctx]] ->].
        exists {| bcontext := v'; bbody := bbody y |}.
        intuition (simpl; auto). }
    eexists; split.
    eapply case_red_brs.
    + eapply OnOne2_disj. right; tea.
    + econstructor; eauto; try reflexivity.
      eapply OnOne2_All2; tea => /=; intuition eauto; try reflexivity.
      2:{ now rewrite b. }
      eapply OnOne2_local_env_All2_fold; tea => /= //; try reflexivity.
      intros *. now eapply on_one_decl_compare_decl.

  - destruct (IHh _ e) as [x [redl redr]].
    exists (tApp x M2).
    split. constructor; auto.
    constructor. eapply eq_term_upto_univ_impl. 5:eauto.
    all:auto. 1-3:typeclasses eauto.
    reflexivity.
  - assert (h : ∑ ll,
      OnOne2 (red1 Σ Δ) l ll *
      All2 (eq_term_upto_univ Σ Re Re) l' ll
    ).
    { induction X.
      - destruct p as [p1 p2].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor. eassumption.
        + constructor.
          * assumption.
          * eapply All2_same.
            intros.
            eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [ll [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix'
      *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) *
        (eq_binder_annot (dname x) (dname y)))%type mfix1 mfix').
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            1-2: eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          1-2: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) * 
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
         fix_context intact. Anything general?
       *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
         unfortunately...
       *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
       (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
           eq_context_upto Σ Re Rle (Γ ,,, fix_context L) Δ ->
           ∑ v' : term,
             red1 Σ Δ (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v'))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    ((red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
     × (forall Δ0 : context,
        eq_context_upto Σ Re Rle (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
          red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v'))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
  (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  OnOne2
      (fun d d' : def term =>
       red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
       × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
         ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
         (rarg x = rarg y)) *
         eq_binder_annot (dname x) (dname y)) mfix1 mfix') _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
           e' : eq_context_upto Σ Re Rle (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_cat ; eauto. reflexivity. }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_body. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) *
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix'
    ).
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) * 
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
         fix_context intact. Anything general?
       *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
         unfortunately...
       *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
       (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
           eq_context_upto Σ Re Rle (Γ ,,, fix_context L) Δ ->
           ∑ v' : term,
             red1 Σ Δ (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v' ))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
     × (forall Δ0 : context,
        eq_context_upto Σ Re Rle (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
           red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v' ))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  (OnOne2
      (fun d d' : def term =>
       red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
       × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
         ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
         rarg x = rarg y) *
         eq_binder_annot (dname x) (dname y)) mfix1 mfix')) _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
           e' : eq_context_upto Σ Re Rle (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_cat ; eauto. reflexivity. }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_body. eassumption.
    + constructor; assumption.
Qed.

Lemma eq_context_gen_context_assumptions {eq leq Γ Δ} :
  eq_context_gen eq leq Γ Δ ->
  context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1; simpl; auto;
  destruct p => /= //; try lia.  
Qed.

Lemma eq_context_extended_subst {Σ Re Rle Γ Δ k} :
  eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle) Γ Δ ->
  All2 (eq_term_upto_univ Σ Re Re) (extended_subst Γ k) (extended_subst Δ k).
Proof.
  intros Heq.
  induction Heq in k |- *; simpl.
  - constructor; auto.
  - depelim p => /=.
    * constructor. eauto. constructor; eauto. eauto.
    * constructor.
      + rewrite (eq_context_gen_context_assumptions Heq).
        len. rewrite (All2_fold_length Heq).
        eapply eq_term_upto_univ_substs; eauto. tc.
        eapply eq_term_upto_univ_lift, e0.
      + eapply IHHeq.
Qed.

Lemma eq_context_gen_eq_context_upto Σ Re Rle Γ Γ' :
  eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle) Γ Γ' ->
  eq_context_upto Σ Re Rle Γ Γ'.
Proof.
  intros.
  eapply All2_fold_impl_len; tea.
  intros. depelim X0; constructor; auto.
Qed.

Lemma red1_eq_context_upto_univ_l Σ Re Rle Γ ctx ctx' ctx'' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_context_gen (eq_term_upto_univ Σ Re Re)
   (eq_term_upto_univ Σ Re Re) ctx ctx' ->
  OnOne2_local_env (on_one_decl
    (fun (Γ' : context) (u v : term) =>
    forall (Rle : Relation_Definitions.relation Universe.t)
      (napp : nat) (u' : term),
    RelationClasses.Reflexive Re ->
    RelationClasses.Reflexive Rle ->
    RelationClasses.Transitive Re ->
    RelationClasses.Transitive Rle ->
    SubstUnivPreserving Re ->
    SubstUnivPreserving Rle ->
    (forall x y : Universe.t, Re x y -> Rle x y) ->
    eq_term_upto_univ_napp Σ Re Rle napp u u' ->
    ∑ v' : term,
      red1 Σ (Γ,,, Γ') u' v'
      × eq_term_upto_univ_napp Σ Re Rle napp v v')) ctx ctx'' ->
  ∑ pctx,
    red1_ctx_rel Σ Γ ctx' pctx *
    eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Re) ctx'' pctx.
Proof.
  intros. 
  rename X into e, X0 into X.
  induction X in e, ctx' |- *.
  - red in p. simpl in p.
    depelim e. depelim c.
    destruct p as [-> p].
    eapply p in e1 as hh ; eauto.
    destruct hh as [? [? ?]].
    eapply red1_eq_context_upto_l in r; cycle -1.
    { eapply eq_context_upto_cat.
      2:{ eapply eq_context_gen_eq_context_upto; tea. }
      reflexivity. }
    all:try tc.
    destruct r as [v' [redv' eqv']].
    eexists; split.
    + constructor; tea. red. cbn. split; tea. reflexivity.
    + constructor. all: eauto. constructor; auto.
      now transitivity x.
  - depelim e.
    depelim c.
    destruct p as [-> [[p ->]|[p ->]]].
    { eapply p in e2 as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_l in r; cycle -1.
      { eapply eq_context_upto_cat.
        2:{ eapply eq_context_gen_eq_context_upto; tea. }
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        left. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
    { eapply p in e1 as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_l in r; cycle -1.
      { eapply eq_context_upto_cat.
        2:{ eapply eq_context_gen_eq_context_upto; tea. }
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        right. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
  - depelim e.
    destruct (IHX _ e) as [? [? ?]].
    eexists. split.
    + now eapply onone2_localenv_cons_tl.
    + constructor. all: eauto.
Qed.

Lemma red1_eq_term_upto_univ_l Σ Re Rle napp Γ u v u' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ_napp Σ Re Rle napp u u' ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' *
         eq_term_upto_univ_napp Σ Re Rle napp v v'.
Proof.
  unfold RelationClasses.subrelation.
  intros he he' tRe tRle hle hle' hR e h.
  induction h in napp, u', e, he, he', tRe, tRle, Rle, hle, hle', hR |- * using red1_ind_all.
  all: try solve [
    dependent destruction e ;
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto
    ]
  ].
  (* tLambda and tProd *)
  10,16:solve [
    dependent destruction e ;
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto ;
    clear h;
    lazymatch goal with
    | r : red1 _ (?Γ,, vass ?na ?A) ?u ?v,
      e :  eq_term_upto_univ_napp _ _ _ _ ?A ?B
      |- _ =>
      let hh := fresh "hh" in
      eapply red1_eq_context_upto_l in r as hh ; revgoals;
      [
        constructor (* with (nb := na) *) ; [
          eapply (eq_context_upto_refl _ Re Re); eauto
        | constructor; tea
        ]
      | reflexivity
      | assumption
      | assumption
      | assumption
      | assumption
      | destruct hh as [? [? ?]]
      ]
    end;
    eexists ; split; [ solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      eapply eq_term_upto_univ_trans ; eauto ;
      eapply eq_term_upto_univ_leq ; eauto
    ]
  ].
  - dependent destruction e. dependent destruction e1.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_substs ; eauto.
      eapply leq_term_leq_term_napp; eauto.
  - dependent destruction e.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_substs ; try assumption.
      eapply leq_term_leq_term_napp; eauto.
      auto.
  - dependent destruction e.
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_refl ; assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e0 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eapply All2_nth_error_Some in a as [t' [hnth [eqctx eqbod]]]; tea.
    have lenctxass := eq_context_gen_context_assumptions eqctx.
    have lenctx := All2_fold_length eqctx.
    eexists. split.
    + constructor; tea. 
      epose proof (All2_length h2). rewrite !List.skipn_length in H0 |- *. 
      congruence.
    + unfold iota_red.
      eapply eq_term_upto_univ_substs => //.
      { rewrite /expand_lets /expand_lets_k.
        eapply eq_term_upto_univ_substs => //.
        { simpl. rewrite lenctxass lenctx.
          eapply eq_term_upto_univ_lift => //.
          eapply eq_term_upto_univ_leq; tea. lia. }
      eapply eq_context_extended_subst; tea. }
      now eapply All2_rev, All2_skipn.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_fix in H.
    case_eq (nth_error mfix idx) ;
      try (intros e ; rewrite e in H ; discriminate H).
    intros d e. rewrite e in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in a as hh ; try eassumption.
    destruct hh as [d' [e' [[[? ?] erarg] eann]]].
    unfold is_constructor in H0.
    case_eq (nth_error args (rarg d)) ;
      try (intros bot ; rewrite bot in H0 ; discriminate H0).
    intros a' ea.
    rewrite ea in H0.
    eapply All2_nth_error_Some in ea as hh ; try eassumption.
    destruct hh as [a'' [ea' ?]].
    eexists. split.
    + eapply red_fix.
      * unfold unfold_fix. rewrite e'; eauto.
      * unfold is_constructor. rewrite <- erarg. rewrite ea'.
        eapply isConstruct_app_eq_term_l ; eassumption.
    + eapply eq_term_upto_univ_napp_mkApps.
      * eapply eq_term_upto_univ_substs ; eauto.
        -- eapply (eq_term_upto_univ_leq _ _ _ 0) ; eauto with arith. 
        -- unfold fix_subst.
           apply All2_length in a as el. rewrite <- el.
           generalize #|mfix|. intro n.
           induction n.
           ++ constructor.
           ++ constructor ; eauto.
              constructor. assumption.
      * assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e0 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    destruct (nth_error mfix idx) eqn:hnth; noconf H.
    eapply All2_nth_error_Some in a0 as hh ; tea.
    destruct hh as [d' [e' [[[? ?] erarg] eann]]].
    eexists. split.
    + eapply red_cofix_case.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor. all: eauto.
      eapply eq_term_upto_univ_mkApps. all: eauto.
      eapply eq_term_upto_univ_substs ; eauto; try exact _.
      eapply (eq_term_upto_univ_leq _ _ _ 0); auto with arith.
      typeclasses eauto.
      unfold cofix_subst.
      apply All2_length in a0 as el. rewrite <- el.
      generalize #|mfix|. intro n.
      induction n.
      * constructor.
      * constructor ; eauto.
        constructor. assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    case_eq (nth_error mfix idx) ;
      try (intros e ; rewrite e in H ; discriminate H).
    intros d e. rewrite e in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in e as hh ; try eassumption.
    destruct hh as [d' [e' [[[? ?] erarg] eann]]].
    eexists. split.
    + eapply red_cofix_proj.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor.
      eapply eq_term_upto_univ_mkApps. all: eauto.
      eapply eq_term_upto_univ_substs ; eauto; try exact _.
      eapply (eq_term_upto_univ_leq _ _ _ 0); auto with arith.
      typeclasses eauto.
      unfold cofix_subst.
      apply All2_length in a as el. rewrite <- el.
      generalize #|mfix|. intro n.
      induction n.
      * constructor.
      * constructor ; eauto.
        constructor. assumption.
  - dependent destruction e.
    eexists. split.
    + econstructor. all: eauto.
    + eapply (eq_term_upto_univ_leq _ _ _ 0); tas. auto. auto with arith.
      now apply eq_term_upto_univ_subst_instance.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eapply All2_nth_error_Some in h2 as hh ; try eassumption.
    destruct hh as [arg' [e' ?]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_leq ; eauto.
      eapply eq_term_eq_term_napp; auto. typeclasses eauto.
  - dependent destruction e.
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto.
    clear h.
    lazymatch goal with
    | r : red1 _ (?Γ,, vdef ?na ?a ?A) ?u ?v,
      e1 : eq_term_upto_univ _ _ _ ?A ?B,
      e2 : eq_term_upto_univ _ _ _ ?a ?b
      |- _ =>
      let hh := fresh "hh" in
      eapply red1_eq_context_upto_l in r as hh ; revgoals ; [
        constructor (* with (nb := na) *) ; [
          eapply (eq_context_upto_refl _ Re Re) ; eauto
        | econstructor; tea
        ]
      | reflexivity
      | assumption
      | assumption
      | assumption
      | assumption
      | destruct hh as [? [? ?]]
      ]
     end.
    eexists. split.
    + eapply letin_red_body ; eauto.
    + constructor ; eauto.
      eapply eq_term_upto_univ_trans ; eauto.
      eapply eq_term_upto_univ_leq ; eauto.
  - dependent destruction e.
    destruct e as [? [? [? ?]]].
    eapply OnOne2_prod_inv in X as [_ X].
    assert (h : ∑ args,
               OnOne2 (red1 Σ Γ) (pparams p') args *
               All2 (eq_term_upto_univ Σ Re Re) params' args
           ).
    { destruct p, p' as []; cbn in *.
      induction X in a0, pparams, pparams0, X |- *.
      - depelim a0.
        eapply p in e as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor; tea.
        + constructor. all: eauto.
      - depelim a0.
        destruct (IHX _ a0) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [pars0 [? ?]].
    eexists. split.
    + eapply case_red_param. eassumption.
    + constructor. all: eauto.
      red; intuition eauto.
  - dependent destruction e.
    destruct e as [? [? [? ?]]].
    destruct p, p'; cbn in *.
    eapply red1_eq_context_upto_univ_l in X; tea; try tc.
    destruct X as [pctx0 [? ?]].
    eexists. split.
    + eapply case_red_pcontext. eassumption.
    + constructor. all: eauto.
      red; intuition eauto.
  - depelim e.
    destruct e as [? [? [? ?]]].
    eapply IHh in e => //.
    destruct e as [v' [red eq]].
    eapply red1_eq_context_upto_l in red.
    7:{ eapply eq_context_upto_cat. 2:{ eapply eq_context_gen_eq_context_upto; tea. }
        reflexivity. }
    all:try tc.
    destruct red as [ret' [redret eqret]].
    eexists; split.
    + eapply case_red_return; tea.
    + econstructor; eauto.
      red; simpl; intuition eauto.
      now transitivity v'.

  - depelim e.
    eapply OnOne2_disj in X as [X|X].
    + eapply OnOne2_prod_assoc in X as [_ X].
      assert (h : ∑ brs0,
               OnOne2 (fun br br' => on_Trel_eq (red1 Σ (Γ ,,, bcontext br)) bbody bcontext br br') brs' brs0 *
               All2 (fun x y =>
                       eq_context_gen (eq_term_upto_univ Σ Re Re) 
                        (eq_term_upto_univ Σ Re Re) (bcontext x) (bcontext y) *
                       (eq_term_upto_univ Σ Re Re (bbody x) (bbody y))
                       )%type brs'0 brs0
           ).
      { induction X in a, brs' |- *.
        - destruct p0 as [p2 p3].
          dependent destruction a. destruct p0 as [h1 h2].
          eapply p2 in h2 as hh ; eauto.
          destruct hh as [? [? ?]].
          eapply red1_eq_context_upto_l in r; cycle -1.
          { eapply eq_context_upto_cat.
            2:{ eapply eq_context_gen_eq_context_upto, h1. }
            reflexivity. }
          all:try tc.
          destruct r as [v' [redv' eqv']].
          eexists. split.
          + constructor.
            instantiate (1 := {| bcontext := bcontext y; bbody := v' |}). cbn. split ; eauto.
          + constructor. all: eauto.
            split ; eauto. cbn. transitivity (bcontext hd) ; eauto.
            now rewrite p3. simpl. now transitivity x.
        - dependent destruction a.
          destruct (IHX _ a) as [? [? ?]].
          eexists. split.
          + eapply OnOne2_tl. eassumption.
          + constructor. all: eauto.
      }
      destruct h as [brs0 [? ?]].
      eexists. split.
      * eapply case_red_brs. eapply OnOne2_disj. left; tea.
      * constructor. all: eauto.

    + assert (h : ∑ brs0,
               OnOne2 (fun br br' => on_Trel_eq (red1_ctx_rel Σ Γ) bcontext bbody br br') brs' brs0 *
               All2 (fun x y =>
                       eq_context_gen (eq_term_upto_univ Σ Re Re) 
                        (eq_term_upto_univ Σ Re Re) (bcontext x) (bcontext y) *
                       eq_term_upto_univ Σ Re Re (bbody x) (bbody y)
                       )%type brs'0 brs0
           ).
      { induction X in a, brs' |- *.
        - destruct p0 as [p2 p3].
          dependent destruction a. destruct p0 as [h1 h2].
          eapply red1_eq_context_upto_univ_l in p2; tea; try tc.
          destruct p2 as [pctx [pred peq]].
          eexists. split.
          + constructor. split.
            instantiate (1 := {| bcontext := pctx; bbody := bbody y |}); tea.
            reflexivity.
          + constructor. split; eauto. simpl.
            transitivity (bbody hd); eauto.
            now rewrite -p3.
            auto.
        - dependent destruction a.
          destruct (IHX _ a) as [? [? ?]].
          eexists. split.
          + eapply OnOne2_tl. eassumption.
          + constructor. all: eauto.
      }
      destruct h as [brs0 [? ?]].
      eexists. split.
      * eapply case_red_brs. eapply OnOne2_disj. right; tea.
      * constructor. all: eauto.
      
  - dependent destruction e.
    assert (h : ∑ args,
               OnOne2 (red1 Σ Γ) args' args *
               All2 (eq_term_upto_univ Σ Re Re) l' args
           ).
    { induction X in a, args' |- *.
      - destruct p as [p1 p2].
        dependent destruction a.
        eapply p2 in e as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor. eassumption.
        + constructor. all: eauto.
      - dependent destruction a.
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun d0 d1 =>
                   red1 Σ Γ d0.(dtype) d1.(dtype) ×
                   (d0.(dname), d0.(dbody), d0.(rarg)) =
                   (d1.(dname), d1.(dbody), d1.(rarg))
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)) * 
                 eq_binder_annot (dname x) (dname y))%type mfix1 mfix
           ).
    { induction X in a, mfix' |- *.
      - destruct p as [[p1 p2] p3].
        dependent destruction a.
        destruct p as [[[h1 h2] h3] h4].
        eapply p2 in h1 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. inversion p3.
          repeat split ; eauto.
      - dependent destruction a. destruct p as [[[h1 h2] h3] h4].
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun x y =>
                   red1 Σ (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
                   (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)) * 
                 eq_binder_annot (dname x) (dname y)) mfix1 mfix
           ).
    { revert mfix' a.
      refine (OnOne2_ind_l _ (fun L x y => (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Rle napp (u' : term),
           RelationClasses.Reflexive Re ->
           RelationClasses.Reflexive Rle ->
           RelationClasses.Transitive Re ->
           RelationClasses.Transitive Rle ->
           SubstUnivPreserving Re ->
           SubstUnivPreserving Rle ->
           (forall u u'0 : Universe.t, Re u u'0 -> Rle u u'0) ->
           eq_term_upto_univ_napp Σ Re Rle napp (dbody x) u' ->
           ∑ v' : term,
             red1 Σ (Γ ,,, fix_context L) u' v'
                  × eq_term_upto_univ_napp Σ Re Rle napp (dbody y) v' ))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => forall mfix', All2
      (fun x y : def term =>
       ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) * eq_binder_annot (dname x) (dname y)) mfix0 mfix' -> ∑ mfix : list (def term),
  ( OnOne2
      (fun x y : def term =>
       red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix' mfix ) *
  ( All2
      (fun x y : def term =>
       ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       (rarg x = rarg y)) * eq_binder_annot (dname x) (dname y)) mfix1 mfix )) _ _ _ _ X).
      - clear X. intros L x y l [[p1 p2] p3] mfix' h.
        dependent destruction h. destruct p as [[[h1 h2] h3] h4].
        eapply p2 in h2 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor. constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto. reflexivity.
        + constructor. constructor; simpl. all: eauto.
          inversion p3.
          simpl. repeat split ; eauto. destruct y0. simpl in *.
          congruence.
      - clear X. intros L x l l' h ih mfix' ha.
        dependent destruction ha. destruct p as [[h1 h2] h3].
        destruct (ih _ ha) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eauto.
        + constructor. constructor. all: eauto.
    }
    destruct h as [mfix [? ?]].
    assert (h : ∑ mfix,
      OnOne2 (fun x y =>
                  red1 Σ (Γ ,,, fix_context mfix') x.(dbody) y.(dbody) ×
                  (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
               ) mfix' mfix ×
        All2 (fun x y =>
                eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                (x.(rarg) = y.(rarg)) *
                eq_binder_annot (dname x) (dname y)
             ) mfix1 mfix %type
    ).
    { clear X.
      assert (hc : eq_context_upto Σ
                     Re Rle
                     (Γ ,,, fix_context mfix0)
                     (Γ ,,, fix_context mfix')
             ).
      { eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl; assumption.
        - clear -he hle tRe tRle hR a. induction a.
          + constructor.
          + destruct r as [[[? ?] ?] ?].
            eapply All2_eq_context_upto.
            eapply All2_rev.
            eapply All2_mapi.
            constructor.
            * intros i. split; [split|]; cbn.
              -- assumption.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift.
                 eapply eq_term_upto_univ_impl; eauto.
                 all:typeclasses eauto.
            * eapply All2_impl ; eauto.
              intros ? ? [[[? ?] ?] ?] i. split; [split|].
              -- assumption.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift.
                 eapply eq_term_upto_univ_impl; eauto.
                 typeclasses eauto.
      }
      clear a.
      eapply OnOne2_impl_exist_and_All ; try eassumption.
      clear o a0.
      intros x x' y [r e] [[[? ?] ?] ?].
      inversion e. clear e.
      eapply red1_eq_context_upto_l in r as [? [? ?]].
      7: eassumption. all: tea.
      eexists. constructor.
      instantiate (1 := mkdef _ _ _ _ _). simpl.
      intuition eauto.
      intuition eauto.
      - rewrite H1. eauto.
      - eapply eq_term_upto_univ_trans; tea.
      - etransitivity ; eauto.
      - now simpl.
    }
    destruct h as [? [? ?]].
    eexists. split.
    +  eapply fix_red_body. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun d0 d1 =>
                   red1 Σ Γ d0.(dtype) d1.(dtype) ×
                   (d0.(dname), d0.(dbody), d0.(rarg)) =
                   (d1.(dname), d1.(dbody), d1.(rarg))
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)) *
                 eq_binder_annot (dname x) (dname y))%type mfix1 mfix
           ).
    { induction X in a, mfix' |- *.
      - destruct p as [[p1 p2] p3].
        dependent destruction a.
        destruct p as [[[h1 h2] h3] h4].
        eapply p2 in h1 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. inversion p3.
          repeat split ; eauto.
      - dependent destruction a. destruct p as [[h1 h2] h3].
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun x y =>
                   red1 Σ (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
                   (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)) * 
                 eq_binder_annot (dname x) (dname y)
               ) mfix1 mfix
           ).
    { revert mfix' a.
      refine (OnOne2_ind_l _ (fun L x y => (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Rle napp (u' : term),
            RelationClasses.Reflexive Re ->
            RelationClasses.Reflexive Rle ->
            RelationClasses.Transitive Re ->
            RelationClasses.Transitive Rle ->
            SubstUnivPreserving Re ->
            SubstUnivPreserving Rle ->
           (forall u u'0 : Universe.t, Re u u'0 -> Rle u u'0) ->
           eq_term_upto_univ_napp Σ Re Rle napp (dbody x) u' ->
           ∑ v' : term,
             red1 Σ (Γ ,,, fix_context L) u' v'
               × eq_term_upto_univ_napp Σ Re Rle napp (dbody y) v'))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => forall mfix', All2
      (fun x y : def term =>
       ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) * eq_binder_annot (dname x) (dname y)) mfix0 mfix' -> ∑ mfix : list (def term),
  ( OnOne2
      (fun x y : def term =>
       red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix' mfix ) *
  ( All2
      (fun x y : def term =>
       ((eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) * eq_binder_annot (dname x) (dname y)) mfix1 mfix )) _ _ _ _ X).
      - clear X. intros L x y l [[p1 p2] p3] mfix' h.
        dependent destruction h. destruct p as [[[h1 h2] h3] h4].
        eapply p2 in h2 as hh ; eauto.
        destruct hh as [? [? ?]].
        noconf p3. hnf in H. noconf H.
        eexists. split; simpl.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. repeat split ; eauto; congruence.
      - clear X. intros L x l l' h ih mfix' ha.
        dependent destruction ha. destruct p as [[h1 h2] h3].
        destruct (ih _ ha) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eauto.
        + constructor. all: eauto.
    }
    destruct h as [mfix [? ?]].
    assert (h : ∑ mfix,
      OnOne2 (fun x y =>
                  red1 Σ (Γ ,,, fix_context mfix') x.(dbody) y.(dbody) ×
                  (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
               ) mfix' mfix ×
        All2 (fun x y =>
                eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                (x.(rarg) = y.(rarg)) *
                eq_binder_annot (dname x) (dname y)
             ) mfix1 mfix
    ).
    { clear X.
      assert (hc : eq_context_upto Σ
                     Re Rle
                     (Γ ,,, fix_context mfix0)
                     (Γ ,,, fix_context mfix')
             ).
      { eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl; assumption.
        - clear -he he' hle hle' hR a. induction a.
          + constructor.
          + destruct r as [[[? ?] ?] ?].
            eapply All2_eq_context_upto.
            eapply All2_rev.
            eapply All2_mapi.
            constructor.
            * intros i. split; [split|].
              -- assumption.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift.
                 eapply eq_term_upto_univ_impl; eauto.
                 all:typeclasses eauto.
            * eapply All2_impl ; eauto.
              intros ? ? [[[? ?] ?] ?] i. split; [split|].
              -- assumption.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift.
                 eapply eq_term_upto_univ_impl; eauto.
                 all:typeclasses eauto.
      }
      clear a.
      eapply OnOne2_impl_exist_and_All ; try eassumption.
      clear o a0.
      intros x x' y [r e] [[? ?] ?].
      inversion e. clear e.
      eapply red1_eq_context_upto_l in r as [? [? ?]].
      7: eassumption. all: tea.
      eexists.
      instantiate (1 := mkdef _ _ _ _ _). simpl.
      intuition eauto.
      - rewrite H1. eauto.
      - eapply eq_term_upto_univ_trans ; tea.
      - etransitivity ; eauto.
      - congruence.
    }
    destruct h as [? [? ?]].
    eexists. split.
    +  eapply cofix_red_body. eassumption.
    + constructor. all: eauto.
Qed.


Lemma Forall2_flip {A} (R : A -> A -> Prop) (x y : list A) : 
  Forall2 (flip R) y x -> Forall2 R x y.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma R_universe_instance_flip R u u' :
  R_universe_instance (flip R) u' u ->
  R_universe_instance R u u'.
Proof.
  unfold R_universe_instance.
  apply Forall2_flip.
Qed.

Lemma eq_context_upto_flip {Σ Re Rle Γ Δ}
  `{!RelationClasses.Reflexive Re}
  `{!RelationClasses.Symmetric Re}
  `{!RelationClasses.Transitive Re}
  `{!RelationClasses.Reflexive Rle}
  `{!RelationClasses.Transitive Rle}
  `{!RelationClasses.subrelation Re Rle} :
  eq_context_upto Σ Re Rle Γ Δ ->
  eq_context_upto Σ Re (flip Rle) Δ Γ.
Proof.
  induction 1; constructor; auto; depelim p; constructor; auto.
  - now symmetry.
  - now eapply eq_term_upto_univ_napp_flip; try typeclasses eauto.
  - now symmetry.
  - now eapply eq_term_upto_univ_napp_flip; try typeclasses eauto.
  - now eapply eq_term_upto_univ_napp_flip; try typeclasses eauto.
Qed.

Lemma red1_eq_context_upto_r Σ Re Rle Γ Δ u v :
  RelationClasses.Equivalence Re ->
  RelationClasses.PreOrder Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  red1 Σ Γ u v ->
  eq_context_upto Σ Re Rle Δ Γ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ Re Re v' v.
Proof.
  intros.
  destruct (red1_eq_context_upto_l Σ (flip Rle) Re Γ Δ u v); auto; try typeclasses eauto.
  - intros x; red; reflexivity.
  - intros s u1 u2 Ru. red. apply R_universe_instance_flip in Ru. now apply H2.
  - intros x y rxy; red. now symmetry in rxy.
  - now apply eq_context_upto_flip.
  - exists x. intuition auto.
    now eapply eq_term_upto_univ_sym.
Qed.

Lemma red1_eq_term_upto_univ_r Σ Re Rle napp Γ u v u' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ_napp Σ Re Rle napp u' u ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' ×
        eq_term_upto_univ_napp Σ Re Rle napp v' v.
Proof.
  intros he he' hse hte htle sre srle hR h uv.
  destruct (red1_eq_term_upto_univ_l Σ Re (flip Rle) napp Γ u v u'); auto.
  - now eapply flip_Transitive.
  - red. intros s u1 u2 ru.
    apply R_universe_instance_flip in ru.
    now apply srle.
  - intros x y X. symmetry in X. apply hR in X. apply X.
  - eapply eq_term_upto_univ_napp_flip; eauto.
  - exists x. intuition auto.
    eapply (eq_term_upto_univ_napp_flip Σ Re (flip Rle) Rle); eauto.
    + now eapply flip_Transitive.
    + unfold flip. intros ? ? H. symmetry in H. eauto.
Qed.

Section RedEq.
  Context (Σ : global_env_ext).
  Context {Re Rle : Universe.t -> Universe.t -> Prop}
          {refl : RelationClasses.Reflexive Re}
          {refl': RelationClasses.Reflexive Rle}
          {pres : SubstUnivPreserving Re}
          {pres' : SubstUnivPreserving Rle}
          {sym : RelationClasses.Symmetric Re}
          {trre : RelationClasses.Transitive Re}
          {trle : RelationClasses.Transitive Rle}.
  Context (inclre : RelationClasses.subrelation Re Rle).

  Lemma red_eq_term_upto_univ_r {Γ T V U} :
    eq_term_upto_univ Σ Re Rle T U -> red Σ Γ U V ->
    ∑ T', red Σ Γ T T' * eq_term_upto_univ Σ Re Rle T' V.
  Proof.
    intros eq r.
    induction r in T, eq |- *.
    - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto.
    - exists T; split; eauto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_l {Γ u v u'} :
    eq_term_upto_univ Σ Re Rle u u' ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Γ u' v' *
    eq_term_upto_univ Σ Re Rle v v'.
  Proof.
    intros eq r.
    induction r in u', eq |- *.
    - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.
End RedEq.



Polymorphic Derive Signature for Relation.clos_refl_trans.

Derive Signature for red1.

Lemma local_env_telescope P Γ Γ' Δ Δ' :
  All2_telescope (on_decls P) Γ Γ' Δ Δ' ->
  All2_fold_over P Γ Γ' (List.rev Δ) (List.rev Δ').
Proof.
  induction 1. simpl. constructor.
  - depelim p. simpl. eapply All2_fold_over_app. repeat constructor => //.
    simpl. 
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor; auto. depelim p0; constructor; auto;
    unfold on_decls_over in *;
    now rewrite !app_context_assoc.
  - simpl. eapply All2_fold_over_app. constructor. 2:auto. constructor.
    simpl. unfold on_decls_over in *. depelim p.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor; auto. depelim p1; constructor; auto; unfold on_decls_over in *;
    now rewrite !app_context_assoc.
Qed.

Lemma All_All2_telescopei_gen P (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_fold_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_fold_over P Γ Γ' Δ Δ' ->
  All2_telescope_n (on_decls P) (fun n : nat => lift0 n)
                   (Γ ,,, Δ) (Γ' ,,, Δ') #|Δ|
    (map (fun def : def term => vass (dname def) (dtype def)) m)
    (map (fun def : def term => vass (dname def) (dtype def)) m').
Proof.
  intros weakP.
  induction 1 in Δ, Δ' |- *; cbn. constructor.
  intros. destruct r. rewrite e. constructor.
  constructor.
  rewrite {2}(All2_fold_length X0).
  now eapply weakP.
  specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                  (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')).
  forward IHX.
  constructor; auto. constructor. now eapply weakP. simpl in IHX.
  rewrite {2}(All2_fold_length X0).
  apply IHX.
Qed.

Lemma All_All2_telescopei P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_fold_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_telescope_n (on_decls P) (fun n => lift0 n)
                   Γ Γ' 0
                   (map (fun def => vass (dname def) (dtype def)) m)
                   (map (fun def => vass (dname def) (dtype def)) m').
Proof.
  specialize (All_All2_telescopei_gen P Γ Γ' [] [] m m'). simpl.
  intros. specialize (X X0 X1). apply X; constructor.
Qed.

Lemma All2_All2_fold_fix_context P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_fold_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_fold (on_decls (on_decls_over P Γ Γ')) (fix_context m) (fix_context m').
Proof.
  intros Hweak a. unfold fix_context.
  eapply local_env_telescope.
  cbn.
  rewrite - !(mapi_mapi
                (fun n def => vass (dname def) (dtype def))
                (fun n decl => lift_decl n 0 decl)).
  eapply All2_telescope_mapi.
  rewrite !mapi_cst_map.
  eapply All_All2_telescopei; eauto.
Qed.

Section RedPred.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Hint Resolve pred1_ctx_over_refl : pcuic.
  Hint Unfold All2_prop2_eq : pcuic.
  Hint Transparent context : pcuic.
  Hint Transparent mfixpoint : pcuic.

  Hint Mode pred1 ! ! ! ! - : pcuic.

  Ltac pcuic := simpl; try typeclasses eauto with pcuic.

  (** Strong substitutivity gives context conversion of reduction!
      It cannot be strenghtened to deal with let-ins: pred1 is
      precisely not closed by arbitrary reductions in contexts with let-ins.
   *)

  Lemma pred1_ctx_pred1 Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u ->
    assumption_context Δ ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u.
  Proof.
    intros Hlen X H X0.
    pose proof (strong_substitutivity _ wfΣ _ _ (Γ ,,, Δ) (Γ' ,,, Δ') _ _ ids ids X).
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite H0. simpl. rewrite e. reflexivity. }
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0 |- *; try lia.
      eapply All2_fold_app_inv in X0 as [_ X0] => //.
      pose proof (All2_fold_length X0).
      rewrite nth_error_app_ge. lia. now rewrite -H1 H0 /= e. }
    forward X1.
    red. intros x; split. eapply pred1_refl_gen; auto.
    destruct option_map as [[o|]|]; auto.
    now rewrite !subst_ids in X1.
  Qed.

  Lemma pred1_ctx_pred1_inv Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u ->
    assumption_context Δ ->
    assumption_context Δ' ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u.
  Proof.
    intros Hlen X H H' X0.
    assert(lenΔ : #|Δ| = #|Δ'|). 
    { eapply pred1_pred1_ctx in X. eapply All2_fold_length in X.
      rewrite !app_context_length in X. lia. }
    pose proof (strong_substitutivity _ wfΣ _ _ (Γ ,,, Δ) (Γ' ,,, Δ) _ _ ids ids X).
    forward X1.
    { red. intros. simpl.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0. lia. rewrite nth_error_app_ge. lia.
      rewrite H0. simpl. rewrite e. reflexivity. }
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0 |- *; try lia.
      eapply All2_fold_app_inv in X0 as [_ X0] => //.
      pose proof (All2_fold_length X0).
      rewrite nth_error_app_ge. lia. now rewrite lenΔ H0 /= e. }
    forward X1.
    red. intros x; split. eapply pred1_refl_gen; auto.
    destruct option_map as [[o|]|]; auto.
    now rewrite !subst_ids in X1.
  Qed.

  Ltac noconf H := repeat (DepElim.noconf H; simpl NoConfusion in * ).

  Hint Extern 1 (eq_binder_annot _ _) => reflexivity : pcuic.
  Hint Resolve pred1_refl_gen : pcuic.
  Hint Extern 4 (All_decls _ _ _) => constructor : pcuic.
  Hint Extern 4 (All2_fold _ _ _) => constructor : pcuic.
  Hint Unfold on_decls_over : pcuic.

  Lemma OnOne2_local_env_pred1_ctx_over Γ Δ Δ' :
     OnOne2_local_env (on_one_decl (fun Δ M N => pred1 Σ (Γ ,,, Δ) (Γ ,,, Δ) M N)) Δ Δ' ->
     pred1_ctx_over Σ Γ Γ Δ Δ'.
  Proof.
    induction 1.
    1-2:constructor; destruct p; subst; intuition eauto.
    - eapply pred1_pred1_ctx in p. pcuic.
    - now constructor.
    - eapply pred1_pred1_ctx in a0. pcuic.
    - eapply pred1_pred1_ctx in a. pcuic.
    - constructor; unfold on_decls_over; simpl; subst; intuition auto.
      eapply pred1_refl.
    - constructor; unfold on_decls_over; simpl; subst; intuition auto.
      eapply pred1_refl.
    - eapply (All2_fold_app _ _ [d] _ [_]); pcuic.
      destruct d as [na [b|] ty]; constructor; pcuic. 
      constructor; unfold on_decls_over; simpl; subst; auto; intuition pcuic.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic.
      unfold on_decls_over; simpl; subst; intuition pcuic.
      constructor.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic.
  Qed.


  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Σ Γ Γ M N.
  Proof with pcuic.
    induction 1 using red1_ind_all; intros; pcuic.
    - constructor; pcuic.
      eapply OnOne2_All2...
    - constructor; pcuic.
      red. simpl. now eapply OnOne2_local_env_pred1_ctx_over in X.
      eapply pred1_refl_gen.
      eapply OnOne2_local_env_pred1_ctx_over in X.
      eapply All2_fold_app; pcuic.
    - constructor; pcuic.
      eapply OnOne2_All2...
      simpl. intros x y [[[? ?] ?]|?]; unfold on_Trel; intuition pcuic; rewrite -?e; auto.
      eapply pred1_ctx_over_refl.
      now eapply OnOne2_local_env_pred1_ctx_over in a.
      eapply OnOne2_local_env_pred1_ctx_over in a. rewrite b; pcuic.
      eapply pred1_refl_gen; eauto.
      now apply All2_fold_app; pcuic.
    - constructor; pcuic.
      eapply OnOne2_All2...
    - constructor; pcuic.
      + apply All2_All2_fold_fix_context.
        now intros; eapply weakening_pred1_pred1.
        eapply OnOne2_All2...
        intros.
        simpl in *. intuition auto. now noconf b.
      + eapply OnOne2_All2; pcuic; simpl;
        unfold on_Trel; simpl; intros; intuition auto.
        noconf b; noconf H. rewrite H0. pcuic.
        apply pred1_refl_gen.
        eapply All2_fold_app; pcuic.
        apply All2_All2_fold_fix_context.
        now intros; eapply weakening_pred1_pred1.
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto.
        congruence. congruence.

        pcuic.
        apply pred1_refl_gen; pcuic.
        eapply All2_fold_app; pcuic.
        apply All2_All2_fold_fix_context.
        now intros; eapply weakening_pred1_pred1.
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. congruence.

    - constructor; pcuic.
      apply All2_All2_fold_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H0; pcuic. congruence.
      + eapply OnOne2_All2...
        intros.
        * intros. unfold on_Trel.
          simpl in *. intuition auto. noconf b. noconf H. rewrite H0. pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b. noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          now rewrite -H. congruence.
        * intros. unfold on_Trel.
          simpl in *. intuition pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b; noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          rewrite -H. pcuic.

    - constructor; pcuic.
      apply All2_All2_fold_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H; pcuic.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H.
          rewrite -H0; pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_fold_over_app. pcuic.
          apply All2_All2_fold_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_fold_over_app. pcuic.
          apply All2_All2_fold_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence.

    - constructor; pcuic.
      apply All2_All2_fold_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        unfold on_Trel.
        simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
        congruence.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          { clear -X.
            unfold fix_context, mapi. generalize 0 at 2 4.
            induction X; intros. intuition auto. simpl. noconf b; noconf H. congruence.
            simpl; now rewrite IHX. }
          now rewrite -H. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_fold_over_app. pcuic.
          apply All2_All2_fold_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic.
          noconf b; noconf H; rewrite H0; pcuic. congruence.
  Qed.

End RedPred.

Section PredRed.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  (* Lemma red_red_decls Γ Γ' Δ Δ' :
    All2_fold_over (fun (Γ _ : context) (t t0 : term) => red Σ Γ t t0) Γ Γ' Δ Δ' ->
    All2_fold (fun Δ Δ' : context => red_decls Σ (Γ,,, Δ) (Γ,,, Δ')) Δ Δ'.
  Proof.
    induction 1; constructor; auto;
    unfold on_decls, on_decls_over in *.
    constructor.
    simpl. *)

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ M N.
  Proof.
    revert Γ Γ'. eapply (@pred1_ind_all_ctx Σ _
      (fun Γ Γ' => All2_fold (on_decls (fun Γ Γ' M N => red Σ Γ M N)) Γ Γ')%type);
      (* (fun Γ Γ' Δ Δ' => All2_fold_over (on_decls (fun Γ Γ' M N => pred1 Σ Γ Γ' M N -> red Σ Γ M N)) Γ Γ')%type); *)
      intros; try reflexivity; pcuic.
      
    - (* Beta *)
      apply red_trans with (tApp (tLambda na t0 b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pcuic.
      apply red_trans with (tApp (tLambda na t0 b1) a1).
      eapply (@red_app Σ); auto with pcuic.
      apply red1_red. constructor.

    - (* Zeta *)
      eapply red_trans with (tLetIn na d0 t0 b1).
      eapply red_letin; eauto with pcuic.
      eapply red_trans with (tLetIn na d1 t1 b1).
      eapply red_letin; eauto with pcuic.
      eapply red1_red; constructor.

    - (* Rel in context *)
      eapply nth_error_pred1_ctx in X0; eauto.
      destruct X0 as [body' [Hnth Hpred]].
      eapply red_trans with (lift0 (S i) body').
      eapply red1_red; constructor; auto.
      eapply nth_error_pred1_ctx_all_defs in H; eauto.
      rewrite -(firstn_skipn (S i) Γ).
      eapply weakening_red_0 => //.
      rewrite firstn_length_le //.
      destruct nth_error eqn:Heq.
      eapply nth_error_Some_length in Heq. lia. noconf Hnth.

    - (* Iota *)
      transitivity (tCase ci p0 (mkApps (tConstruct ci.(ci_ind) c u) args1) brs1).
      etransitivity.
      { eapply red_case_c. eapply red_mkApps. auto. solve_all. }
      etransitivity.
      { eapply red_case_brs. red. solve_all;
        unfold on_Trel in *; intuition auto.
        eapply red_ctx_rel_red_context_rel; eauto.
        red. 
        eapply PCUICEnvironment.All2_fold_impl; tea.
        intros. depelim X2; constructor; auto. }
      reflexivity. 
      eapply red1_red. constructor => //.

    - move: H H0.
      move => unf isc.
      transitivity (mkApps (tFix mfix1 idx) args1).
      eapply red_mkApps. eapply red_fix_congr. red in X3. solve_all. eapply a.
      solve_all.
      eapply red_step. econstructor; eauto. 2:eauto.
      eapply (is_constructor_pred1 Σ). eapply (All2_impl X4); intuition eauto. auto.

    - transitivity (tCase ci p1 (mkApps (tCoFix mfix1 idx) args1) brs1).
      destruct p1; unfold on_Trel in *; cbn in *.
      subst puinst.
      eapply red_case; eauto.
      * eapply red_ctx_rel_red_context_rel => //.
        red.
        eapply PCUICEnvironment.All2_fold_impl; tea => /=.
        intros ? ? ? ? []; constructor; auto.
      * solve_all.
      * red. solve_all.
        eapply red_mkApps; [|solve_all].
        etransitivity. eapply red_cofix_congr. red in X3; solve_all.
        eapply a. reflexivity.
      * red. solve_all.
        eapply red_ctx_rel_red_context_rel => //.
        red. eapply PCUICEnvironment.All2_fold_impl; tea => /=.
        intros ???? []; constructor; auto.
      * constructor. econstructor; eauto.

    - transitivity (tProj p (mkApps (tCoFix mfix1 idx) args1)).
      eapply red_proj_c; eauto.
      eapply red_mkApps; [|solve_all].
      eapply red_cofix_congr. red in X3; solve_all. eapply a.
      eapply red_step. econstructor; eauto. eauto.

    - transitivity (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args1)).
      eapply red_proj_c; eauto.
      eapply red_mkApps; [|solve_all]. auto.
      eapply red1_red. econstructor; eauto.

    - now eapply red_abs_alt.
    - now eapply red_app.
    - now eapply red_letin_alt => //.
    - unfold on_Trel in *; destruct p1; cbn in *. subst puinst.
      eapply red_case => //.
      * eapply red_ctx_rel_red_context_rel => //.
        eapply PCUICEnvironment.All2_fold_impl; tea => //.
        now intros ???? []; constructor.
      * solve_all.
      * red. solve_all.
        eapply red_ctx_rel_red_context_rel => //.
        eapply PCUICEnvironment.All2_fold_impl; tea => //.
        now intros ???? []; constructor.

    - now eapply red_proj_c.
    - eapply red_fix_congr. red in X3; solve_all. eapply a.
    - eapply red_cofix_congr. red in X3; solve_all. eapply a.
    - eapply red_prod; auto.
    - eapply red_evar; auto. solve_all.
  Qed.

  Lemma All2_fold_mix P Q x y : All2_fold P x y -> All2_fold Q x y ->
    All2_fold (fun Γ Γ' t T => 
      (P Γ Γ' t T) * (Q Γ Γ' t T))%type x y.
  Proof.
    intros HP HQ; induction HP; depelim HQ; try (simpl in H; noconf H); 
      try (simpl in H0; noconf H0); constructor; intuition eauto.
  Qed.

  Lemma pred1_red_r_gen Γ Γ' Δ Δ' : forall M N,
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') M N -> 
    #|Γ| = #|Γ'| ->
    pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ' ,,, Δ) (Γ' ,,, Δ') M N.
  Proof.
    intros M N.
    generalize_eq Γ0 (Γ ,,, Δ); intro e.
    generalize_eq Γ'0 (Γ' ,,, Δ'); intros e' p.
    rewrite e'.
    revert Γ Γ' Δ Δ' e e'.
    revert Γ0 Γ'0 M N p.
    refine (@pred1_ind_all_ctx Σ _ 
      (fun Γ0 Γ'0 =>
        forall Γ Γ' Δ Δ' : context,
        Γ0 = Γ ,,, Δ -> Γ'0 = Γ' ,,, Δ' ->
        #|Γ| = #|Γ'| ->
        pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ'))
      (fun Γ0 Γ'0 ctx ctx' => 
        forall Γ Γ' Δ Δ' : context,
        Γ0 = Γ ,,, Δ -> Γ'0 = Γ' ,,, Δ' ->
        #|Γ| = #|Γ'| ->
        pred1_ctx_over Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ctx ctx')
       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      intros; subst; try solve [econstructor; eauto].

    - eapply All2_fold_app => //. eapply pred1_ctx_refl.
      eapply All2_fold_app_inv in X0 as [] => //. 
      eapply (All2_fold_impl_ind a0). clear a0; intros; eauto.
      red. eapply X1; eauto. eapply All2_fold_app => //.
      apply pred1_ctx_refl.
    - eapply (All2_fold_impl_ind X3); unfold on_decls_over. intros.
      specialize (X5 Γ0 Γ'0 (Δ0 ,,, par) (Δ'0 ,,, par')
        ltac:(now rewrite app_context_assoc) ltac:(now rewrite app_context_assoc)).
      rewrite !app_context_assoc in X5. apply X5 => //.
      eapply All2_fold_app. eapply X1. 2:eauto. all:eauto.

    - econstructor; eauto. 
      specialize (X0 Γ0 Γ'0 (Δ ,, vass na t0) (Δ' ,, vass na t1) eq_refl).
      apply X0 => //. simpl. constructor; auto. now constructor.

    - econstructor; eauto. 
      eapply (X4 Γ0 Γ'0 (Δ ,, vdef na d0 t0) (Δ' ,, vdef na d1 t1) eq_refl eq_refl H).
      simpl; constructor; auto. constructor; eauto.

    - econstructor; eauto.
      * solve_all.
      * unfold on_Trel in *. solve_all.
        rewrite - !app_context_assoc.
        eapply b1; rewrite ?app_context_assoc; eauto.
        eapply All2_fold_app; eauto.

    - econstructor; eauto. red. red in X3. 
      unfold on_Trel in *; solve_all.
      rewrite - !app_context_assoc.
      eapply b; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //.
      eapply X2; eauto.
      solve_all.
      
    - econstructor; eauto; unfold on_Trel in *; solve_all.
      red in X3 |- *. unfold on_Trel in *; solve_all.
      rewrite - !app_context_assoc; eapply b; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply X2; eauto.
      rewrite - !app_context_assoc; eapply X9; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply X7; eauto.
      rewrite - !app_context_assoc; eapply b1; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply b0; eauto.
      
    - econstructor; eauto.
      red in X3 |- *. unfold on_Trel in *; solve_all.
      rewrite - !app_context_assoc; eapply b; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply X2; eauto.
      solve_all.

    - econstructor; eauto.
      solve_all.

    - econstructor; eauto.
      eapply (X2 _ _ (Δ ,, vass na M) (Δ' ,, vass na M')); eauto; try reflexivity => //.
      simpl; constructor; eauto. now constructor.
    
    - econstructor; eauto.
      eapply (X4 _ _ (Δ ,, vdef na d0 t0) (Δ' ,, vdef na d1 t1)); eauto; try reflexivity.
      simpl; constructor; eauto. now constructor.

    - unfold on_Trel in *; econstructor; eauto; unfold on_Trel; solve_all.
      rewrite - !app_context_assoc; eapply X5; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //; eapply X3; eauto.
      rewrite - !app_context_assoc; eapply b1; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //; eapply b0; eauto.

    - econstructor; eauto.
      red in X3 |- *. unfold on_Trel in *; solve_all.
      rewrite - !app_context_assoc; eapply b; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply X2; eauto.

    - econstructor; eauto.
      red in X3 |- *. unfold on_Trel in *; solve_all.
      rewrite - !app_context_assoc; eapply b; rewrite ?app_context_assoc; eauto.
      eapply All2_fold_app => //. eapply X2; eauto.

    - econstructor; eauto.
      eapply (X2 _ _ (Δ ,, vass na M0) (Δ' ,, vass na M1)); try reflexivity; auto.
      simpl; constructor; eauto. now constructor.

    - econstructor; eauto. solve_all.
  Qed.

  Lemma pred1_pred1_r Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> 
    pred1 Σ Γ' Γ' M N.
  Proof.
    intros M N pred.
    apply (pred1_red_r_gen _ _ [] [] M N pred).
    eapply pred1_pred1_ctx in pred. apply (length_of pred).
    simpl. eapply pred1_ctx_refl.
  Qed.

  Lemma pred1_red_r Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ' M N.
  Proof.
    intros M N p.
    eapply pred1_pred1_r in p.
    now eapply pred1_red in p.
  Qed.

End PredRed.



Generalizable Variables A B R S.

Section AbstractConfluence.
  Section Definitions.

    Context {A : Type}.
    Definition joinable (R : A -> A -> Type) (x y : A) := ∑ z, R x z * R y z.
    Definition diamond (R : A -> A -> Type) := forall x y z, R x y -> R x z -> joinable R y z.
    Definition confluent (R : relation A) := diamond (clos_refl_trans R).

  End Definitions.

  Global Instance joinable_proper A :
    Proper (relation_equivalence ==> relation_equivalence)%signature (@joinable A).
  Proof.
    reduce_goal. split; unfold joinable; intros.
    destruct X0. exists x1. intuition eauto. setoid_rewrite (X x0 x1) in a. auto.
    specialize (X y0 x1). now apply X in b.
    red in X.
    destruct X0 as [z [rl rr]].
    apply X in rl. apply X in rr.
    exists z; split; auto.
  Qed.

  Global Instance diamond_proper A : Proper (relation_equivalence ==> iffT)%signature (@diamond A).
  Proof.
    reduce_goal.
    rewrite /diamond.
    split; intros.
    setoid_rewrite <- (X x0 y0) in X1.
    setoid_rewrite <- (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
    setoid_rewrite (X x0 y0) in X1.
    setoid_rewrite (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
  Qed.

  Lemma clos_rt_proper A : Proper (relation_equivalence ==> relation_equivalence) (@clos_refl_trans A).
  Proof.
    reduce_goal. split; intros.
    induction X0; try apply X in r; try solve [econstructor; eauto].
    induction X0; try apply X in r; try solve [econstructor; eauto].
  Qed.

  Global Instance confluent_proper A : Proper (relation_equivalence ==> iffT)%signature (@confluent A).
  Proof.
    reduce_goal.
    split; rewrite /confluent; auto.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
  Qed.

  Lemma sandwich {A} (R S : A -> A -> Type) :
    inclusion R S -> inclusion S (clos_refl_trans R) ->
    (iffT (confluent S) (confluent R)).
  Proof.
    intros inclR inclS.
    apply clos_rt_monotone in inclR.
    apply clos_rt_monotone in inclS.
    assert (inclusion (clos_refl_trans S) (clos_refl_trans R)).
    etransitivity; eauto.
    apply clos_rt_idempotent.
    rewrite /confluent.
    apply diamond_proper.
    now apply relation_equivalence_inclusion.
  Qed.

  Section Diamond.
    Context {A} {R S : relation A}.
    Context (sc : diamond R).

    Lemma diamond_t1n_t_confluent t u v :
      trans_clos_1n R t u ->
      R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof.
      move => tu.
      revert v.
      induction tu.
      intros.
      - destruct (sc _ _ _ r X); auto.
        eexists; split; constructor; intuition eauto.
      - move => v xv.
        destruct (sc _ _ _ r xv); auto.
        destruct p. specialize (IHtu _ r0).
        destruct IHtu as [nf [redl redr]].
        exists nf. split; auto.
        econstructor 2; eauto.
    Qed.

    Lemma diamond_t1n_t1n_confluent {t u v} :
      trans_clos_1n R t u ->
      trans_clos_1n R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof.
      move => tu tv.
      induction tv in u, tu |- *.
      - eapply diamond_t1n_t_confluent; eauto.
      - eapply diamond_t1n_t_confluent in r; eauto.
        destruct r as [nf [redl redr]].
        specialize (IHtv _ redr) as [nf' [redl' redr']].
        exists nf'; intuition auto.
        apply trans_clos_t1n_iff.
        econstructor 2; eapply trans_clos_t1n_iff; eauto.
    Qed.

    Lemma diamond_t_t_confluent {t u v} :
      trans_clos R t u ->
      trans_clos R t v ->
      ∑ t', trans_clos R u t' * trans_clos R v t'.
    Proof.
      move => tu tv.
      apply trans_clos_t1n_iff in tu;
        apply trans_clos_t1n_iff in tv.
      destruct (diamond_t1n_t1n_confluent tu tv).
      exists x. split; apply trans_clos_t1n_iff; intuition auto.
    Qed.

    Lemma commutes_diamonds_diamond :
      commutes R S -> diamond S -> diamond (relation_disjunction R S).
    Proof.
      intros HRS HS x y z xy xz.
      destruct xy, xz.
      destruct (sc _ _ _ r r0).
      eexists; intuition auto. now left. now left.
      destruct (HRS _ _ _ r s).
      exists x0.
      intuition auto. right; auto. left; auto.
      destruct (HRS _ _ _ r s).
      eexists; intuition auto. left; eauto. right; auto.
      destruct (HS _ _ _ s s0). intuition auto.
      eexists. split; right; eauto.
    Qed.

    Lemma commutes_disj_joinable :
      commutes R S -> confluent R -> confluent S ->
      forall x y z, relation_disjunction R S x y ->
                    relation_disjunction R S x z ->
                    joinable (clos_refl_trans (relation_disjunction R S)) y z.
    Proof.
      intros.
      destruct X2. destruct X3.
      destruct (X0 _ _ _ (rt_step r) (rt_step r0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_left.
      now apply clos_rt_disjunction_left.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_right, rt_step.
      now apply clos_rt_disjunction_left, rt_step.
      destruct X3.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_left, rt_step.
      now apply clos_rt_disjunction_right, rt_step.
      destruct (X1 _ _ _ (rt_step s) (rt_step s0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_right.
      now apply clos_rt_disjunction_right.
    Qed.

  End Diamond.

  Theorem diamond_confluent `{Hrefl : Reflexive A R} : diamond R -> confluent R.
  Proof.
    move=> Hdia x y z H H'.
    apply clos_rt_t_incl in H.
    apply clos_rt_t_incl in H'.
    pose proof (clos_t_rt_equiv (R:=R)).
    apply (joinable_proper _ _ _ X).
    apply (diamond_t_t_confluent Hdia H H').
  Qed.

  Corollary confluent_union {A} {R S : relation A} :
    Reflexive R ->
    commutes R S -> diamond R -> diamond S -> confluent (relation_disjunction R S).
  Proof.
    intros HRR HRS Hcom HR HS. apply diamond_confluent.
    now apply commutes_diamonds_diamond.
  Qed.

End AbstractConfluence.

Unset Universe Minimization ToSet.



Lemma red_pred {cf:checker_flags} {Σ : global_env} {Γ t u} : wf Σ -> clos_refl_trans (red1 Σ Γ) t u -> clos_refl_trans (pred1 Σ Γ Γ) t u.
Proof.
  intros wfΣ. eapply clos_rt_monotone.
  intros x y H.
  eapply red1_pred1; auto.
Qed.

Section RedConfluence.
  Context {cf : checker_flags}.
  Context {Σ : global_env} (wfΣ : wf Σ).

  Instance pred1_refl Γ : Reflexive (pred1 Σ Γ Γ).
  Proof. red; apply pred1_refl. Qed.

  Definition pred1_rel : (context * term) -> (context * term) -> Type :=
    fun t u => pred1 Σ (fst t) (fst u) (snd t) (snd u).

  Instance pred1_rel_refl : Reflexive pred1_rel.
  Proof. red. intros [ctx x]. red. simpl. apply pred1_refl. Qed.

  Lemma red1_weak_confluence Γ t u v :
    red1 Σ Γ t u -> red1 Σ Γ t v ->
    ∑ t', red Σ Γ u t' * red Σ Γ v t'.
  Proof.
    move/(red1_pred1 wfΣ) => tu.
    move/(red1_pred1 wfΣ) => tv.
    eapply pred1_diamond in tu; eauto.
    destruct tu as [redl redr].
    eapply pred1_red in redl; auto.
    eapply pred1_red in redr; auto.
    eexists _; split; eauto.
  Qed.

  Lemma diamond_pred1_rel : diamond pred1_rel.
  Proof.
    move=> t u v tu tv.
    destruct (pred1_diamond wfΣ tu tv).
    eexists (rho_ctx Σ (fst t), rho Σ (rho_ctx Σ (fst t)) (snd t)).
    split; auto.
  Qed.

  Lemma pred1_rel_confluent : confluent pred1_rel.
  Proof.
    eapply diamond_confluent. apply diamond_pred1_rel.
  Qed.

  Lemma red_trans_clos_pred1 Γ t u :
    red Σ Γ t u ->
    trans_clos pred1_rel (Γ, t) (Γ, u).
  Proof.
    induction 1.
    constructor. now eapply red1_pred1 in r.
    constructor. pcuic.
    econstructor 2; eauto.
  Qed.

  Inductive clos_refl_trans_ctx_decl (R : relation context_decl) (x : context_decl) : context_decl -> Type :=
    rt_ctx_decl_step : forall y, R x y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_refl y : eq_binder_annot x.(decl_name) y.(decl_name) -> 
    decl_body x = decl_body y -> decl_type x = decl_type y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_trans : forall y z, clos_refl_trans_ctx_decl R x y -> clos_refl_trans_ctx_decl R y z ->
                               clos_refl_trans_ctx_decl R x z.

  Definition eq_context_upto_names := eq_context_gen eq eq.

  Global Instance eq_context_upto_names_refl : Reflexive eq_context_upto_names := _.
  Global Instance eq_context_upto_names_sym : Symmetric eq_context_upto_names := _.
  Global Instance eq_context_upto_names_trans : Transitive eq_context_upto_names := _.

  Inductive clos_refl_trans_ctx (R : relation context) (x : context) : context -> Type :=
  | rt_ctx_step : forall y, R x y -> clos_refl_trans_ctx R x y
  | rt_ctx_refl y : eq_context_upto_names x y -> clos_refl_trans_ctx R x y
  | rt_ctx_trans : forall y z, clos_refl_trans_ctx R x y -> clos_refl_trans_ctx R y z -> clos_refl_trans_ctx R x z.

  Global Instance clos_refl_trans_ctx_refl R :
    Reflexive (clos_refl_trans_ctx R).
  Proof. intros HR. constructor 2. reflexivity. Qed.

  Global Instance clos_refl_trans_ctx_trans R : Transitive (clos_refl_trans_ctx R).
  Proof.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition red1_rel : relation (context * term) :=
    relation_disjunction (fun '(Γ, t) '(Δ, u) => (red1 Σ Γ t u * (Γ = Δ)))%type
                         (fun '(Γ, t) '(Δ, u) => (red1_ctx Σ Γ Δ * (t = u)))%type.

  Definition red_ctx : relation context :=
    All2_fold (on_decls (fun Γ Δ => red Σ Γ)).

  Lemma red1_ctx_pred1_ctx Γ Γ' : red1_ctx Σ Γ Γ' -> pred1_ctx Σ Γ Γ'.
  Proof.
    intros. induction X; try constructor; auto. pcuic.
    cbn in p. destruct p as [-> p]. constructor.
    now eapply red1_pred1. pcuic. 
    destruct p as [-> p]; constructor; auto;
    destruct p as [[redb ->]|[redt ->]]; try reflexivity; pcuic; now eapply red1_pred1.
    - eapply All_decls_refl. intro. now eapply pred1_refl_gen.
  Qed.

  Lemma pred1_ctx_red_ctx Γ Γ' : pred1_ctx Σ Γ Γ' -> red_ctx Γ Γ'.
  Proof.
    intros. induction X; try constructor; pcuic.
    eapply All_decls_impl; tea.
    now eapply pred1_red.
  Qed.

  Definition red_rel_ctx :=
    fun '(Γ, t) '(Δ, u) =>
      (red Σ Γ t u * red_ctx Γ Δ)%type.

  Lemma pred1_red' Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red_rel_ctx (Γ, M) (Γ', N).
  Proof.
    intros * Hred.
    split. apply (pred1_red wfΣ _ _ _ _ Hred).
    eapply pred1_pred1_ctx in Hred.
    now eapply pred1_ctx_red_ctx.
  Qed.

  Lemma clos_rt_OnOne2_local_env_incl R :
    inclusion (OnOne2_local_env (on_one_decl (fun Δ => clos_refl_trans (R Δ))))
              (clos_refl_trans (OnOne2_local_env (on_one_decl R))).
  Proof.
    intros x y H.
    induction H; firstorder; try subst na'.
    - induction b. repeat constructor. pcuicfo.
      constructor 2.
      econstructor 3 with (Γ ,, vass na y); auto.
    - subst.
      induction a0. repeat constructor. pcuicfo.
      constructor 2.
      econstructor 3 with (Γ ,, vdef na b' y); auto.
    - subst t'.
      induction a0. constructor. constructor. red. simpl. pcuicfo.
      constructor 2.
      econstructor 3 with (Γ ,, vdef na y t); auto.
    - clear H. induction IHOnOne2_local_env. constructor. now constructor 3.
      constructor 2.
      eapply transitivity. eauto. auto.
  Qed.

  Lemma clos_rt_OnOne2_local_env_ctx_incl R :
    inclusion (clos_refl_trans (OnOne2_local_env (on_one_decl R)))
              (clos_refl_trans_ctx (OnOne2_local_env (on_one_decl R))).
  Proof.
    intros x y H.
    induction H; firstorder; try solve[econstructor; eauto].
  Qed.
  
  Lemma red_ctx_clos_rt_red1_ctx : inclusion red_ctx (clos_refl_trans_ctx (red1_ctx Σ)).
  Proof.
    intros x y H.
    induction H; try firstorder.
    destruct p.
    - transitivity (Γ ,, vass na t').
      eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl. constructor.
      cbn. split; auto.
      clear r H.
      induction IHAll2_fold; try solve[repeat constructor; auto].
      etransitivity; eauto.
    - transitivity (Γ ,, vdef na b t').
      * eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl. constructor 2.
        cbn. split; auto.
      * transitivity (Γ ,, vdef na b' t').
        + eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl.
          constructor 2. cbn. split; auto.
        + clear -IHAll2_fold.
          induction IHAll2_fold; try solve[repeat constructor; auto].
          etransitivity; eauto.
  Qed.

  Inductive clos_refl_trans_ctx_t (R : relation (context * term)) (x : context * term) : context * term -> Type :=
  | rt_ctx_t_step : forall y, R x y -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_refl y : eq_context_upto_names (fst x) (fst y) -> snd x = snd y -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_trans : forall y z, clos_refl_trans_ctx_t R x y -> clos_refl_trans_ctx_t R y z -> clos_refl_trans_ctx_t R x z.

  Global Instance clos_refl_trans_ctx_t_refl R :
    Reflexive (clos_refl_trans_ctx_t R).
  Proof. intros HR. constructor 2. reflexivity. auto. Qed.

  Global Instance clos_refl_trans_ctx_t_trans R : Transitive (clos_refl_trans_ctx_t R).
  Proof.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition clos_rt_ctx_t_monotone (R S : relation _) :
    inclusion R S -> inclusion (clos_refl_trans_ctx_t R) (clos_refl_trans_ctx_t S).
  Proof.
    move => incls x y.
    induction 1; solve [econstructor; eauto].
  Qed.

  Lemma clos_rt_ctx_t_disjunction_left (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t R)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof.
    apply clos_rt_ctx_t_monotone.
    intros x y H; left; exact H.
  Qed.

  Lemma clos_rt_ctx_t_disjunction_right (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t S)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof.
    apply clos_rt_ctx_t_monotone.
    intros x y H; right; exact H.
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_l (R : relation _) (S : relation _) :
    (forall x y b, R x y -> S (x, b) (y, b)) ->
    forall x y b,
      clos_refl_trans_ctx R x y ->
      clos_refl_trans_ctx_t S (x, b) (y, b).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_r (R : relation term) (S : relation (context * term)) a :
    (forall x y, R x y -> S (a, x) (a, y)) ->
    forall x y,
      clos_refl_trans R x y ->
      clos_refl_trans_ctx_t S (a, x) (a, y).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
    constructor 2. simpl. apply reflexivity. reflexivity.
  Qed.

  Lemma clos_rt_red1_rel_ctx_rt_ctx_red1_rel : inclusion red_rel_ctx (clos_refl_trans_ctx_t red1_rel).
  Proof.
    move=> [Γ t] [Δ u] [redt redctx].
    eapply clos_rt_rt1n_iff in redt.
    induction redt.
    induction redctx; try solve [constructor; eauto].
    - constructor 2; simpl; apply reflexivity.
    - etransitivity.
      * eapply clos_rt_ctx_t_disjunction_right.
        instantiate (1:= (Γ',, d', x)).
        eapply clos_refl_trans_ctx_t_prod_l. intros. split; eauto.
        transitivity (Γ ,, d).
        constructor 2. repeat constructor. simpl. auto. reflexivity.
        reflexivity.
        apply red_ctx_clos_rt_red1_ctx. constructor; auto.
      * clear p. eapply clos_rt_ctx_t_disjunction_right.
        constructor 2; simpl; reflexivity.
    - transitivity (Γ, y).
      * eapply clos_rt_ctx_t_disjunction_left.
        eapply clos_refl_trans_ctx_t_prod_r. intros. split; eauto.
        constructor. apply r.
      * apply IHredt.
  Qed.

  Definition pred1_rel_alpha : (context * term) -> (context * term) -> Type :=
    fun t u => (pred1 Σ (fst t) (fst u) (snd t) (snd u) + 
      (eq_context_upto_names (fst t) (fst u) × snd t = snd u))%type.

  Definition red1_rel_alpha : relation (context * term) :=
    relation_disjunction (fun '(Γ, t) '(Δ, u) => (red1 Σ Γ t u * (Γ = Δ)))%type
     (relation_disjunction
        (fun '(Γ, t) '(Δ, u) => ((red1_ctx Σ Γ Δ * (t = u))))
        (fun '(Γ, t) '(Δ, u) => ((eq_context_upto_names Γ Δ * (t = u)))))%type.

  Lemma clos_rt_red1_rel_rt_ctx : inclusion (clos_refl_trans red1_rel) (clos_refl_trans_ctx_t red1_rel).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y. constructor. auto.
    - constructor 2; apply reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_pred1_rel_alpha : inclusion red1_rel_alpha pred1_rel_alpha.
  Proof.
    intros [ctx t] [ctx' t'].
    rewrite /red1_rel_alpha /pred1_rel_alpha /=.
    intros [[l <-]|[[r <-]|[r <-]]].
    - left; now eapply red1_pred1.
    - left. eapply pred1_refl_gen. now apply red1_ctx_pred1_ctx.
    - right; split; auto.
  Qed.

  Lemma pred1_rel_alpha_red1_rel_alpha : inclusion pred1_rel_alpha (clos_refl_trans red1_rel_alpha).
  Proof.
    intros x y pred. red in pred.
    destruct pred as [pred|[pctx eq]].
    - eapply pred1_red' in pred; auto.
      destruct pred.
      destruct x, y. simpl in *.
      transitivity (c, t0).
      + eapply clos_rt_disjunction_left.
        eapply clos_refl_trans_prod_r; tea. intros. split; eauto.
      + eapply clos_rt_disjunction_right.
        eapply (clos_refl_trans_prod_l (fun x y => red1_ctx Σ x y + eq_context_upto_names x y))%type.
        intros. red. destruct X; intuition auto.
        clear r.
        apply red_ctx_clos_rt_red1_ctx in r0.
        induction r0. constructor; auto.
        constructor. auto.
        now transitivity y.
    - constructor. right. right. destruct x, y; cbn in *; auto.
  Qed.

  Lemma pred1_upto_names_gen {Γ Γ' Δ Δ' t u} : 
    pred1 Σ Γ Δ t u ->
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    pred1_ctx Σ Γ' Δ' ->
    pred1 Σ Γ' Δ' t u.
  Proof.
    intros pr eqctx eqctx' predctx.
    epose proof (strong_substitutivity Σ wfΣ Γ Δ Γ' Δ' t u ids ids pr).
    forward X.
    { intros x d hnth. destruct d as [na [b|] ty] => /= //.
      exists x, b. split; auto.
      eapply All2_fold_nth in hnth as [d' [hnth' [eqctx'' eqd]]]. 2:exact eqctx.
      sigma. split; auto.
      simpl in *. depelim eqd. subst.
      now rewrite hnth' /=. }
    forward X.
    { intros x d hnth. destruct d as [na [b|] ty] => /= //.
      exists x, b. split; auto.
      eapply All2_fold_nth in hnth as [d' [hnth' [eqctx'' eqd]]]. 2:exact eqctx'.
      sigma. split; auto.
      simpl in *. depelim eqd. subst.
      now rewrite hnth' /=. }
    forward X. {
      intros x; split. now constructor.
      destruct option_map => //. destruct o => //.
    }
    now rewrite !subst_ids in X.
  Qed.

  Lemma pred1_ctx_upto_names {Γ Γ' Δ} : 
    pred1_ctx Σ Γ Δ ->
    eq_context_upto_names Γ Γ' ->
    ∑ Δ', pred1_ctx Σ Γ' Δ' × eq_context_upto_names Δ Δ'.
  Proof.
    intros pr eqctx.
    induction eqctx in Δ, pr |- *; depelim pr.
    - exists []; split; auto; pcuic.
    - depelim a.
      * depelim p0. subst.
        destruct (IHeqctx _ pr) as [Δ' [pred' eq']]. 
        exists (vass na' t' :: Δ').
        split. constructor. apply pred'. constructor.
        eapply pred1_upto_names_gen; tea.
        constructor => //. constructor => //.
      * destruct (IHeqctx _ pr) as [Δ' [pred' eq']].
        depelim p1; subst.
        exists (vdef na' b' t' :: Δ').
        split. constructor. apply pred'. constructor.
        eapply pred1_upto_names_gen; tea.
        eapply pred1_upto_names_gen; tea.
        constructor => //. constructor => //.
  Qed.

  Lemma pred1_upto_names {Γ Γ' Δ t u} : 
    pred1 Σ Γ Δ t u ->
    eq_context_upto_names Γ Γ' ->
    ∑ Δ', pred1 Σ Γ' Δ' t u × eq_context_upto_names Δ Δ'.
  Proof.
    intros pr eqctx.
    pose proof (pred1_pred1_ctx _ pr).
    destruct (pred1_ctx_upto_names X eqctx) as [Δ' [pred' eq']].
    exists Δ'; split; auto.
    now eapply pred1_upto_names_gen.
  Qed.

  Lemma diamond_pred1_rel_alpha : diamond pred1_rel_alpha.
  Proof.
    move=> t u v tu tv.
    destruct tu as [tu|[tu eq]], tv as [tv|[tv eq']].
    - destruct (pred1_diamond wfΣ tu tv).
      eexists (rho_ctx Σ (fst t), rho Σ (rho_ctx Σ (fst t)) (snd t)).
      split; left; auto.
    - destruct t as [ctxt t], u as [ctxu u], v as [ctxv v]; cbn in *; subst v.
      eapply pred1_upto_names in tu as [Δ' [pred eqctx]]; tea.
      exists (Δ', u). unfold pred1_rel_alpha; cbn.
      firstorder.
    - destruct t as [ctxt t], u as [ctxu u], v as [ctxv v]; cbn in *; subst u.
      eapply pred1_upto_names in tv as [Δ' [pred eqctx]]; tea.
      exists (Δ', v). unfold pred1_rel_alpha; cbn.
      firstorder.
    - destruct t as [ctxt t], u as [ctxu u], v as [ctxv v]; cbn in *; subst u v.
      exists (ctxt, t). unfold pred1_rel_alpha; cbn.
      split. right; split; auto. now symmetry.
      right. split; auto. now symmetry.
  Qed.

  Lemma pred1_rel_alpha_confluent : confluent pred1_rel_alpha.
  Proof.
    eapply diamond_confluent. apply diamond_pred1_rel_alpha.
  Qed.

  Lemma pred_rel_confluent : confluent red1_rel_alpha.
  Proof.
    notypeclasses refine (fst (sandwich _ _ _ _) _).
    3:eapply pred1_rel_alpha_confluent; eauto.
    - apply red1_rel_alpha_pred1_rel_alpha.
    - apply pred1_rel_alpha_red1_rel_alpha.
  Qed.

  Lemma clos_refl_trans_out Γ x y :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel (Γ, x) (Γ, y).
  Proof.
    induction 1. constructor. red. left. pcuicfo.
    constructor 2.
    econstructor 3; eauto.
  Qed.

  Lemma clos_red_rel_out x y :
    clos_refl_trans red1_rel x y ->
    clos_refl_trans pred1_rel x y.
  Proof.
    eapply clos_rt_monotone. clear x y.
    intros [Γ t] [Δ u] hred.
    destruct hred as [[ht eq]|[hctx eq]]. subst.
    red. simpl. now eapply red1_pred1.
    subst. red.
    simpl.
    eapply pred1_refl_gen. now eapply red1_ctx_pred1_ctx.
  Qed.

  Lemma red1_rel_alpha_red1_rel : inclusion (clos_refl_trans red1_rel_alpha) (clos_refl_trans_ctx_t red1_rel).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct p; subst.
      constructor 2. simpl. auto. reflexivity.
    - constructor 2; reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_red1_rel_inv : inclusion (clos_refl_trans_ctx_t red1_rel) (clos_refl_trans red1_rel_alpha).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct p. subst.
      constructor. firstorder.
    - destruct x, y. simpl in *.
      subst. constructor. firstorder.
    - econstructor 3; eauto.
  Qed.

  Lemma clos_red_rel_out_inv x y :
    clos_refl_trans pred1_rel x y ->
    clos_refl_trans red1_rel_alpha x y.
  Proof.
    induction 1.
    red in r.
    destruct x as [Γ t], y as [Δ u]; simpl in *.
    pose proof (pred1_pred1_ctx _ r).
    apply red1_rel_alpha_red1_rel_inv.
    transitivity (Γ, u).
    eapply clos_refl_trans_ctx_t_prod_r. intros. red. left. split; eauto.
    now apply pred1_red in r.
    eapply clos_refl_trans_ctx_t_prod_l. intros. red. right. split; eauto.
    now apply red_ctx_clos_rt_red1_ctx, pred1_ctx_red_ctx.
    constructor 2.
    etransitivity; eauto.
  Qed.

  Global Instance red_ctx_refl : Reflexive red_ctx.
  Proof.
    move=> x. eapply All2_fold_refl; intros; apply All_decls_refl; auto.
  Qed.

  Hint Transparent context : typeclass_instances.

  Lemma red_ctx_red_context Γ Δ : red_ctx Γ Δ <~> red_context Σ Γ Δ.
  Proof.
    split; intros.
    - red. eapply PCUICEnvironment.All2_fold_impl; tea.
      intros ???? []; constructor; auto.
    - red in X |- *.
      eapply PCUICEnvironment.All2_fold_impl; tea.
      intros ???? []; constructor; auto.
  Qed.
  
  Global Instance red_ctx_trans : Transitive red_ctx.
  Proof.
    move=> Γ Γ' Γ'' H1 H2.
    unfold red_ctx in *. 
    eapply All2_fold_trans; tea.
    intros. transitivity y => //.
    eapply All_decls_impl; tea.
    intros t t' r.
    eapply red_red_ctx; eauto.
    now eapply red_ctx_red_context.
  Qed.

  Lemma clos_rt_red1_rel_red1 x y :
    clos_refl_trans red1_rel x y ->
    red_ctx (fst x) (fst y) *
    clos_refl_trans (red1 Σ (fst x)) (snd x) (snd y).
  Proof.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - split; reflexivity.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. split. auto.
        transitivity u; auto.
      * destruct p. subst. split.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        etransitivity; eauto.
        eapply red_red_ctx; eauto.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        now eapply red_ctx_red_context.
  Qed.

  Lemma decl_body_eq_context_upto_names Γ Γ' n d :
    option_map decl_body (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_body (nth_error Γ' n) = Some d.
  Proof.
    move: Γ' n d; induction Γ; destruct n; simpl; intros; try congruence.
    noconf H. depelim X. depelim c; subst; simpl => //.
    depelim X. apply IHΓ; auto.
  Qed.

  Lemma decl_type_eq_context_upto_names Γ Γ' n d :
    option_map decl_type (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_type (nth_error Γ' n) = Some d.
  Proof.
    move: Γ' n d; induction Γ; destruct n; simpl; intros; try congruence.
    noconf H. depelim X. depelim c; subst; simpl => //.
    depelim X. simpl. apply IHΓ; auto.
  Qed.

  Lemma eq_context_upto_names_app Γ Γ' Δ :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    intros.
    induction Δ; auto. constructor; auto. reflexivity.
  Qed.

  Lemma red1_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    red1 Σ Γ t u ->
    red1 Σ Γ' t u.
  Proof.
    move=> Hctx.
    eapply context_pres_let_bodies_red1.
    eapply PCUICEnvironment.All2_fold_impl; tea => /= _ _ ? ? [] /=;
    rewrite /pres_let_bodies /= //; intros; congruence.
  Qed.

  Lemma clos_rt_red1_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    clos_refl_trans (red1 Σ Γ) t u ->
    clos_refl_trans (red1 Σ Γ') t u.
  Proof.
    intros HΓ H. move: H. apply clos_rt_monotone => x y.
    now apply red1_eq_context_upto_names.
  Qed.

  Lemma red_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    red Σ Γ t u ->
    red Σ Γ' t u.
  Proof.
    intros HΓ H. move: H. apply clos_rt_monotone => x y.
    now apply red1_eq_context_upto_names.
  Qed.
  
  Definition red_ctx_alpha : relation context :=
    All2_fold (fun Γ _ => All_decls_alpha (red Σ Γ)).

  Lemma eq_context_upto_names_red_ctx Γ Δ Γ' Δ' :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    red_ctx Γ Δ ->
    red_ctx_alpha Γ' Δ'.
  Proof.
    intros.
    induction X in X0, Δ, Δ', X1 |- *. depelim X1. depelim X0. constructor.
    depelim X1. depelim X0.
    constructor. eapply IHX; tea.
    depelim p; depelim c; subst; depelim a; try constructor; eauto.
    1,3:now etransitivity.
    all:eapply red_eq_context_upto_names; eauto.
  Qed.

  Lemma eq_context_upto_names_red_ctx_alpha Γ Δ Γ' Δ' :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    red_ctx_alpha Γ Δ ->
    red_ctx_alpha Γ' Δ'.
  Proof.
    intros.
    induction X in X0, Δ, Δ', X1 |- *. depelim X1. depelim X0. constructor.
    depelim X1. depelim X0.
    constructor. eapply IHX; tea.
    depelim p; depelim c; subst; depelim a; try constructor; eauto.
    1,3:now etransitivity.
    all:eapply red_eq_context_upto_names; eauto.
  Qed.

  Instance proper_red_ctx :
    Proper (eq_context_upto_names ==> eq_context_upto_names ==> iffT) red_ctx_alpha.
  Proof.
    reduce_goal.
    split.
    intros. eapply eq_context_upto_names_red_ctx_alpha; eauto.
    intros. symmetry in X, X0. eapply eq_context_upto_names_red_ctx_alpha; eauto.
  Qed.

  Instance red_ctx_alpha_refl : Reflexive red_ctx_alpha.
  Proof.
    rewrite /red_ctx_alpha.
    intros x; apply All2_fold_refl; tc.
  Qed.

  Lemma red_ctx_red_ctx_alpha_trans Γ Δ Δ' : 
    red_ctx Γ Δ -> red_ctx_alpha Δ Δ' -> red_ctx_alpha Γ Δ'.
  Proof.
    intros r r'.
    induction r in Δ', r' |- *; depelim r'; constructor; auto.
    now eapply IHr.
    depelim p; depelim a; constructor; auto.
    all:etransitivity; tea.
    all:eapply red_red_ctx; tea; now eapply red_ctx_red_context.
  Qed.

  Lemma clos_rt_red1_alpha_out x y :
    clos_refl_trans red1_rel_alpha x y ->
    red_ctx_alpha (fst x) (fst y) *
    clos_refl_trans (red1 Σ (fst x)) (snd x) (snd y).
  Proof.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - split; reflexivity.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. split. auto.
        transitivity u; auto.
      * destruct r. destruct p. subst. split; auto.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        eapply red_ctx_red_ctx_alpha_trans; tea.
        eapply red_red_ctx; eauto.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        now eapply red_ctx_red_context.
        destruct p. subst.
        split; auto.
        eapply eq_context_upto_names_red_ctx_alpha. 3:eauto. now symmetry in e. reflexivity.
        eapply clos_rt_red1_eq_context_upto_names; eauto. now symmetry in e.
  Qed.

  Lemma red1_red1_ctx_inv Γ Δ Δ' t u :
     red1 Σ (Γ ,,, Δ) t u ->
     assumption_context Δ ->
     red1_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
     red Σ (Γ ,,, Δ') t u.
   Proof.
     intros redt assΔ redΔ.
     apply red1_pred1 in redt => //.
     eapply red1_ctx_pred1_ctx in redΔ => //.
     eapply pred1_ctx_pred1 in redt; eauto.
     now eapply pred1_red_r in redt.
   Qed.
  
  Lemma red_red1_ctx_inv Γ Δ Δ' t u :
    red Σ (Γ ,,, Δ) t u ->
    assumption_context Δ ->
    red1_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    red Σ (Γ ,,, Δ') t u.
  Proof.
    intros redt assΔ redΔ. induction redt.
    - eapply red1_red1_ctx_inv; eauto.
    - reflexivity.
    - now transitivity y.
  Qed.
    
  Inductive clos_refl_trans_ctx_1n (R : relation context) (x : context) : context -> Type :=
  | rt1n_ctx_eq : clos_refl_trans_ctx_1n R x x
  | rt1n_ctx_trans : forall y z, eq_context_upto_names x y + R x y -> clos_refl_trans_ctx_1n R y z -> clos_refl_trans_ctx_1n R x z.


  Lemma clos_refl_trans_ctx_to_1n (x y : context) :
    clos_refl_trans_ctx (red1_ctx Σ) x y <~> clos_refl_trans_ctx_1n (red1_ctx Σ) x y.
  Proof.
    split.
    induction 1. econstructor 2. eauto. constructor; auto.
    econstructor 2. left; eauto. constructor.
    clear X1 X2.
    induction IHX1 in z, IHX2 |- *.
    destruct IHX2. constructor.
    destruct s. econstructor 2. left; eauto. auto.
    econstructor 2. right; eauto. eauto.
    specialize (IHIHX1 _ IHX2). econstructor 2; eauto.

    induction 1. constructor 2. eapply eq_context_upto_names_refl.
    destruct s. econstructor 3. constructor 2; eauto. eauto.
    econstructor 3. constructor 1; eauto. eauto.
  Qed. 

  Lemma clos_rt_red1_red1_rel_alpha Γ x y :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel_alpha (Γ, x) (Γ, y).
  Proof.
    induction 1. constructor. red. left. pcuicfo.
    constructor 2.
    econstructor 3; eauto.
  Qed.

  Lemma red1_confluent Γ : confluent (red1 Σ Γ).
  Proof.
    intros x y z.
    intros.
    pose proof (pred_rel_confluent (Γ, x) (Γ, y) (Γ, z)).
    forward X1 by now eapply clos_rt_red1_red1_rel_alpha.
    forward X1 by now eapply clos_rt_red1_red1_rel_alpha.
    destruct X1 as [[Δ nf] [redl redr]].
    exists nf.
    eapply clos_rt_red1_alpha_out in redl.
    eapply clos_rt_red1_alpha_out in redr. simpl in *.
    intuition auto.
  Qed.

  Lemma pred_red {Γ t u} :
    clos_refl_trans (pred1 Σ Γ Γ) t u ->
    clos_refl_trans (red1 Σ Γ) t u.
  Proof.
    intros pred.
    eapply (clos_rt_red1_rel_red1 (Γ, t) (Γ, u)).
    apply clos_refl_trans_out.
    apply (clos_rt_red1_alpha_out (Γ, t) (Γ, u)).
    apply clos_red_rel_out_inv.
    induction pred. constructor; auto. constructor 2.
    now transitivity (Γ, y).
  Qed.

End RedConfluence.

Arguments red1_ctx _ _ _ : clear implicits.


Section ConfluenceFacts.
  Context {cf : checker_flags}.
  Context (Σ : global_env) (wfΣ : wf Σ).

  Lemma red_mkApps_tConstruct (Γ : context)
        ind pars k (args : list term) c :
    red Σ Γ (mkApps (tConstruct ind pars k) args) c ->
    ∑ args' : list term,
    (c = mkApps (tConstruct ind pars k) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hred. eapply red_pred in Hred.
    generalize_eq x (mkApps (tConstruct ind pars k) args).
    induction Hred in ind, pars, k, args |- * ; simplify *.
    - eapply pred1_mkApps_tConstruct in r as [r' [eq redargs]].
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]. reflexivity. subst y.
      specialize (IHHred2 _ _ _ _ eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
    - assumption.
  Qed.

  Lemma red_mkApps_tInd (Γ : context)
        ind u (args : list term) c :
    red Σ Γ (mkApps (tInd ind u) args) c ->
    ∑ args' : list term,
    (c = mkApps (tInd ind u) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tInd ind u) args).
    induction Hred in ind, u, args |- * ; simplify *.
    - eapply pred1_mkApps_tInd in r as [r' [eq redargs]].
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]. reflexivity. subst y.
      specialize (IHHred2 _ _ _ eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tRel (Γ : context) k b (args : list term) c :
    nth_error Γ k = Some b -> decl_body b = None ->
    red Σ Γ (mkApps (tRel k) args) c ->
    ∑ args' : list term,
    (c = mkApps (tRel k) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hnth Hb Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tRel k) args).
    induction Hred in k, b, Hnth, Hb, args |- * ; simplify *.
    - eapply pred1_mkApps_tRel in r as [r' [eq redargs]]; eauto.
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]; eauto. subst.
      specialize (IHHred2 _ _ _ Hnth Hb eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tConst_axiom (Γ : context)
        cst u (args : list term) cb c :
    declared_constant Σ cst cb -> cst_body cb = None ->
    red Σ Γ (mkApps (tConst cst u) args) c ->
    ∑ args' : list term,
    (c = mkApps (tConst cst u) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hdecl Hbody Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tConst cst u) args).
    induction Hred in cst, u, args, Hdecl |- *; simplify *.
    - eapply pred1_mkApps_tConst_axiom in r as [r' [eq redargs]]; eauto.
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize (IHHred1 _ _ _ Hdecl eq_refl) as [? [? ?]]. subst y.
      specialize (IHHred2 _ _ _ Hdecl eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma clos_rt_red1_ctx_red_ctx :
    inclusion (clos_refl_trans (@red1_ctx Σ)) (@red_ctx Σ).
  Proof.
    intros x y H. induction H.
    - apply red1_ctx_pred1_ctx in r => //.
      apply pred1_ctx_red_ctx in r => //.
    - reflexivity.
    - now eapply (red_ctx_trans wfΣ); eauto.
  Qed.

  Lemma red_confluence {Γ t u v} :
    red Σ Γ t u -> red Σ Γ t v ->
    ∑ v', red Σ Γ u v' * red Σ Γ v v'.
  Proof.
    move=> H H'.
    destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
    exists nf; intuition auto.
  Qed.

End ConfluenceFacts.

Arguments red_confluence {cf} {Σ} wfΣ {Γ t u v}.

(** We can now derive transitivity of the conversion relation *)

Instance conv_trans {cf:checker_flags} (Σ : global_env_ext) {Γ} :
  wf Σ -> Transitive (conv Σ Γ).
Proof.
  intros wfΣ t u v X0 X1.
  eapply conv_alt_red in X0 as [t' [u' [[tt' uu'] eq]]].
  eapply conv_alt_red in X1 as [u'' [v' [[uu'' vv'] eq']]].
  eapply conv_alt_red.
  destruct (red_confluence wfΣ uu' uu'') as [u'nf [ul ur]].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; try tc.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; try tc.
  exists tnf, unf.
  intuition auto.
  - now transitivity t'.
  - now transitivity v'.
  - now transitivity u'nf.
Qed.

Instance cumul_trans {cf:checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> Transitive (cumul Σ Γ).
Proof.
  intros wfΣ t u v X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply cumul_alt.
  eapply red_eq_term_upto_univ_r in eq. all:tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq';tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, v'1.
  split. 1: split.
  - transitivity v' ; auto.
  - transitivity w' ; auto.
  - eapply leq_term_trans with nf; eauto.
Qed.
