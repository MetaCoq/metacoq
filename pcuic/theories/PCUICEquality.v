(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.


Local Open Scope type_scope.

Section CRelationLemmas.
  Local Set Universe Polymorphism.
  Context {A : Type} (R : crelation A).

  Lemma flip_Reflexive : Reflexive R -> Reflexive (flip R).
  Proof.
    intros HR x. unfold flip. apply reflexivity.
  Qed.

  Lemma flip_Symmetric : Symmetric R -> Symmetric (flip R).
  Proof.
    intros HR x y. unfold flip. apply symmetry.
  Qed.

  Lemma flip_Transitive : Transitive R -> Transitive (flip R).
  Proof.
    intros HR x y z xy yz.
    unfold flip in *. now transitivity y.
  Qed.

End CRelationLemmas.

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly 
  match the instances, so as to keep syntactic equality an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => True (* Missing variance stands for irrelevance *)
    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition R_global_instance Σ Re Rle gr :=
  match lookup_env Σ gr with
  | Some (InductiveDecl decl) => 
    match decl.(ind_variance) with
    | Some v => R_universe_instance_variance Re Rle v
    | None => R_universe_instance Re
    end
   | _ => R_universe_instance Re
  end.

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

Inductive eq_term_upto_univ Σ (Re Rle : Universe.t -> Universe.t -> Prop) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ Σ Re Rle (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ Σ Re Re) args args' ->
    eq_term_upto_univ Σ Re Rle (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ Σ Re Rle (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ Σ Re Rle (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ Σ Re Rle t t' ->
    eq_term_upto_univ Σ Re Re u u' ->
    eq_term_upto_univ Σ Re Rle (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ Σ Re Rle (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_global_instance Σ Re Rle (inductive_mind i) u u' ->
    eq_term_upto_univ Σ Re Rle (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_global_instance Σ Re Rle (inductive_mind i) u u' ->
    eq_term_upto_univ Σ Re Rle (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_term_upto_univ Σ Re Re ty ty' ->
    eq_term_upto_univ Σ Re Rle t t' ->
    eq_term_upto_univ Σ Re Rle (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_term_upto_univ Σ Re Re a a' ->
    eq_term_upto_univ Σ Re Rle b b' ->
    eq_term_upto_univ Σ Re Rle (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_term_upto_univ Σ Re Re t t' ->
    eq_term_upto_univ Σ Re Re ty ty' ->
    eq_term_upto_univ Σ Re Rle u u' ->
    eq_term_upto_univ Σ Re Rle (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
    eq_term_upto_univ Σ Re Re p p' ->
    eq_term_upto_univ Σ Re Re c c' ->
    All2 (fun x y =>
      (fst x = fst y) *
      eq_term_upto_univ Σ Re Re (snd x) (snd y)
    ) brs brs' ->
    eq_term_upto_univ Σ Re Rle (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ Σ Re Re c c' ->
    eq_term_upto_univ Σ Re Rle (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
      eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    eq_term_upto_univ Σ Re Rle (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
      eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    eq_term_upto_univ Σ Re Rle (tCoFix mfix idx) (tCoFix mfix' idx).

(* ** Syntactic conversion up-to universes *)

Definition eq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition leq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (leq_universe φ).
    
Lemma R_global_instance_refl Σ Re Rle gr u : 
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr u u.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct lookup_env as [[g|g]|] eqn:lookup.
  - apply Forall2_same; eauto.
  - destruct ind_variance as [v|] eqn:var.  
    2:apply Forall2_same; eauto. 
    induction u in v |- *; simpl; auto;
    destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  - apply Forall2_same; eauto.
Qed.    

Instance eq_term_upto_univ_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_term_upto_univ Σ Re Rle).
Proof.
  intros hRe hRle t.
  induction t in Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  - apply R_global_instance_refl; auto.
  - apply R_global_instance_refl; auto.
  - eapply All_All2; eauto. simpl. intuition eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
Qed.

Instance eq_term_refl `{checker_flags} Σ φ : Reflexive (eq_term Σ φ).
Proof.
  apply eq_term_upto_univ_refl. all: exact _.
Qed.

Instance leq_term_refl `{checker_flags} Σ φ : Reflexive (leq_term Σ φ).
Proof.
  apply eq_term_upto_univ_refl; exact _.
Qed.

(* TODO MOVE *)
Existing Instance All2_symP.

(* TODO MOVE *)
Instance Forall2_symP :
  forall A (P : A -> A -> Prop),
    RelationClasses.Symmetric P ->
    Symmetric (Forall2 P).
Proof.
  intros A P h l l' hl.
  induction hl. all: auto.
Qed.

Derive Signature for eq_term_upto_univ.

Lemma R_global_instance_sym Σ Re Rle gr u u' : 
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  R_global_instance Σ Re Rle gr u' u ->
  R_global_instance Σ Re Rle gr u u'.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct lookup_env as [[g|g]|] eqn:lookup.
  - apply Forall2_symP; eauto.
  - destruct ind_variance as [v|] eqn:var.  
    2:apply Forall2_symP; eauto. 
    induction u in u', v |- *; destruct u'; simpl; auto;
    destruct v as [|v vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.    

Instance eq_term_upto_univ_sym Σ Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle u v e.
  induction u in Rle, hle, v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - econstructor. eapply R_global_instance_sym; eauto. 
  - econstructor. eapply R_global_instance_sym; eauto. 
  - econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 [h2 h3]]. eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]].
      eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]]. eapply h1 in h3 ; auto.
Qed.

Instance eq_term_sym `{checker_flags} Σ φ : Symmetric (eq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_sym. all: exact _.
Qed.

Instance R_global_instance_trans Σ Re Rle gr :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (R_global_instance Σ Re Rle gr).
Proof.
  intros he hle x y z.
  unfold R_global_instance.
  destruct lookup_env as [[d|d]|].
  eapply Forall2_trans; auto.
  2:eapply Forall2_trans; auto.
  destruct ind_variance.
  2:eapply Forall2_trans; auto.
  clear -he hle.
  induction x in y, z, l |- *; destruct y, z, l; simpl; auto => //.
  intros [Ra Rxy] [Rt Ryz].
  split; eauto.
  destruct t1; simpl in *; auto.
  now etransitivity; eauto.
  now etransitivity; eauto.
Qed.

Instance eq_term_upto_univ_trans Σ Re Rle :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle u v w e1 e2.
  induction u in Rle, hle, v, w, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try eapply Forall2_trans ; eauto
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
    constructor.
    eapply R_global_instance_trans; eauto.
  - dependent destruction e2.
    constructor.
    eapply R_global_instance_trans; eauto.
  - dependent destruction e2.
    econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, brs'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 [h2 h3]].
      destruct p0 as [? ?]. split; eauto.
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

Instance eq_term_trans {cf:checker_flags} Σ φ : Transitive (eq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_trans. all: exact _.
Qed.

Instance leq_term_trans {cf:checker_flags} Σ φ : Transitive (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_trans ; exact _.
Qed.


Instance eq_term_upto_univ_equiv Σ Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ Σ Re Re).
Proof.
  constructor. all: exact _.
Defined.

Instance eq_term_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term Σ φ) :=
  {| Equivalence_Reflexive := eq_term_refl _ _;
     Equivalence_Symmetric := eq_term_sym _ _;
     Equivalence_Transitive := eq_term_trans _ _ |}.

Instance leq_term_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term Σ φ) :=
  {| PreOrder_Reflexive := leq_term_refl _ _;
     PreOrder_Transitive := leq_term_trans _ _ |}.

Instance R_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (R_universe_instance R).
Proof.
  split.
  - intro. apply Forall2_same. reflexivity.
  - intros x y xy. eapply Forall2_sym, Forall2_impl; tea. now symmetry.
  - intros x y z xy yz. eapply Forall2_trans; tea. apply hR.
Qed.

Lemma R_universe_instance_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_universe_instance Re) (R_universe_instance Rle).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence R) gr
  : RelationClasses.Equivalence (R_global_instance Σ R R gr).
Proof.
  split.
  - intro. apply R_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply R_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply R_global_instance_trans; eauto; typeclasses eauto.
Qed.

Instance R_global_instance_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) gr :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ Re Re gr) (R_global_instance Σ Re Rle gr).
Proof.
  intros hR u v.
  unfold R_global_instance.
  destruct lookup_env as [[g|g]|]; auto.
  destruct ind_variance; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu]. split; auto.
  destruct t0; simpl in *; auto.
Qed.  

Lemma eq_term_upto_univ_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  Antisymmetric (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros hR u v h h'.
  induction u in v, h, h' |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; inversion h' ;
       subst ; try constructor ; auto.
  all: eapply RelationClasses.antisymmetry; eauto.
Qed.

Instance leq_term_antisym {cf:checker_flags} Σ φ
  : Antisymmetric (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.

Instance R_global_instance_impl Σ Re Re' Rle Rle' gr :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr) (R_global_instance Σ Re' Rle' gr).
Proof.
  intros he hle t t'.
  rewrite /R_global_instance.
  destruct lookup_env as [[g|g]|]; eauto using R_universe_instance_impl'.
  destruct ind_variance; eauto using R_universe_instance_impl'.
  induction t in l, t' |- *; destruct l, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
Qed.

Instance R_global_instance_empty_impl Σ Re Re' Rle Rle' gr :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance [] Re Rle gr) (R_global_instance Σ Re' Rle' gr).
Proof.
  intros he hle hele t t'.
  rewrite /R_global_instance. simpl.
  destruct lookup_env as [[g|g]|]; eauto using R_universe_instance_impl'.
  destruct ind_variance; eauto using R_universe_instance_impl'.
  induction t in l, t' |- *; destruct l, t'; simpl; intros H; inv H; auto.
  simpl.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Instance eq_term_upto_univ_impl Σ Re Re' Rle Rle' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re' Rle').
Proof.
  intros he hle t t'.
  induction t in t', Rle, Rle', hle |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl; eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
Qed.

Instance eq_term_upto_univ_empty_impl Σ Re Re' Rle Rle' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (eq_term_upto_univ [] Re Rle) (eq_term_upto_univ Σ Re' Rle').
Proof.
  intros he hle hele t t'.
  induction t in t', Rle, Rle', hle, hele |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_empty_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_empty_impl; eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
Qed.

Instance eq_term_upto_univ_leq Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  subrelation (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

Instance eq_term_leq_term {cf:checker_flags} Σ φ
  : subrelation (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_leq; exact _.
Qed.

Instance leq_term_partial_order {cf:checker_flags} Σ φ
  : PartialOrder (eq_term Σ φ) (leq_term Σ φ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.


Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift Σ Re Rle n k :
  Proper (eq_term_upto_univ Σ Re Rle ==> eq_term_upto_univ Σ Re Rle) (lift n k).
Proof.
  intros u v e.
  induction u in v, n, k, e, Rle |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [cbn ; constructor ; try lih ; try assumption; solve_all].
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
Qed.

Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
  eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
  leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.


Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_substs Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_term_upto_univ Σ Re Rle u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_term_upto_univ Σ Re Rle (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hR u v n l l' hu hl.
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

Lemma eq_term_upto_univ_subst Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    eq_term_upto_univ Σ Re Rle u v ->
    eq_term_upto_univ Σ Re Re x y ->
    eq_term_upto_univ Σ Re Rle (u{n := x}) (v{n := y}).
Proof.
  intros hR u v n x y e1 e2.
  eapply eq_term_upto_univ_substs; eauto.
Qed.

Lemma subst_eq_term {cf:checker_flags} Σ φ l k T U :
  eq_term Σ φ T U ->
  eq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  now eapply All2_same.
Qed.

Lemma subst_leq_term {cf:checker_flags} Σ φ l k T U :
  leq_term Σ φ T U ->
  leq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  intro; apply eq_universe_leq_universe.
  now eapply All2_same.
Qed.

(** ** Boolean version **  *)

Definition compare_universe_variance (equ lequ : Universe.t -> Universe.t -> bool) v u u' :=
  match v with
  | Variance.Irrelevant => true
  | Variance.Covariant => lequ (Universe.make u) (Universe.make u')
  | Variance.Invariant => equ (Universe.make u) (Universe.make u')
  end.

Definition compare_universe_instance equ u u' :=
  forallb2 equ (map Universe.make u) (map Universe.make u').
  
Fixpoint compare_universe_instance_variance equ lequ v u u' :=
  match u, u' with
  | u :: us, u' :: us' =>
    match v with
    | [] => true (* Missing variance stands for irrelevance *)
    | v :: vs => compare_universe_variance equ lequ v u u' &&
        compare_universe_instance_variance equ lequ vs us us'
    end
  | [], [] => true
  | _, _ => false
  end.

Definition compare_global_instance Σ equ lequ gr :=
  match lookup_env Σ gr with
  | Some (InductiveDecl decl) => 
    match decl.(ind_variance) with
    | Some v => compare_universe_instance_variance equ lequ v
    | None => compare_universe_instance equ
    end
   | _ => compare_universe_instance equ
  end.

Fixpoint eqb_term_upto_univ Σ (equ lequ : Universe.t -> Universe.t -> bool) (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ Σ equ equ) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    lequ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ Σ equ lequ u u' &&
    eqb_term_upto_univ Σ equ equ v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    compare_global_instance Σ equ lequ (inductive_mind i) u u'

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    compare_global_instance Σ equ lequ (inductive_mind i) u u'

  | tLambda na A t, tLambda na' A' t' =>
    eqb_term_upto_univ Σ equ equ A A' &&
    eqb_term_upto_univ Σ equ lequ t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_term_upto_univ Σ equ equ A A' &&
    eqb_term_upto_univ Σ equ lequ B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_term_upto_univ Σ equ equ B B' &&
    eqb_term_upto_univ Σ equ equ b b' &&
    eqb_term_upto_univ Σ equ lequ u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_term_upto_univ Σ equ equ p p' &&
    eqb_term_upto_univ Σ equ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      eqb_term_upto_univ Σ equ equ (snd x) (snd y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ Σ equ equ c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ Σ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ Σ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ Σ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ Σ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | _, _ => false
  end.

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
  | ih : forall lequ Rle hle t', reflectT (eq_term_upto_univ _ _ _ ?t _) _,
    hle : forall u u', reflectT (?Rle u u') (?lequ u u')
    |- context [ eqb_term_upto_univ _ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle hle t') ; nodec ; subst
  end.

Lemma compare_global_instance_impl (equ lequ : _ -> _ -> bool) Σ Re Rle gr :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (compare_global_instance Σ equ lequ gr) (R_global_instance Σ Re Rle gr).
Proof.
  intros hre hrle x y.
  unfold compare_global_instance, R_global_instance.
  destruct lookup_env as [[g|g]|]; auto.
  intro. eapply forallb2_Forall2 in H.
  eapply Forall2_impl; tea; eauto.
  2:{ intro. eapply forallb2_Forall2 in H.
    eapply Forall2_impl; tea; eauto. }
  destruct ind_variance; auto.
  2:{ intro. eapply forallb2_Forall2 in H.
    eapply Forall2_impl; tea; eauto. }
  induction x in l, y |- *; destruct l, y; simpl; auto.    
  rtoProp. intros [Hat Hxy]. split; auto.
  destruct t; simpl in *; auto.
Qed.

Lemma Forall2_forallb2:
  forall (A : Type) (p : A -> A -> bool) (l l' : list A),
  Forall2 (fun x y : A => p x y) l l' -> forallb2 p l l'.
Proof.
  induction 1; simpl; auto.
  now rewrite H IHForall2.
Qed.

Lemma compare_global_instance_impl_inv (equ lequ : _ -> _ -> bool) Σ Re Rle gr :
  RelationClasses.subrelation Re equ ->
  RelationClasses.subrelation Rle lequ ->
  subrelation (R_global_instance Σ Re Rle gr) (compare_global_instance Σ equ lequ gr).
Proof.
  intros hre hrle x y.
  unfold compare_global_instance, R_global_instance.
  destruct lookup_env as [[g|g]|]; auto.
  intro. red. eapply Forall2_forallb2.
  eapply Forall2_impl; tea; eauto.
  2:{ intro. eapply Forall2_forallb2.
    eapply Forall2_impl; tea; eauto. }
  destruct ind_variance; auto.
  2:{ intro. eapply Forall2_forallb2.
    eapply Forall2_impl; tea; eauto. }
  induction x in l, y |- *; destruct l, y; simpl; auto.    
  rtoProp. intros [Hat Hxy]. split; auto.
  destruct t; simpl in *; auto.
Qed.

Lemma eqb_term_upto_univ_impl (equ lequ : _ -> _ -> bool) Σ  Re Rle :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (eqb_term_upto_univ Σ equ lequ) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t'; try discriminate 1. all: cbn -[eqb].
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [|discriminate]. constructor.
    cbn in H. apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    eapply All_impl; tea. eauto.
  - constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    eapply compare_global_instance_impl; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    eqspec; [|discriminate].
    intro. simpl in H.
    constructor. eapply compare_global_instance_impl; eauto.
  - eqspec; [|discriminate]. intro. rtoProp.
    destruct indn. econstructor; eauto.
    apply forallb2_All2 in H0.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|discriminate].
    intro. split; eauto.
  - eqspec; [|discriminate]. intro. constructor; eauto.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
Qed.

Lemma equiv_reflectT P (b : bool) : (P -> b) -> (b -> P) -> reflectT P b.
Proof.
  intros. destruct b; constructor; auto.
Qed.

Lemma reflectT_subrelation {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> subrelation R r.
Proof.
  intros. intros x y h. destruct (X x y); auto.
Qed.

Lemma reflectT_subrelation' {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> subrelation r R.
Proof.
  intros. intros x y h. destruct (X x y); auto. discriminate.
Qed.

Lemma reflect_eq_term_upto_univ Σ equ lequ (Re Rle : Universe.t -> Universe.t -> Prop) :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall t t', reflectT (eq_term_upto_univ Σ Re Rle t t')
                   (eqb_term_upto_univ Σ equ lequ t t').
Proof.
  intros he hle t t'.
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
      * constructor. intro bot. inversion bot. inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion X0.
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
  - cbn - [eqb]. eqspecs. equspec equ he. ih.
    constructor. constructor; assumption.
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
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl; apply equiv_reflectT.
    inversion 1; subst.
    eapply compare_global_instance_impl_inv; eauto.
    apply (reflectT_subrelation he).
    apply (reflectT_subrelation hle).
    intro; constructor; eapply compare_global_instance_impl; eauto.
    apply (reflectT_subrelation' he).
    apply (reflectT_subrelation' hle).
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl; apply equiv_reflectT.
    inversion 1; subst.
    eapply compare_global_instance_impl_inv; eauto.
    apply (reflectT_subrelation he).
    apply (reflectT_subrelation hle).
    intro; constructor; eapply compare_global_instance_impl; eauto.
    apply (reflectT_subrelation' he).
    apply (reflectT_subrelation' hle).

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

Lemma compare_global_instance_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) gr u,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    compare_global_instance Σ eqb leqb gr u u.
Proof.
  intros Σ eqb leqb gr u eqb_refl leqb_refl.
  rewrite /compare_global_instance.
  destruct lookup_env as [[g|g]|].
  2:destruct ind_variance.
  1,3-4:eapply forallb2_map, forallb2_refl; intro; apply eqb_refl.
  induction u in l |- *; destruct l; simpl; auto.
  rtoProp. split; auto.
  destruct t; simpl; auto.
Qed.

Lemma eqb_term_upto_univ_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    eqb_term_upto_univ Σ eqb leqb t t.
Proof.
  intros Σ eqb leqb t eqb_refl leqb_refl.
  induction t using term_forall_list_ind in leqb, leqb_refl |- *.
  all: simpl.
  all: rewrite -> ?Nat.eqb_refl, ?eq_string_refl, ?eq_kername_refl, ?eq_inductive_refl.
  all: repeat rewrite -> eq_prod_refl
        by (eauto using eq_prod_refl, Nat.eqb_refl, eq_string_refl, eq_inductive_refl).
  all: repeat lazymatch goal with
      | ih : forall leqb, _ -> @?P leqb |- _ =>
        rewrite -> ih by assumption ; clear ih
      end.
  all: simpl.
  all: try solve [ eauto ].
  - induction X.
    + reflexivity.
    + simpl. rewrite -> p by assumption. auto.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - eapply compare_global_instance_refl; auto.
  - eapply compare_global_instance_refl; auto.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl. rewrite -> p0 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite -> Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_upto_univ_mkApps Σ Re Rle u1 l1 u2 l2 :
    eq_term_upto_univ Σ Re Rle u1 u2 ->
    All2 (eq_term_upto_univ Σ Re Re) l1 l2 ->
    eq_term_upto_univ Σ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ Σ Re Rle u u' *
      All2 (eq_term_upto_univ Σ Re Re) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in u, t, h, Rle |- *.
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

Lemma eq_term_upto_univ_mkApps_r_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ Σ Re Rle u' u *
      All2 (eq_term_upto_univ Σ Re Re) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in u, t, h, Rle |- *.
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

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ φ Γ :
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply eq_term_upto_univ_it_mkLambda_or_LetIn; exact _.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkProd_or_LetIn {cf:checker_flags} Σ φ Γ:
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply eq_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ φ Γ u v :
    eq_term Σ φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term Σ  φ u v.
Proof.
  revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma upto_eq_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation (eq_term_upto_univ Σ eq eq) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_impl.
  all: intros ? ? []; eauto.
Qed.

(** ** Syntactic equality up to printing anotations ** *)

Definition upto_names := eq_term_upto_univ [] eq eq.

Infix "≡" := upto_names (at level 60).

Infix "≡'" := (eq_term_upto_univ eq eq) (at level 60).
Notation upto_names' := (eq_term_upto_univ eq eq).

Instance upto_names_ref : Reflexive upto_names.
Proof.
  eapply eq_term_upto_univ_refl; exact _.
Qed.

Instance upto_names_sym : Symmetric upto_names.
Proof.
  eapply eq_term_upto_univ_sym; exact _.
Qed.

Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply eq_term_upto_univ_trans; exact _.
Qed.

(* todo: rename *)
(* Definition nleq_term t t' := *)
(*   eqb_term_upto_univ eqb eqb t t'. *)

(* Corollary reflect_upto_names : *)
(*   forall t t', reflectT (upto_names t t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. eapply reflect_eq_term_upto_univ. *)
(*   all: intros u u'; eapply reflect_reflectT, eqb_spec. *)
(* Qed. *)

Lemma upto_names_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation upto_names (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_empty_impl.
  all: intros ? ? []; eauto.
Qed.

Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> eq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> leq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma eq_term_upto_univ_isApp Σ Re Rle u v :
  eq_term_upto_univ Σ Re Rle u v ->
  isApp u = isApp v.
Proof.
  induction 1.
  all: reflexivity.
Qed.


(** ** Equality on contexts ** *)

Inductive eq_context_upto Σ (Re : Universe.t -> Universe.t -> Prop) : context -> context -> Type :=
| eq_context_nil : eq_context_upto Σ Re [] []
| eq_context_vass na A Γ nb B Δ :
    eq_term_upto_univ Σ Re Re A B ->
    eq_context_upto Σ Re Γ Δ ->
    eq_context_upto Σ Re (Γ ,, vass na A) (Δ ,, vass nb B)
| eq_context_vdef na u A Γ nb v B Δ :
    eq_term_upto_univ Σ Re Re u v ->
    eq_term_upto_univ Σ Re Re A B ->
    eq_context_upto Σ Re Γ Δ ->
    eq_context_upto Σ Re (Γ ,, vdef na u A) (Δ ,, vdef nb v B).

Definition eq_def_upto Σ Re d d' : Type :=
  (eq_term_upto_univ Σ Re Re d.(dtype) d'.(dtype)) *
  (eq_term_upto_univ Σ Re Re d.(dbody) d'.(dbody)) *
  (d.(rarg) = d'.(rarg)).

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Definition eq_decl_upto Σ Re d d' : Type :=
  rel_option (eq_term_upto_univ Σ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Σ Re Re d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Σ Re :
  subrelation (All2 (eq_decl_upto Σ  Re)) (eq_context_upto Σ Re).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [h1 h2].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h1.
    + constructor ; eauto.
    + constructor ; eauto.
Qed.

Lemma eq_context_upto_refl Σ Re :
  RelationClasses.Reflexive Re ->
  Reflexive (eq_context_upto Σ Re).
Proof.
  intros hRe Γ.
  induction Γ as [| [na [bo |] ty] Γ ih].
  - constructor.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
Qed.

Lemma eq_context_upto_sym Σ Re :
  RelationClasses.Symmetric Re ->
  Symmetric (eq_context_upto Σ Re).
Proof.
  intros hRe Γ Δ.
  induction 1; constructor; eauto using eq_term_upto_univ_sym.
  all:eapply eq_term_upto_univ_sym; auto.
Qed.

Lemma eq_context_upto_cat Σ Re Γ Δ Γ' Δ' :
  eq_context_upto Σ Re Γ Γ' ->
  eq_context_upto Σ Re Δ Δ' ->
  eq_context_upto Σ Re (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros h1 h2. induction h2 in Γ, Γ', h1 |- *.
  - assumption.
  - simpl. constructor ; eauto.
  - simpl. constructor ; eauto.
Qed.

Lemma eq_context_upto_rev Σ Re Γ Δ :
  eq_context_upto Σ Re Γ Δ ->
  eq_context_upto Σ Re (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_rev' :
  forall Σ Γ Δ Re,
    eq_context_upto Σ Re Γ Δ ->
    eq_context_upto Σ Re (List.rev Γ) (List.rev Δ).
Proof.
  intros Σ Γ Δ Re h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. assumption.
    + assumption.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_context_upto_length :
  forall {Σ Re Γ Δ},
    eq_context_upto Σ Re Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Σ Re Γ Δ h.
  induction h. all: simpl ; auto.
Qed.

Lemma eq_context_upto_subst_context Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_context_upto Σ Re u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_context_upto Σ Re (subst_context l n u) (subst_context l' n v).
Proof.
  intros re u v n l l'.
  induction 1; intros Hl.
  - rewrite !subst_context_nil. constructor.
  - rewrite !subst_context_snoc; constructor; auto.
    simpl. rewrite (eq_context_upto_length X).
    apply eq_term_upto_univ_substs; auto. typeclasses eauto.
  - rewrite !subst_context_snoc; constructor; auto;
    simpl; rewrite (eq_context_upto_length X).
    apply eq_term_upto_univ_substs; auto. typeclasses eauto.
    apply eq_term_upto_univ_substs; auto. typeclasses eauto.
Qed.

Lemma eq_context_upto_smash_context Σ ctx ctx' x y :
  eq_context_upto Σ eq ctx ctx' -> eq_context_upto Σ eq x y -> 
  eq_context_upto Σ eq (smash_context ctx x) (smash_context ctx' y).
Proof.
  induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl; 
    try split; auto; try constructor; auto.
  - apply IHx; auto. apply eq_context_upto_cat; auto.
    constructor; auto. constructor.
  - apply IHx; auto. eapply eq_context_upto_subst_context; eauto.
    typeclasses eauto.
Qed.

Lemma eq_context_upto_nth_error Σ Re ctx ctx' n :
  eq_context_upto Σ Re ctx ctx' -> 
  rel_option (eq_decl_upto Σ Re) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto. 
    constructor. split; auto. constructor.
  - destruct n; simpl; auto.
    constructor. constructor; simpl; auto.
    constructor; auto.
Qed.

Lemma eq_context_impl :
  forall Σ Re Re',
    RelationClasses.subrelation Re Re' ->
    subrelation (eq_context_upto Σ Re) (eq_context_upto Σ Re').
Proof.
  intros Σ Re Re' hR Γ Δ h.
  induction h.
  - constructor.
  - constructor. 2: assumption.
    eapply eq_term_upto_univ_impl. all: eassumption.
  - constructor. 3: assumption.
    all: eapply eq_term_upto_univ_impl. all: eassumption.
Qed.

Section ContextUpTo.
  Context (Σ : global_env).
  Context (Re : Universe.t -> Universe.t -> Prop).
  Context (ReR : RelationClasses.Reflexive Re).
  Context (ReS : RelationClasses.Symmetric Re).
  Context (ReT : RelationClasses.Transitive Re).

  Notation eq_ctx := (eq_context_upto Σ Re).

  Global Instance eq_ctx_refl : Reflexive eq_ctx.
  Proof. now intros ?; apply eq_context_upto_refl. Qed.

  Global Instance eq_ctx_sym : Symmetric eq_ctx.
  Proof.
    intros x y. now apply eq_context_upto_sym.
  Qed.

  Global Instance eq_ctx_trans : Transitive eq_ctx.
  Proof.
    intros Γ0 Γ1 Γ2 H. induction H in Γ2 |- *.
    - intros H2; inversion H2; subst; constructor; auto.
    - intros H2; inversion H2; subst; constructor; auto.
      etransitivity; eauto.
    - intros H2; inversion H2; subst; constructor; auto.
      all: etransitivity; eauto.
  Qed.

End ContextUpTo.


(* todo: unify *)
Definition eq_opt_term `{checker_flags} Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} Σ φ (d d' : context_decl) :=
  eq_opt_term Σ φ d.(decl_body) d'.(decl_body) * eq_term Σ φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} Σ φ (Γ Δ : context) :=
  All2 (eq_decl Σ φ) Γ Δ.


Lemma lift_eq_decl `{checker_flags} Σ ϕ n k d d' :
  eq_decl Σ ϕ d d' -> eq_decl Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  destruct d, d', decl_body, decl_body0;
    unfold eq_decl, map_decl; cbn; intuition auto using lift_eq_term.
Qed.

Lemma lift_eq_context `{checker_flags} Σ φ l l' n k :
  eq_context Σ φ l l' ->
  eq_context Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite -> ?lift_context_snoc0.
  constructor.
  all: inversion X; subst. constructor.
  - apply All2_length in X1. rewrite X1.
    now apply lift_eq_decl.
  - now apply IHl.
Qed.


Lemma eq_term_upto_univ_mkApps_inv Σ Re u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Σ Re Re (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ Σ Re Re u u' * All2 (eq_term_upto_univ Σ Re Re) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isLambda_eq_term_l Σ Re u v :
    isLambda u ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_eq_term_r Σ Re u v :
    isLambda v ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_eq_term_l Σ Re u v :
    isConstruct_app u ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r :
  forall Σ Re u v,
    isConstruct_app v ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app u.
Proof.
  intros Σ Re u v h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

(* TODO MOVE *)
Instance subrelation_same :
  forall A (R : A -> A -> Prop),
    RelationClasses.subrelation R R.
Proof.
  intros A R x y h. assumption.
Qed.

Lemma R_global_instance_flip Σ gr 
  (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v:
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  R_global_instance Σ Re Rle gr u v ->
  R_global_instance Σ Re Rle' gr v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl'.
  rewrite /R_global_instance.
  destruct lookup_env as [[g|g]|] eqn:lookup.
  - apply Forall2_symP; eauto.
  - destruct ind_variance as [vs|] eqn:var.  
    2:apply Forall2_symP; eauto. 
    induction u in vs, v |- *; destruct v; simpl; auto;
    destruct vs as [|v' vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v'; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.

Lemma eq_term_upto_univ_flip Σ (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ Σ Re Rle u v ->
  eq_term_upto_univ Σ Re Rle' v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H.
  assert (Resub : RelationClasses.subrelation Re Re).
  { typeclasses eauto. }
  revert Rerefl Rlerefl Resym Retrans Rletrans incl incl' Resub.
  revert Re Rle u v H Rle'.
  induction 1; intros; constructor; intuition auto.
  - eapply All2_symP; auto. eapply eq_term_upto_univ_sym; auto.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply R_global_instance_flip; eauto.
  - eapply R_global_instance_flip; eauto.
  - eapply All2_sym. solve_all.
    simpl in *. subst. now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
Qed.


Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' H. eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed.
