(* Distributed under the terms of the MIT license. *)
Require Import ssrbool MSetWeakList MSetFacts MSetProperties.
From MetaCoq.Template Require Import utils config Universes wGraph.

Import ConstraintType.

Arguments Z.add : simpl nomatch.
Arguments Nat.leb : simpl nomatch.
Arguments Nat.eqb : simpl nomatch.



(** variable levels are levels which are Level or Var *)
Module VariableLevel.
  Inductive t := Level (_ : string) | Var (_ : nat).
  Definition lt : t -> t -> Prop :=
    fun x y => match x, y with
            | Level _, Var _ => True
            | Level s, Level s' => string_lt s s'
            | Var n, Var n' => n < n'
            | Var _, Level _ => False
            end.
  Global Instance lt_strorder : StrictOrder lt.
    split.
    - intros [s|n] H; cbn in H.
      unfold string_lt in H.
      pose proof (string_compare_eq s s). intuition.
      rewrite H in *. discriminate. intuition.
    - intros [s1|n1] [s2|n2] [s3|n3]; cbn; intuition.
      eapply transitive_string_lt; eassumption.
  Qed.
  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x y [] z t []; reflexivity.
  Qed.
  Definition compare : t -> t -> comparison :=
    fun x y => match x, y with
            | Level _, Var _ => Datatypes.Lt
            | Level s, Level s' => string_compare s s'
            | Var n, Var n' => Nat.compare n n'
            | Var _, Level _ => Datatypes.Gt
            end.
  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
    intros [s|n] [s'|n']; cbn; try now constructor.
    - eapply CompareSpec_Proper. 2-4: reflexivity.
      2: apply CompareSpec_string.
      split; congruence.
    - eapply CompareSpec_Proper. 2-4: reflexivity.
      2: apply PeanoNat.Nat.compare_spec.
      split; congruence.
  Qed.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    intros [s|n] [s'|n']; try now constructor.
    destruct (string_dec s s'); [left|right]; congruence.
    destruct (PeanoNat.Nat.eq_dec n n'); [left|right]; congruence.
  Defined.

  Definition to_noprop (l : t) : NoPropLevel.t :=
    match l with
    | Level s => NoPropLevel.Level s
    | Var n => NoPropLevel.Var n
    end.

  Definition to_level (l : t) : Level.t := to_noprop l.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | Level s => Z.pos (v.(valuation_mono) s)
               | Var x => Z.of_nat (v.(valuation_poly) x)
               end.
End VariableLevel.

Coercion VariableLevel.to_noprop : VariableLevel.t >-> NoPropLevel.t.


Module GoodConstraint.
  Inductive t_ :=
  (* l <= l' *)
  | gc_le : VariableLevel.t -> VariableLevel.t -> t_
  (* l < l' *)
  | gc_lt : VariableLevel.t -> VariableLevel.t -> t_
  (* Set < Var n *)
  | gc_lt_set : nat -> t_
  (* Set = Var n *)
  | gc_eq_set : nat -> t_.
  Definition t : Set := t_.
  Definition eq : t -> t -> Prop := Logic.eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. all: try apply VariableLevel.eq_dec.
    all: apply Peano_dec.eq_nat_dec.
  Defined.
End GoodConstraint.
Module GoodConstraintSet := Make GoodConstraint.
Module GoodConstraintSetFact := WFactsOn GoodConstraint GoodConstraintSet.
Module GoodConstraintSetProp := WPropertiesOn GoodConstraint GoodConstraintSet.

Definition GoodConstraintSet_pair x y
  := GoodConstraintSet.add y (GoodConstraintSet.singleton x).

Lemma GoodConstraintSet_pair_In x y z
  : GoodConstraintSet.In x (GoodConstraintSet_pair y z)
    -> x = y \/ x = z.
Proof.
  intro H. apply GoodConstraintSetFact.add_iff in H.
  destruct H; [intuition|].
  apply GoodConstraintSetFact.singleton_1 in H; intuition.
Qed.

Import VariableLevel GoodConstraint.


Definition gc_satisfies0 v (gc : GoodConstraint.t) : bool :=
  match gc with
  | gc_le l l' => (val v l <=? val v l')%Z
  | gc_lt l l' => (val v l <? val v l')%Z
  | gc_lt_set l => 0 <? v.(valuation_poly) l
  | gc_eq_set l => 0 =? v.(valuation_poly) l
  end.

Definition gc_satisfies v : GoodConstraintSet.t -> bool :=
  GoodConstraintSet.for_all (gc_satisfies0 v).

Definition gc_consistent ctrs : Prop := exists v, gc_satisfies v ctrs.

Lemma gc_satisfies_pair v gc1 gc2 :
  (gc_satisfies0 v gc1 /\ gc_satisfies0 v gc2) <->
  gc_satisfies v (GoodConstraintSet_pair gc1 gc2).
Proof.
  cbn; destruct (GoodConstraint.eq_dec gc2 gc1); cbn;
    rewrite if_true_false.
  now destruct e. symmetry. apply andb_and.
Defined.

(* None -> not satisfiable *)
(* Some empty -> useless *)
(* else: singleton or two elements set (l = l' -> {l<=l', l'<=l}) *)
Definition gc_of_constraint `{checker_flags} (uc : UnivConstraint.t)
  : option GoodConstraintSet.t
  := let empty := Some GoodConstraintSet.empty in
     let singleton := fun x => Some (GoodConstraintSet.singleton x) in
     let pair := fun x y => Some (GoodConstraintSet_pair x y) in
     match uc with
     (* Prop _ _ *)
     | (Level.lProp, Le, Level.lProp) => empty
     | (Level.lProp, Le, _) => if prop_sub_type then empty else None
     | (Level.lProp, Eq, Level.lProp) => empty
     | (Level.lProp, Eq, _) => None
     | (Level.lProp, Lt, Level.lProp) => None
     | (Level.lProp, Lt, _) => if prop_sub_type then empty else None

     (* Set _ _ *)
     | (Level.lSet, Le, Level.lProp) => None
     | (Level.lSet, Le, _) => empty
     | (Level.lSet, Eq, Level.lProp) => None
     | (Level.lSet, Eq, Level.lSet) => empty
     | (Level.lSet, Eq, Level.Level _) => None
     | (Level.lSet, Eq, Level.Var n) => singleton (gc_eq_set n)
     | (Level.lSet, Lt, Level.lProp) => None
     | (Level.lSet, Lt, Level.lSet) => None
     | (Level.lSet, Lt, Level.Level _) => empty
     | (Level.lSet, Lt, Level.Var n) => singleton (gc_lt_set n)

     (* Level _ _ *)
     | (Level.Level _, Le, Level.lProp) => None
     | (Level.Level _, Le, Level.lSet) => None
     | (Level.Level l, Le, Level.Level l')
       => singleton (gc_le (Level l) (Level l'))
     | (Level.Level l, Le, Level.Var n) => singleton (gc_le (Level l) (Var n))
     | (Level.Level _, Eq, Level.lProp) => None
     | (Level.Level _, Eq, Level.lSet) => None
     | (Level.Level l, Eq, Level.Level l')
       => pair (gc_le (Level l) (Level l')) (gc_le (Level l') (Level l))
     | (Level.Level l, Eq, Level.Var n)
       => pair (gc_le (Level l) (Var n)) (gc_le (Var n) (Level l))
     | (Level.Level _, Lt, Level.lProp) => None
     | (Level.Level _, Lt, Level.lSet) => None
     | (Level.Level l, Lt, Level.Level l')
       => singleton (gc_lt (Level l) (Level l'))
     | (Level.Level l, Lt, Level.Var n) => singleton (gc_lt (Level l) (Var n))

     (* Var _ _ *)
     | (Level.Var _, Le, Level.lProp) => None
     | (Level.Var n, Le, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Le, Level.Level l) => singleton (gc_le (Var n) (Level l))
     | (Level.Var n, Le, Level.Var n') => singleton (gc_le (Var n) (Var n'))
     | (Level.Var _, Eq, Level.lProp) => None
     | (Level.Var n, Eq, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Eq, Level.Level l)
       => pair (gc_le (Var n) (Level l)) (gc_le (Level l) (Var n))

     | (Level.Var n, Eq, Level.Var n')
       => pair (gc_le (Var n) (Var n')) (gc_le (Var n') (Var n))
     | (Level.Var _, Lt, Level.lProp) => None
     | (Level.Var _, Lt, Level.lSet) => None
     | (Level.Var n, Lt, Level.Level l) => singleton (gc_lt (Var n) (Level l))
     | (Level.Var n, Lt, Level.Var n') => singleton (gc_lt (Var n) (Var n'))
     end.

Section GC.

Context `{cf : checker_flags}.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (gc_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1; destruct l, l'; try constructor.
    all: cbn -[GoodConstraintSet_pair] in *.
    all: lled; cbn -[GoodConstraintSet_pair]; try reflexivity.
    all: rewrite ?if_true_false; repeat toProp ; try lia.
    all: apply gc_satisfies_pair; split; cbn; toProp; try lia.
  - destruct uc as [[[] []] []]; intro H; constructor.
    all: cbn -[GoodConstraintSet_pair] in *; try contradiction.
    all: rewrite ?if_true_false in *; lled; cbn -[GoodConstraintSet_pair] in *;
      try contradiction; repeat toProp; try lia.
    all: apply gc_satisfies_pair in H; destruct H as [H1 H2]; cbn in *;
      repeat toProp; try lia.
Qed.


Definition add_gc_of_constraint uc (S : option GoodConstraintSet.t)
  := S1 <- S ;;
     S2 <- gc_of_constraint uc ;;
     ret (GoodConstraintSet.union S1 S2).

Definition gc_of_constraints (ctrs : ConstraintSet.t) : option GoodConstraintSet.t
  := ConstraintSet.fold add_gc_of_constraint
                        ctrs (Some GoodConstraintSet.empty).


Lemma gc_of_constraints_spec v ctrs :
  satisfies v ctrs <-> on_Some (gc_satisfies v) (gc_of_constraints ctrs).
Proof.
  unfold gc_satisfies, satisfies, ConstraintSet.For_all, gc_of_constraints.
  set (S := GoodConstraintSet.empty).
  rewrite ConstraintSet.fold_spec.
  etransitivity. eapply iff_forall.
  intro; eapply imp_iff_compat_r. eapply ConstraintSetFact.elements_iff.
  set (l := ConstraintSet.elements ctrs). simpl.
  transitivity ((forall uc, InA Logic.eq uc l -> satisfies0 v uc) /\
                (forall gc, GoodConstraintSet.In gc S -> gc_satisfies0 v gc)). {
    intuition. inversion H0. }
  clearbody S; revert S; induction l; intro S; cbn.
  - split.
    + intro. apply GoodConstraintSetFact.for_all_1.
      intros x y []; reflexivity.
      intro; apply H.
    + intros HS. split. intros ux H; inversion H.
      apply GoodConstraintSetFact.for_all_2.
      intros x y []; reflexivity.
      assumption.
  - split.
    + intros [H1 H2].
      assert (HH : on_Some (gc_satisfies v) (gc_of_constraint a)). {
        apply gc_of_constraint_spec, H1. now constructor. }
      case_eq (gc_of_constraint a); [|intro e; rewrite e in HH; contradiction].
      intros X HX; rewrite HX in *; cbn in HH.
      apply IHl. split.
      * intros uc H0. apply H1. now apply InA_cons_tl.
      * intros gc H0. apply GoodConstraintSetFact.union_1 in H0.
        induction H0. intuition.
        apply GoodConstraintSetFact.for_all_2 in HH.
        apply HH. assumption.
        intros x y []; reflexivity.
    + intros HH.
      case_eq (gc_of_constraint a).
      * intros X HX; rewrite HX in *; cbn in HH.
        destruct (proj2 (IHl _) HH) as [IH1 IH2]. clear IHl HH.
        split. intuition. apply InA_cons in H. induction H.
        subst. apply gc_of_constraint_spec. rewrite HX.
        cbn. apply GoodConstraintSetFact.for_all_1.
        intros x y []; reflexivity.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_3.
        firstorder.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_2.
      * intro HX; rewrite HX in HH. apply False_rect. revert HH; clear.
        induction l. inversion 1.
        assumption.
Qed.


Lemma gc_consistent_iff ctrs :
  consistent ctrs <-> on_Some gc_consistent (gc_of_constraints ctrs).
Proof.
  split.
  - intros [v H]. apply gc_of_constraints_spec in H.
    destruct (gc_of_constraints ctrs); cbn in *.
    exists v. assumption. contradiction.
  - case_eq  (gc_of_constraints ctrs); cbn; [|contradiction].
    intros ctrs' e HC. destruct HC as [v Hv].
    exists v. apply gc_of_constraints_spec. now rewrite e; cbn.
Qed.



Definition gc_leq_universe_n n ctrs (u u' : Universe.t)
  := forall v, gc_satisfies v ctrs -> (Z.of_nat n + val v u <= val v u')%u.

Definition gc_eq_universe0 φ (u u' : Universe.t) :=
  forall v, gc_satisfies v φ -> val v u = val v u'.

Definition gc_leq_universe φ (u u' : Universe.t)
  := if check_univs then gc_leq_universe_n 0 φ u u' else True.

Definition gc_eq_universe φ (u u' : Universe.t)
  := if check_univs then gc_eq_universe0 φ u u' else True.


Lemma gc_leq_universe_n_iff n ctrs u u' :
  leq_universe_n n ctrs u u'
  <-> on_Some_or_None (fun ctrs => gc_leq_universe_n n ctrs u u')
                    (gc_of_constraints ctrs).
Proof.
  split.
  - intro H. case_eq (gc_of_constraints ctrs).
    + intros ctrs' e. cbn. intros v Hv. apply H. apply gc_of_constraints_spec.
      rewrite e. assumption.
    + intro; exact I.
  - case_eq (gc_of_constraints ctrs); cbn.
    + intros ctrs' e H.
      intros v Hv. apply H.
      apply gc_of_constraints_spec in Hv.
      rewrite e in Hv; assumption.
    + intros e _ v Hv.
      apply gc_of_constraints_spec in Hv.
      rewrite e in Hv; contradiction.
Defined.

Lemma gc_eq_universe0_iff ctrs u u' :
  eq_universe0 ctrs u u'
  <-> on_Some_or_None (fun ctrs => gc_eq_universe0 ctrs u u')
                    (gc_of_constraints ctrs).
Proof.
  split.
  - intro H. case_eq (gc_of_constraints ctrs).
    + intros ctrs' e. cbn. intros v Hv. apply H. apply gc_of_constraints_spec.
      rewrite e. assumption.
    + intro; exact I.
  - case_eq (gc_of_constraints ctrs); cbn.
    + intros ctrs' e H.
      intros v Hv. apply H.
      apply gc_of_constraints_spec in Hv.
      rewrite e in Hv; assumption.
    + intros e _ v Hv.
      apply gc_of_constraints_spec in Hv.
      rewrite e in Hv; contradiction.
Defined.

Lemma gc_leq_universe_iff ctrs u u' :
  leq_universe ctrs u u'
  <-> on_Some_or_None (fun ctrs => gc_leq_universe ctrs u u')
                    (gc_of_constraints ctrs).
Proof.
  unfold leq_universe, leq_universe0, gc_leq_universe.
  destruct check_univs.
  apply gc_leq_universe_n_iff.
  destruct (gc_of_constraints ctrs); reflexivity.
Qed.

Lemma gc_eq_universe_iff ctrs u u' :
  eq_universe ctrs u u'
  <-> on_Some_or_None (fun ctrs => gc_eq_universe ctrs u u')
                    (gc_of_constraints ctrs).
Proof.
  unfold eq_universe, eq_universe0, gc_eq_universe.
  destruct check_univs.
  apply gc_eq_universe0_iff.
  destruct (gc_of_constraints ctrs); reflexivity.
Qed.

End GC.




Module Import wGraph := wGraph.WeightedGraph NoPropLevel.

Local Notation lSet := NoPropLevel.lSet.
(* vtn = variable to noprop *)
Local Notation vtn := VariableLevel.to_noprop.

Definition universes_graph := wGraph.t.
Definition init_graph : universes_graph
  := (VSet.singleton lSet, EdgeSet.empty, lSet).

Lemma init_graph_invariants : invariants init_graph.
Proof.
  repeat split; cbn in *.
  1-2: inversion H.
  now apply VSet.singleton_spec.
  apply VSet.singleton_spec in H.
  rewrite H; constructor.
Defined.

Definition no_prop_levels (X : LevelSet.t) : VSet.t
  := LevelSet.fold (fun l X => match NoPropLevel.of_level l with
                            | Some l => VSet.add l X
                            | None => X
                            end)
                   X VSet.empty.


Definition declared : Level.t -> LevelSet.t -> Prop := LevelSet.In.

Definition uctx_invariants (uctx : ContextSet.t)
  := ConstraintSet.For_all (fun '(l, _, l') => declared l uctx.1 /\ declared l' uctx.1)
                           uctx.2.

Definition global_uctx_invariants (uctx : ContextSet.t)
  := LevelSet.In Level.lSet uctx.1 /\ uctx_invariants uctx.


Definition global_gc_uctx_invariants (uctx : VSet.t * GoodConstraintSet.t)
  := VSet.In lSet uctx.1 /\ GoodConstraintSet.For_all (fun gc => match gc with
                 | gc_le l l'
                 | gc_lt l l'  => VSet.In (vtn l) uctx.1
                                 /\ VSet.In (vtn l') uctx.1
                 | gc_lt_set n
                 | gc_eq_set n => VSet.In (NoPropLevel.Var n) uctx.1
                 end) uctx.2.

Definition gc_of_uctx `{checker_flags} (uctx : ContextSet.t)
  : option (VSet.t * GoodConstraintSet.t)
  := ctrs <- gc_of_constraints uctx.2 ;;
     ret (no_prop_levels uctx.1, ctrs).


Lemma no_prop_levels_no_prop_level (l : NoPropLevel.t) levels
  : declared l levels ->  VSet.In l (no_prop_levels levels).
Proof.
  unfold no_prop_levels, declared. rewrite LevelSet.fold_spec.
  intro H. apply LevelSetFact.elements_1, InA_In_eq in H.
  cut (In (l : Level.t) (LevelSet.elements levels) \/ VSet.In l VSet.empty);
    [|now left].
  clear H; generalize VSet.empty.
  induction (LevelSet.elements levels); simpl.
  - intuition.
  - intros X [[HH|HH]|HH].
    + subst a; cbn. apply IHl0.
      right. rewrite NoPropLevel.of_to_level.
      apply VSet.add_spec; intuition.
    + apply IHl0. now left.
    + apply IHl0. right.
      destruct (NoPropLevel.of_level a); tas.
      apply VSet.add_spec; intuition.
Qed.

Lemma gc_of_constraint_iff `{cf:checker_flags} ctrs0 ctrs gc
      (HH : gc_of_constraints ctrs0 = Some ctrs)
: GoodConstraintSet.In gc ctrs
  <-> ConstraintSet.Exists
      (fun e => on_Some (GoodConstraintSet.In gc) (gc_of_constraint e)) ctrs0.
Proof.
  unfold gc_of_constraints in HH. rewrite ConstraintSet.fold_spec in HH.
  transitivity ((exists ctr, In ctr (ConstraintSet.elements ctrs0) /\
                        on_Some (GoodConstraintSet.In gc) (gc_of_constraint ctr))
                \/ GoodConstraintSet.In gc GoodConstraintSet.empty).
  2:{ split.
      - intros [[ctr [H1 H2]]|H]. exists ctr. split.
        apply ConstraintSetFact.elements_iff, InA_In_eq; tas. tas.
        now apply GoodConstraintSetFact.empty_iff in H.
      - intros [ctr H]. left. exists ctr. split.
        apply InA_In_eq, ConstraintSetFact.elements_1, H. apply H. }
  revert HH; generalize GoodConstraintSet.empty.
  induction (ConstraintSet.elements ctrs0).
  - cbn. intros X HH. apply some_inj in HH; subst.
    firstorder.
  - intros X HH. simpl in HH. unfold add_gc_of_constraint at 2 in HH.
    simpl in HH. case_eq (gc_of_constraint a).
    + intros Y HY. rewrite HY in HH.
      apply IHl in HH.
      etransitivity. exact HH. etransitivity.
      apply or_iff_compat_l. apply GoodConstraintSet.union_spec.
      split.
      * intros [[ctr H]|[H|H]]. left. exists ctr. intuition. intuition.
        left. exists a. intuition. rewrite HY; tas.
      * intros [[ctr [[H1|H1] H2]]|H]. subst a. right. right.
        rewrite HY in H2; tas.
        left. exists ctr. intuition.
        right. left; tas.
    + intro eq; rewrite eq in HH; simpl in HH.
      apply False_rect. clear -HH. induction l.
      * discriminate HH.
      * simpl in HH. apply IHl.
        apply HH.
Qed.



Lemma gc_of_uctx_invariants `{cf:checker_flags} uctx uctx'
      (H : gc_of_uctx uctx = Some uctx')
  : global_uctx_invariants uctx -> global_gc_uctx_invariants uctx'.
Proof.
  intros [Hi0 Hi].
  unfold gc_of_uctx in H.
  case_eq (gc_of_constraints uctx.2); [|intro eq; rewrite eq in H; discriminate].
  intros ctrs eq; rewrite eq in H; apply some_inj in H. subst uctx'.
  split; simpl.
  - apply no_prop_levels_no_prop_level; tas.
  - red in Hi.
    destruct uctx as [levels ctrs0]; cbn in *.
    intros gc Hgc.
    eapply gc_of_constraint_iff in Hgc; tea.
    destruct Hgc as [e [He HH]].
    specialize (Hi e He); cbn in Hi.
    clear -Hi HH.
    destruct e as [[l ct] l']; simpl in Hi.
    destruct l, ct, l'; cbn in HH; destruct prop_sub_type; cbn in HH.
    all: match goal with
         | HH : False |- _ => contradiction HH
         | HH : GoodConstraintSet.In ?A GoodConstraintSet.empty |- _
           => apply GoodConstraintSetFact.empty_iff in HH; contradiction HH
         | HH : GoodConstraintSet.In ?A (GoodConstraintSet.singleton ?B) |- _
           => apply GoodConstraintSetFact.singleton_1 in HH; subst gc
         | HH : GoodConstraintSet.In ?A (GoodConstraintSet_pair ?B _) |- _
           => apply GoodConstraintSet_pair_In in HH; destruct HH as [HH|HH]; subst gc
         end.
    all: try split; try apply no_prop_levels_no_prop_level, Hi;
      try apply no_prop_levels_no_prop_level, Hi.
Qed.


Definition edge_of_level (l : VariableLevel.t) : EdgeSet.elt :=
  match l with
  | Level l => (lSet, 1, NoPropLevel.Level l)
  | Var n => (lSet, 0, NoPropLevel.Var n)
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edge_of_constraint (gc : GoodConstraint.t) : EdgeSet.elt :=
  match gc with
  | gc_le l l' => (vtn l, 0, vtn l')
  | gc_lt l l' => (vtn l, 1, vtn l')
  | gc_lt_set n => (lSet, 1, vtn (Var n))
  | gc_eq_set n => (vtn (Var n), 0, lSet)
  end.


Lemma source_edge_of_level g : (edge_of_level g)..s = lSet.
Proof.
  destruct g; reflexivity.
Qed.

Lemma target_edge_of_level g : (edge_of_level g)..t = vtn g.
Proof.
  destruct g; reflexivity.
Qed.


Definition make_graph (uctx : VSet.t * GoodConstraintSet.t) : wGraph.t :=
  let init_edges := VSet.fold (fun l E => match l with
                                       | NoPropLevel.Level s =>
                                         EdgeSet.add (edge_of_level (Level s)) E
                                       | NoPropLevel.Var n =>
                                         EdgeSet.add (edge_of_level (Var n)) E
                                       | lSet => E end) uctx.1 EdgeSet.empty in
  let edges := GoodConstraintSet.fold
                 (fun ctr => EdgeSet.add (edge_of_constraint ctr)) uctx.2 init_edges in
  (uctx.1, edges, lSet).

Lemma make_graph_E uctx e
  : EdgeSet.In e (wGraph.E (make_graph uctx))
    <-> (exists l, VSet.In (vtn l) uctx.1 /\ e = edge_of_level l)
      \/ (GoodConstraintSet.Exists (fun gc => e = edge_of_constraint gc) uctx.2).
Proof.
  unfold make_graph. unfold wGraph.E.
  simpl.
  assert (XX: forall E, EdgeSet.In e (GoodConstraintSet.fold
                           (fun ctr => EdgeSet.add (edge_of_constraint ctr)) uctx.2 E)
          <-> (exists gc, In gc (GoodConstraintSet.elements uctx.2) /\ e = edge_of_constraint gc)
             \/ EdgeSet.In e E). {
    intro E. rewrite GoodConstraintSet.fold_spec.
    induction (GoodConstraintSet.elements uctx.2) in E |- *.
    - cbn. firstorder.
    - simpl. etransitivity. apply IHl. clear IHl. split.
      + intros [[gc H]|H]. left. exists gc. intuition.
        apply EdgeSet.add_spec in H. destruct H as [H|H].
        left. exists a. intuition. right; tas.
      + intros [[gc [[H1|H1] H2]]|H].
        right. apply EdgeSet.add_spec. left; now subst.
        left. exists gc. split; tas.
        right. apply EdgeSet.add_spec. right; tas. }
  etransitivity. apply XX. clear XX.
  etransitivity. apply or_comm.
  etransitivity. apply or_iff_compat_l.
  2: apply or_iff_compat_r.
  - apply iff_ex; intro gc. apply and_iff_compat_r.
    symmetry. etransitivity.
    apply GoodConstraintSetFact.elements_iff. apply InA_In_eq.
  - transitivity ((exists l, In (vtn l) (VSet.elements uctx.1) /\ e = edge_of_level l)
                  \/ EdgeSet.In e EdgeSet.empty).
    2:{ split. intros [[l [H1 H2]]|H]. exists l. split; tas.
        apply InA_In_eq, VSetFact.elements_iff in H1; tas.
        now apply EdgeSetFact.empty_iff in H.
        intros [l [H1 H2]]. left. exists l. split.
        apply InA_In_eq, VSetFact.elements_1; tas. tas. }
    rewrite VSet.fold_spec. generalize EdgeSet.empty.
    induction (VSet.elements uctx.1).
    + cbn. intro E; firstorder.
    + intro E. etransitivity. apply IHl. split.
      * intro HH.
        destruct HH as [[l' Hl]|HH]. left. exists l'. intuition.
        destruct a as [|l'|l']. right; tas.
        all: apply EdgeSet.add_spec in HH; destruct HH;
          [left|right; tas].
        exists (Level l'); intuition. exists (Var l'); intuition.
      * intros [[l' [[H1|H1] H2]]|H].
        right. subst a. destruct l'; apply EdgeSet.add_spec; left; tas.
        destruct l'; left; [exists (Level s)|exists (Var n)]; intuition.
        right. destruct a; tas; apply EdgeSet.add_spec; right; tas.
Qed.


Global Instance make_graph_invariants uctx (Hi : global_gc_uctx_invariants uctx)
  : invariants (make_graph uctx).
Proof.
  split; [|split].
  - intros e He. apply make_graph_E in He.
    destruct He as [[l [Hl He]]|[gc [Hgc He]]].
    + subst e. split. rewrite source_edge_of_level. apply Hi.
      rewrite target_edge_of_level; tas.
    + subst e. split. destruct gc; try apply (Hi.p2 _ Hgc). apply Hi.
      destruct gc; try apply (Hi.p2 _ Hgc). apply Hi.
  - apply Hi.
  - cbn. intros l Hl. sq. destruct l. constructor.
    econstructor. 2: constructor.
    assert (He: EdgeSet.In (edge_of_level (Level s)) (wGraph.E (make_graph uctx))). {
      apply make_graph_E. left. exists (Level s). intuition. }
    eexists; exact He.
    econstructor. 2: constructor.
    assert (He: EdgeSet.In (edge_of_level (Var n)) (wGraph.E (make_graph uctx))). {
      apply make_graph_E. left. exists (Var n). intuition. }
    eexists; exact He.
Qed.


Ltac sets_iff :=
  match goal with
  |  |- (_ /\ _) <-> _
     => eapply and_iff_compat_l; sets_iff
  |  |- (_ /\ _) <-> _
     => eapply and_iff_compat_l; sets_iff
  |  |- (_ \/ _) <-> _
     => eapply or_iff_compat_l; sets_iff
  |  |- (_ \/ _) <-> _
     => eapply or_iff_compat_l; sets_iff
  |  |- VSet.In _ (VSet.add _ _) <-> _
     => etransitivity; [eapply VSet.add_spec|sets_iff]
  |  |- EdgeSet.In _ (EdgeSet.add _ _) <-> _
     => etransitivity; [eapply EdgeSet.add_spec|sets_iff]
  |  |- VSet.In _ (VSet.singleton _) <-> _
     => etransitivity; [eapply VSet.singleton_spec|sets_iff]
  |  |- EdgeSet.In _ (EdgeSet.singleton _) <-> _
     => etransitivity; [eapply EdgeSet.singleton_spec|sets_iff]
  | _ => reflexivity
  end.

Ltac simplify_sets :=
  repeat match goal with
  | |- VSet.In ?A (VSet.add ?B ?C)
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj2 X); clear X]
  | |- EdgeSet.In ?A (EdgeSet.add ?B ?C)
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj2 X); clear X]
  | H : VSet.In ?A (VSet.add ?B ?C) |- _
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A (EdgeSet.add ?B ?C) |- _
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : VSet.In ?A (VSet.singleton ?B) |- _
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.singleton B) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A (EdgeSet.singleton ?B) |- _
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.singleton B) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A EdgeSet.empty |- _
    => apply EdgeSetFact.empty_iff in H; contradiction
  end.

Definition labelling_of_valuation (v : valuation) : labelling
  := fun x => match x with
           | lSet => 0
           | NoPropLevel.Level l => Pos.to_nat (v.(valuation_mono) l)
           | NoPropLevel.Var n => v.(valuation_poly) n
           end.

Definition valuation_of_labelling (l : labelling) : valuation
  := {| valuation_mono := fun s => Pos.of_nat (l (vtn (Level s)));
        valuation_poly := fun n => l (vtn (Var n)) |}.


Section MakeGraph.
  Context uctx (Huctx : global_gc_uctx_invariants uctx).
  Let ctrs := uctx.2.
  Let G : universes_graph := make_graph uctx.

  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x uctx.1
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof.
    destruct x; cbnr.
    - intros _. now apply proj1 in Hl; cbn in Hl.
    - intro Hs. apply Nat2Pos.id.
      assert (HH: EdgeSet.In (lSet, 1, vtn (Level s)) (wGraph.E G)). {
        subst G. apply make_graph_E. left.
        exists (Level s). intuition. }
      apply (proj2 Hl) in HH; cbn in HH. lia.
  Qed.

  Lemma make_graph_spec v :
    gc_satisfies v uctx.2 <-> correct_labelling G (labelling_of_valuation v).
  Proof.
    unfold gc_satisfies, correct_labelling. split; intro H.
    - split. reflexivity.
      intros e He. cbn in He.
      apply make_graph_E in He.
      destruct He as [[l [Hl He]]|[ctr [Hc He]]]; cbn.
      + subst e; cbn. destruct l; cbn; lia.
      + subst e.
        apply GoodConstraintSet.for_all_spec in H.
        2: intros x y []; reflexivity.
        specialize (H _ Hc). cbn in *.
        destruct ctr as [[] []|[] []|n|n]; cbn in *; toProp H; try lia.
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (proj2 (make_graph_E uctx (edge_of_constraint gc))
                        (or_intror (ex_intro _ gc (conj Hgc eq_refl)))) as XX.
      specialize (H.p2 _ XX).
      destruct gc as [[] []|[] []|n|n]; intro HH; cbn in *; toProp; lia.
  Qed.

  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) uctx.2 <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) uctx.2.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling. intuition.
    rewrite !valuation_labelling_eq; tas. now apply H.
    all: now apply make_graph_invariants.
  Qed.

  Corollary make_graph_spec2 :
    gc_consistent uctx.2 <-> exists l, correct_labelling G l.
  Proof.
    split.
    - intros [v H]. exists (labelling_of_valuation v).
      apply make_graph_spec. assumption.
    - intros [l Hl]. exists (valuation_of_labelling l).
      apply make_graph_spec'. assumption.
  Defined.

  Global Instance consistent_no_loop : gc_consistent ctrs -> acyclic_no_loop G.
  Proof.
    intro. apply acyclic_caract1, make_graph_spec2.
    now apply make_graph_invariants. assumption.
  Defined.
End MakeGraph.

Existing Class gc_consistent.
Existing Class global_gc_uctx_invariants.
Existing Class global_uctx_invariants.
Existing Instance gc_of_uctx_invariants.

(** ** Check of consistency ** *)

Definition is_consistent `{checker_flags} uctx :=
  match gc_of_uctx uctx with
  | Some uctx => is_acyclic (make_graph uctx)
  | None => false
  end.

Lemma is_consistent_spec `{checker_flags} uctx (Huctx : global_uctx_invariants uctx)
  : is_consistent uctx <-> consistent uctx.2.
Proof.
  etransitivity. 2: symmetry; apply gc_consistent_iff.
  unfold is_consistent; cbn.
  case_eq (gc_of_constraints uctx.2); cbn.
  2: intro; split; [discriminate|inversion 1].
  intros ctrs Hctrs.
  pose proof (gc_of_uctx_invariants uctx (no_prop_levels uctx.1, ctrs)) as XX.
  cbn in XX; rewrite Hctrs in XX; specialize (XX eq_refl Huctx).
  etransitivity. apply make_graph_invariants in XX.
  etransitivity. apply is_acyclic_spec; tas.
  apply acyclic_caract1; tas.
  symmetry; apply (make_graph_spec2 (no_prop_levels uctx.1, ctrs)); tas.
Qed.


(* This section: specif in term of gc_uctx *)
Section CheckLeq.
  Context {cf:checker_flags}.

  Context (G : universes_graph)
          uctx (Huctx: global_gc_uctx_invariants uctx) (HC : gc_consistent uctx.2)
          (HG : G = make_graph uctx).

  Definition gc_level_declared l
    := on_Some_or_None (fun l => VSet.In l uctx.1) (NoPropLevel.of_level l).

  Lemma gc_level_declared_make_graph (l : NoPropLevel.t) :
    gc_level_declared l -> VSet.In l (wGraph.V G).
  Proof.
    intros Hl. red in Hl. rewrite NoPropLevel.of_to_level in Hl; cbn in Hl.
    subst G; assumption.
  Qed.

  Definition gc_expr_declared e
    := on_Some_or_None (fun l => VSet.In l uctx.1) (UnivExpr.get_noprop e).

  Definition gc_levels_declared (u : Universe.t)
    := UnivExprSet.For_all gc_expr_declared u.


  Lemma val_level_of_variable_level v (l : VariableLevel.t)
    : val v (l : Level.t) = val v l.
  Proof.
    destruct l; cbn; lia.
  Qed.

  Lemma val_labelling_of_valuation v (l : NoPropLevel.t)
    : val v (Universe.make l) = Z.of_nat (labelling_of_valuation v l).
  Proof.
    destruct l; cbnr. lia.
  Qed.

  Lemma val_labelling_of_valuation' v (l : NoPropLevel.t) b :
    val v (Universe.make' (UnivExpr.npe (l, b)))
    = ((if b then 1 else 0) + Z.of_nat (labelling_of_valuation v l))%Z.
  Proof.
    destruct l; cbnr. lia.
  Qed.

  Lemma val_valuation_of_labelling' L  (l : NoPropLevel.t) b
        (e := UnivExpr.npe (l, b)) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) e = ((if b then 1 else 0) + Z.of_nat (L l))%Z.
  Proof.
    intros Hl [HG1 HG2]. subst G. simpl in HG1.
    destruct l as [|l|l]; rewrite ?HG1; cbnr.
    pose proof (make_graph_E uctx (edge_of_level (VariableLevel.Level l))).p2 as H.
    forward H. {
      left. eexists; split; try reflexivity; tas. }
    specialize (HG2 _ H); cbn in HG2. rewrite HG1 in HG2; cbn in HG2.
    f_equal. clear -HG2. set (L (NoPropLevel.Level l)) in *; clearbody n.
    destruct n; try lia.
    rewrite <- Pos.of_nat_succ. lia.
  Qed.

  Lemma val_valuation_of_labelling L  (l : NoPropLevel.t) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) l = Z.of_nat (L l)%Z.
  Proof.
    intros Hl HL.
    exact (val_valuation_of_labelling' L l false Hl HL).
  Qed.


  (** ** Check of leq ** *)

  Lemma leq_universe_vertices0 n (l l' : NoPropLevel.t)
    : leq_vertices G n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intros H v Hv. subst G.
    apply make_graph_spec in Hv; tas.
    specialize (H _ Hv).
    rewrite !val_labelling_of_valuation. lled; lia.
  Qed.

  Lemma leq_universe_vertices1 n (l l' : NoPropLevel.t)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l')
      -> leq_vertices G n l l'.
  Proof.
    subst G. intros H v Hv.
    pose proof (H _ (make_graph_spec' _ Huctx _ Hv)) as HH.
    rewrite <- (valuation_labelling_eq _ _ Hv l Hl).
    rewrite <- (valuation_labelling_eq _ _ Hv l' Hl').
    pose proof (val_labelling_of_valuation (valuation_of_labelling v) l).
    pose proof (val_labelling_of_valuation (valuation_of_labelling v) l').
    cbn in *; lled; lia.
  Qed.

  Lemma leq_universe_vertices n (l l' : NoPropLevel.t)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l')
      <-> leq_vertices G n l l'.
  Proof.
    split.
    - intros H v Hv. apply leq_universe_vertices1; tas.
    - apply leq_universe_vertices0.
  Qed.


  Definition leqb_no_prop_n n (l l' : NoPropLevel.t)
    := leqb_vertices G n l l'.

  Lemma leqb_no_prop_n_spec0 n l l'
    : leqb_no_prop_n n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intro HH. apply leq_universe_vertices0.
    apply leqb_vertices_correct; tas; subst G; exact _.
  Qed.

  Lemma leqb_no_prop_n_spec n (l l' : NoPropLevel.t)
        (Hl : VSet.In l uctx.1) (Hl' : VSet.In l' uctx.1)
    : leqb_no_prop_n n l l'
      <-> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof with try exact _.
    symmetry. etransitivity. apply leq_universe_vertices; subst G; assumption.
    etransitivity. subst G; apply leqb_vertices_correct...
    unfold leqb_no_prop_n; now subst G.
  Qed.


  (* this is function [check_smaller_expr] of kernel/uGraph.ml *)
  Definition leqb_expr_n n (e1 e2 : UnivExpr.t) :=
    match e1, e2 with
    | UnivExpr.lProp, UnivExpr.lProp => n =? 0
    | UnivExpr.npe _, UnivExpr.lProp => false
    | UnivExpr.lProp, UnivExpr.npe (l, false) => match n with
                     | O => prop_sub_type
                     | S n => leqb_no_prop_n n lSet l
                     end
    | UnivExpr.lProp, UnivExpr.npe (l, true) => match n with
                     | O => prop_sub_type
                     | S O => true
                     | S (S n) => leqb_no_prop_n n lSet l
                     end
    | UnivExpr.npe (l1, false), UnivExpr.npe (l2, false)
    | UnivExpr.npe (l1, true), UnivExpr.npe (l2, true) => leqb_no_prop_n n l1 l2
    | UnivExpr.npe (l1, true), UnivExpr.npe (l2, false) => leqb_no_prop_n (S n) l1 l2
    | UnivExpr.npe (l1, false), UnivExpr.npe (l2, true)
      => leqb_no_prop_n (Peano.pred n) l1 l2 (* surprising! *)
    end.


  (* Non trivial lemma *)
  Lemma constraint_strengthening (l1 l2 : NoPropLevel.t) :
    gc_level_declared l1 -> gc_level_declared l2 ->
    (forall v, gc_satisfies v uctx.2 -> (val v l1 <= 1 + val v l2)%u) ->
    forall v, gc_satisfies v uctx.2 -> (val v l1 <= val v l2)%u.
  Proof.
    intros Hl1 Hl2 Hl12.
    assert (gc_leq_universe_n 0 uctx.2 (Universe.make l1) (Universe.make l2)).
    2:{ intros v Hv; specialize (H v Hv). now rewrite !Universe.val_make_npl in H. }
    apply gc_level_declared_make_graph in Hl1 as Hl1'.
    apply gc_level_declared_make_graph in Hl2 as Hl2'.
    assert (HG1 : invariants G) by (subst; exact _).
    assert (HG2 : acyclic_no_loop G) by (subst; exact _).
    apply leq_universe_vertices0. 
    apply leq_vertices_caract0; tas.
    case_eq (lsp G l1 l2); [cbn; intros; lia|].
    pose (K := 12). intro HH. exfalso.
    apply correct_labelling_lsp_G' with (K:=K) in HH as HH1; tas.
    set (G' := wGraph.G' G l2 l1 K) in HH1; cbn in HH1.
    assert (Hs : wGraph.s G = lSet) by now subst G.
    rewrite Hs in HH1.
    pose proof (make_graph_spec' _ Huctx
                                 (fun x => option_get 0 (lsp G' lSet x))) as HH2.
    forward HH2; [now subst G|].
    specialize (Hl12 _ HH2); cbn in Hl12; clear HH2.
    assert (HG'1 : invariants G'). {
      subst G'; apply HI'; subst G; auto. }
    assert (HG'2 : acyclic_no_loop G'). {
      subst G'; apply HG'; subst G; auto. }
    apply lsp_s in Hl1' as Hl1G; tas.
    destruct Hl1G as [n1 Hn1]; rewrite Hs in Hn1.
    apply lsp_s in Hl2' as Hl2G; tas.
    destruct Hl2G as [n2 Hn2]; rewrite Hs in Hn2.
    pose proof (lsp_G'_incr G l2 l1 K lSet l1) as Xl1.
    rewrite Hn1 in Xl1.
    replace (wGraph.G' G l2 l1 K) with G' in Xl1; [|now subst G].
    case_eq (lsp G' lSet l1);
      [|intro XX; now rewrite XX in Xl1].
    intros n1' Hn1'; rewrite Hn1' in *; cbn in *.
    pose proof (lsp_G'_incr G l2 l1 K lSet l2) as Xl2.
    rewrite Hn2 in Xl2.
    replace (wGraph.G' G l2 l1 K) with G' in Xl2; [|now subst G].
    case_eq (lsp G' lSet l2);
      [|intro XX; now rewrite XX in Xl2].
    intros n2' Hn2'; rewrite Hn2' in *; cbn in *.
    pose proof (lsp_G'_sx G l2 l1 Hl1' Hl2' HH K) as XX.
    replace (lsp (wGraph.G' G l2 l1 K) (wGraph.s G) l2) with (Some n2') in XX;
      [|subst G G'; congruence].
    replace (lsp (wGraph.G' G l2 l1 K) (wGraph.s G) l1) with (Some n1') in XX;
      [|subst G G'; congruence]; cbn in XX.
    apply lle_le in Hl12.
    rewrite !val_valuation_of_labelling in Hl12; tas.
    rewrite Hn1', Hn2' in Hl12; cbn in Hl12; lia.
  Qed.

  Lemma leqb_expr_n_spec0 n e e'
    : leqb_expr_n n e e'
      -> gc_leq_universe_n n uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    unfold leqb_expr_n.
    destruct e as [|[l []]], e' as [|[l' []]]; cbn in *; try discriminate;
      intros H v Hv; cbn;
      try (apply leqb_no_prop_n_spec0 in H; specialize (H v Hv); cbn in H;
           rewrite ?UnivExpr.val_make_npl in H; try (lled; lia)).
    - toProp; subst; reflexivity.
    - destruct n as [|[|n]].
      * pose proof (NoPropLevel.val_zero l' v); lled; lia.
      * pose proof (NoPropLevel.val_zero l' v); lled; lia.
      * apply leqb_no_prop_n_spec0 in H. specialize (H v Hv).
        cbn in H. rewrite ?UnivExpr.val_make_npl in H. lled; lia.
    - destruct n.
      * pose proof (NoPropLevel.val_zero l' v); lled; lia.
      * apply leqb_no_prop_n_spec0 in H. specialize (H v Hv).
        cbn in H. rewrite ?UnivExpr.val_make_npl in H. lled; lia.
    - pose proof (NoPropLevel.val_zero l v).
      destruct n; lled; lia.
  Qed.

  Local Ltac tac0 v :=
    repeat match goal with
           | l : NoPropLevel.t |- _
             => pose proof (NoPropLevel.val_zero l v);
               change (id NoPropLevel.t) in l
           end;
    unfold id in *.
  Local Ltac tac1
    := match goal with
       | H : gc_leq_universe_n _ _ _ _ |- is_true (leqb_no_prop_n _ _ _)
         => let v := fresh "v" in
           apply leqb_no_prop_n_spec; tas; try apply Huctx;
           [..|intros v Hv; specialize (H v Hv)]; tac0 v;
           cbn in *; rewrite ?UnivExpr.val_make_npl in *
       | v0 : valuation |- _ => tac0 v0
       end.

  Lemma leqb_expr_n_spec n e e'
        (HHl  : gc_expr_declared e)
        (HHl' : gc_expr_declared e')
    : leqb_expr_n n e e'
      <-> gc_leq_universe_n n uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    split; [apply leqb_expr_n_spec0|].
    unfold leqb_expr_n.
    destruct e as [|[l []]], e' as [|[l' []]]; cbn; intro H;
      destruct HC as  [v0 Hv0]; pose proof (H v0 Hv0) as H0; cbn in H0.
    - toProp. lled; lia.
    - destruct n as [|[|n]]; tac1; lled; try reflexivity; try lia.
    - destruct n as [|n]; tac1; lled; try reflexivity; try lia.
    - tac1; lled; try reflexivity; try lia.
    - tac1; lled; try reflexivity; try lia.
    - tac1; lled; try reflexivity; try lia.
    - tac1; lled; try reflexivity; try lia.
    - destruct n as [|n].
      + apply leqb_no_prop_n_spec; tas.
        intros v Hv.
        simple refine (let HH := constraint_strengthening l l' _ _ H v Hv in _).
        * red. rewrite NoPropLevel.of_to_level; tas.
        * red. rewrite NoPropLevel.of_to_level; tas.
        * clearbody HH. rewrite !Universe.val_make_npl; assumption.
      + tac1; lled; try reflexivity; try lia.
    - tac1; lled; try reflexivity; try lia.
  Qed.


  (* this is function [exists_bigger] of kernel/uGraph.ml *)
  Definition leqb_expr_univ_n n (e1 : UnivExpr.t ) (u : Universe.t) :=
    if UnivExpr.is_prop e1 && (n =? 0) then
      prop_sub_type || Universe.is_prop u
    else
      let '(e2, u) := Universe.exprs u in
      List.fold_left (fun b e2 => leqb_expr_n n e1 e2 || b)
                     u (leqb_expr_n n e1 e2).

  Lemma no_prop_not_zero_le_zero e n :
    UnivExpr.is_prop e && (n =? 0) = false
    -> forall v, (0 <= Z.of_nat n + val v e)%Z.
  Proof.
    intros Hp v. apply andb_false_iff in Hp; destruct Hp as [H|H].
    apply (UnivExpr.is_prop_val_false e) with (v:=v) in H. lia.
    pose proof (UnivExpr.val_minus_one e v).
    destruct n; [discriminate|lia].
  Qed.


  Lemma leqb_expr_univ_n_spec0 n e1 u
    : leqb_expr_univ_n n e1 u
      -> gc_leq_universe_n n uctx.2 (Universe.make' e1) u.
  Proof.
    unfold leqb_expr_univ_n, gc_leq_universe_n; cbn.
    case_eq (UnivExpr.is_prop e1 && (n =? 0)); intro Hp. {
      apply andb_true_iff in Hp; destruct Hp as [He1 Hn].
      apply PeanoNat.Nat.eqb_eq in Hn; subst n; cbn.
      intros H v Hv; apply UnivExpr.is_prop_val with (v:=v) in He1; rewrite He1.
      apply orb_true_iff in H; destruct H as [H|H].
      pose proof (val_minus_one u v); lled; lia.
      apply is_prop_val with (v:=v) in H; lled; lia. }
    intros HH v Hv. rewrite val_fold_right.
    apply no_prop_not_zero_le_zero with (v:=v) in Hp.
    destruct (Universe.exprs u) as [e u'].
    rewrite <- !fold_left_rev_right in HH; cbn in *.
    induction (List.rev u'); cbn in *.
    - apply leqb_expr_n_spec0; tas.
    - apply orb_true_iff in HH. destruct HH as [HH|HH].
      + apply leqb_expr_n_spec0 in HH. specialize (HH v Hv); cbn in HH.
        lled; lia.
      + apply IHl in HH; clear IHl. lled; lia.
  Qed.

  Import Nbar Datatypes.

  (* Non trivial lemma *)
  Lemma gc_leq_universe_n_sup n (l : NoPropLevel.t) b (u : Universe.t)
        (e := UnivExpr.npe (l, b)) :
      gc_level_declared l ->
      gc_levels_declared u ->
      gc_leq_universe_n n uctx.2 (Universe.make' e) u ->
      exists (e' : UnivExpr.t), UnivExprSet.In e' u
            /\ gc_leq_universe_n n uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    intros Hl Hu H.
    assert (HG1 : invariants G) by (subst; exact _).
    assert (HG2 : acyclic_no_loop G) by (subst; exact _).
    assert (Hs : wGraph.s G = lSet) by now subst G.
 
    case_eq (lsp G l lSet).
    (* case where there is a path from l to Set *)
    - intros m Hm. red in H.
      assert (Hl' : forall v, gc_satisfies v uctx.2 -> val v l = 0%Z). {
        intros v Hv. apply make_graph_spec in Hv.
        enough (val v (Universe.make l) <= 0)%Z as HH. {
          rewrite Universe.val_make_npl in HH.
          pose proof (NoPropLevel.val_zero l v); lia. }
        rewrite <- HG in Hv.
        eapply correct_labelling_lsp in Hm; tea.
        cbn in Hm. rewrite val_labelling_of_valuation; lia. }
      assert (UnivExprSet.for_all
                (fun ei => match ei with
                        | UnivExpr.lProp => true
                        | UnivExpr.npe (li, bi) =>
                          le_lt_dec (Some (if bi then 1 else 0)
                                     + Some (if b then 0 else 1)
                                     + lsp G (wGraph.s G) li)
                                    (Some n)
                        end)%nbar
                u = false) as HH. {
        apply not_true_iff_false; intro HH.
        pose proof (lsp_correctness G) as Hlab.
        set (lab := fun x => option_get 0 (lsp G (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv); cbn in H. rewrite Hl' in H; tas.
        subst e; clear Hl' l Hl m Hm Hv.
        apply lle_le in H.
        apply UnivExprSet.for_all_spec in HH; proper.
        apply val_le_caract in H.
        destruct H as [ei [Hei H]]. specialize (HH ei Hei); cbn in HH.
        specialize (Hu ei Hei).
        destruct ei as [|[li bi]]; cbn in *; [destruct b; lia|].
        destruct (lsp_s G li) as [ni Hni].
        { now rewrite HG. }
        rewrite Hni in HH; cbn in HH.
          match goal with
          | H : is_left ?X = true |- _ =>
            destruct X as [HH'|?]; [|discriminate]; clear H
          end.
          assert (val (valuation_of_labelling lab) li = Z.of_nat ni) as XX. {
            rewrite val_valuation_of_labelling; tas.
            subst lab; cbn; now rewrite Hni.
            { red. now rewrite NoPropLevel.of_to_level. } }
          rewrite XX in H; clear Hni XX.
          cbn in H; destruct b, bi; lia. }
      apply UnivExprSet_for_all_false in HH.
      apply UnivExprSet.exists_spec in HH; proper.
      destruct HH as [[|[li bi]] [He' HH]]; [discriminate|].
      eexists; split; tea.
      match goal with
      | H : ~~ ssrbool.is_left ?X = true |- _ =>
        destruct X as [HH'|HH']; try discriminate; clear H
      end.
      cbn in HH'. case_eq (lsp G (wGraph.s G) li).
      2: intros X; rewrite X in HH'; destruct bi, b; contradiction.
      intros nl Hnl v Hv; rewrite Hnl in HH'.
      rewrite (val_labelling_of_valuation' _ li); cbn.
      rewrite (Hl' _ Hv); clear Hl'.
      apply make_graph_spec in Hv; tas. rewrite <- HG in Hv.
      apply (correct_labelling_lsp _ Hnl) in Hv.
      rewrite Hs in Hv; cbn in *.
      destruct bi, b; lled; lia.

    (* case where there is no path from l to Set *)
    - intros HlSet. subst e.
      assert (UnivExprSet.for_all
                (fun ei => match ei with
                        | UnivExpr.lProp => true
                        | UnivExpr.npe (li, bi) =>
                          le_lt_dec (Some (if bi then 1 else 0)
                                     + Some (if b then 0 else 1)
                                     + lsp G l li)
                                    (Some n)
                        end)%nbar
                u = false) as HH. {
        apply not_true_iff_false; intro HH.
        assert (Hl' : VSet.In l (wGraph.V G)). {
          red in Hl; rewrite NoPropLevel.of_to_level in Hl; cbn in Hl;
            now subst G. }
        destruct (lsp_s G _ Hl') as [nl Hnl]; cbn in Hnl.

        assert (exists K, nl <= K /\
                     UnivExprSet.For_all
                       (fun ei => match ei with
                                 | UnivExpr.lProp => True
                                 | UnivExpr.npe (li, bi) =>
                                   match lsp G (wGraph.s G) li with
                                   | None => True
                                   | Some ni => (if bi then 1 else 0) + ni < K
                                   end
                                 end) u) as XX. {
          exists (UnivExprSet.fold
               (fun ei K => match ei with
                         | UnivExpr.lProp => K
                         | UnivExpr.npe (li, bi) =>
                           match lsp G (wGraph.s G) li with
                           | None => K
                           | Some ni => Nat.max K (S
                                                    ((if bi then 1 else 0) + ni))
                           end
                         end) u nl).
          clear -Hu HG HG1. split.
          - rewrite UnivExprSet.fold_spec. rewrite <- fold_left_rev_right.
            induction (List.rev (UnivExprSet.elements u)). reflexivity.
            cbn. destruct a as [|[li bi]]; tas.
            destruct (lsp G (wGraph.s G) li); tas; lia.
          - intros [|[li bi]] Hei; trivial.
            specialize (Hu _ Hei); cbn in Hu.
            destruct (lsp_s G li) as [ni' Hni'].
            { now subst G. }
            rewrite Hni'.
            rewrite UnivExprSet.fold_spec. rewrite <- fold_left_rev_right.
            apply UnivExprSetFact.elements_1, InA_In_eq, in_rev in Hei.
            change (In (UnivExpr.npe (li, bi))
                       (@List.rev UnivExprSet.elt (UnivExprSet.elements u))) in Hei.
            induction (List.rev (UnivExprSet.elements u)); inv Hei.
            + subst a; cbn. rewrite Hni'. lia.
            + specialize (IHl H). cbn. destruct a as [|[li' bi']]; [lia|].
              destruct (lsp G (wGraph.s G) li'); lia. }
        destruct XX as [K [HK1 HK2]].
        assert (Hs' : VSet.In lSet (wGraph.V G)). {
          rewrite <- Hs; apply HG1. }
        set (G' := wGraph.G' G lSet l K) in *.
        assert (HG'1 : invariants G'). {
          subst G'; apply HI'; tas. }
        assert (HG'2 : acyclic_no_loop G'). {
          subst G'; apply HG'; tas. }
        apply correct_labelling_lsp_G' with (K:=K) in HlSet as Hlab; tas.
        fold G' in Hlab; cbn in Hlab.
        set (lab := fun x => option_get 0 (lsp G' (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv); clear Hv.
        rewrite Universe.val_make' in H.
        rewrite val_valuation_of_labelling' in H; tas.

        apply lle_le in H. apply val_le_caract in H.
        destruct H as [ei [Hei H]].
        apply UnivExprSet.for_all_spec in HH; proper.
        specialize (HH _ Hei); cbn in HH.
        specialize (Hu _ Hei).
        destruct ei as [|[li bi]]; cbn in H; [destruct b; lia|].
        rewrite val_valuation_of_labelling in H; tas.
        2:{ red. now rewrite NoPropLevel.of_to_level. }
        match goal with
        | H : is_left ?X = true |- _ =>
          destruct X as [HH'|HH']; try discriminate; clear H
        end.
        assert (lab l = K) as XX. {
          subst lab; cbn. subst G'. rewrite Hs in *.
          rewrite lsp_G'_spec_left; tas. rewrite Hnl.
          unfold lsp. rewrite acyclic_lsp0_xx; tas. cbn; lia. }
        rewrite XX in H; clear XX Hnl Hl Hl'.
        destruct (lsp_s G li) as [ni Hni].
        { now subst G. }
        specialize (HK2 _ Hei); cbn in HK2. rewrite Hni in HK2.

        case_eq (lsp G l li).
        - intros ki Hki. rewrite Hki in HH'; cbn in HH'.
          assert (lab li = K + ki) as XX. {
            subst lab; cbn. subst G'. rewrite Hs in *.
            rewrite lsp_G'_spec_left; tas. rewrite Hki.
            rewrite Hni; cbn; lia. }
          rewrite XX in H. destruct b, bi; cbn in *; lia.

        - intro Hki.
          assert (lab li = ni) as XX. {
            subst lab; cbn. subst G'. rewrite Hs in *.
            rewrite lsp_G'_spec_left; tas. now rewrite Hki, Hni. }
          rewrite XX in H. destruct b, bi; lia. }

    apply UnivExprSet_for_all_false in HH.
    apply UnivExprSet.exists_spec in HH; proper.
    destruct HH as [[|[li bi]] [He' HH]]; [discriminate|].
    eexists; split; tea.
    match goal with
    | H : ~~ is_left ?X = true |- _ =>
      destruct X as [HH'|HH']; try discriminate; clear H
    end.
    cbn in HH'. case_eq (lsp G l li).
    2: intros X; rewrite X in HH'; destruct bi, b; contradiction.
    intros nl Hnl v Hv; rewrite Hnl in HH'.
    apply make_graph_spec in Hv; tas. rewrite <- HG in Hv.
    apply (correct_labelling_lsp _ Hnl) in Hv.
    rewrite !val_labelling_of_valuation'.
    destruct bi, b; cbn in *; lled; lia.
  Qed.

  Lemma leqb_expr_S_n_Prop_Set n e
        (He : gc_expr_declared e)
    : leqb_expr_n (S n) UnivExpr.prop e = leqb_expr_n n UnivExpr.set e.
  Proof.
    destruct e as [|[l []]]; cbnr.
    destruct n; cbnr.
    symmetry. apply leqb_no_prop_n_spec; tas. apply Huctx.
    intros v Hv; cbn.
    destruct l; cbn; lled; lia.
  Qed.

  Lemma leqb_expr_univ_n_spec n e1 u
        (He1 : gc_expr_declared e1)
        (Hu  : gc_levels_declared u)
    : leqb_expr_univ_n n e1 u
      <-> gc_leq_universe_n n uctx.2 (Universe.make' e1) u.
  Proof.
    split; [apply leqb_expr_univ_n_spec0|].
    unfold leqb_expr_univ_n; intro HH.
    case_eq (UnivExpr.is_prop e1 && (n =? 0)); intro Hp. {
      apply andb_true_iff in Hp; destruct Hp as [Hp1 Hn].
      apply PeanoNat.Nat.eqb_eq in Hn; subst n.
      destruct HC as [v0 Hv0]. specialize (HH v0 Hv0); cbn in HH.
      apply UnivExpr.is_prop_val with (v:=v0) in Hp1; rewrite Hp1 in HH.
      lled; cbnr. apply val_is_prop with (v:=v0). lia. }
    case_eq (Universe.exprs u). intros e u' ee.
    assert (Hu': gc_expr_declared e /\ Forall gc_expr_declared u'). {
      split. apply Hu. apply Universe.In_exprs. left. now rewrite ee.
      apply Forall_forall. intros e' He'. apply Hu.
      apply Universe.In_exprs. right. now rewrite ee. }
    (* We replace the Prop+1 case by Set *)
    assert (exists l1 b1 n', let e1' := UnivExpr.npe (l1, b1) in
                        gc_expr_declared e1' /\
                        gc_leq_universe_n n' uctx.2 (Universe.make' e1') u /\
                        fold_left (fun b e2 => leqb_expr_n n e1 e2 || b) u'
                                  (leqb_expr_n n e1 e) =
                        fold_left (fun b e2 => leqb_expr_n n' e1' e2 || b) u'
                                  (leqb_expr_n n' e1' e)) as XX. {
      destruct e1 as [|[l1 b1]]; [|exists l1, b1, n; repeat split; tas].
      destruct n as [|n]; [discriminate|]; clear Hp.
      exists NoPropLevel.lSet, false, n. repeat split.
      - apply Huctx.
      - intros v Hv; specialize (HH v Hv); cbn in *. lled; lia.
      - clear ee u Hu HH. rewrite <- !fold_left_rev_right.
        destruct Hu' as [He Hu']. apply rev_Forall in Hu'.
        induction (List.rev u'); cbn -[leqb_expr_n].
        + apply leqb_expr_S_n_Prop_Set; tas.
        + inv Hu'. f_equal. apply leqb_expr_S_n_Prop_Set; tas.
          apply IHl; tas. }
    clear He1 HH Hp.
    destruct XX as [l1 [b1 [n' [He1 [HH XX]]]]]; rewrite XX; clear XX e1.
    apply gc_leq_universe_n_sup in HH; tas.
    2:{ red. now rewrite NoPropLevel.of_to_level. }
    destruct HH as [e' [He' HH]]. apply leqb_expr_n_spec in HH; tas.
    2:{ now apply Hu. }
    apply Universe.In_exprs in He'. rewrite ee in He'; cbn in He'.
    rewrite <- !fold_left_rev_right.
    clear -He' HH. destruct He' as [H|H]; [subst|].
    - induction (List.rev u'); tas. cbn -[leqb_expr_n]. now rewrite IHl, orb_true_r.
    - apply In_rev in H. change (@In UnivExpr.t e' (List.rev u')) in H.
      induction (List.rev u'); tas; cbn -[leqb_expr_n]; invs H.
      now rewrite HH. now rewrite IHl, orb_true_r.
  Qed.


  (* this is function [real_check_leq] of kernel/uGraph.ml *)
  Definition leqb_universe_n n (u1 u2 : Universe.t) :=
    if Universe.is_prop u1 && (n =? 0) then
      prop_sub_type || Universe.is_prop u2
    else
      let '(e1, u1) := Universe.exprs u1 in
      List.fold_left (fun b e1 => ((UnivExpr.is_prop e1 && (n =? 0))
                                || leqb_expr_univ_n n e1 u2) && b)
                     u1 ((UnivExpr.is_prop e1 && (n =? 0))
                         || leqb_expr_univ_n n e1 u2).

  Lemma no_prop_not_zero_le_zero' u n :
    Universe.is_prop u && (n =? 0) = false
    -> forall v, (0 <= Z.of_nat n + val v u)%Z.
  Proof.
    intros Hp v. apply andb_false_iff in Hp; destruct Hp as [H|H].
    apply (is_prop_val_false u) with (v:=v) in H. lia.
    pose proof (val_minus_one u v).
    destruct n; [discriminate|lia].
  Qed.

  Lemma leqb_universe_n_spec0 n u1 u2
    : leqb_universe_n n u1 u2 -> gc_leq_universe_n n uctx.2 u1 u2.
  Proof.
    unfold leqb_universe_n, gc_leq_universe_n.
    case_eq (Universe.is_prop u1 && (n =? 0)); intro Hp. {
      intros H v Hv.
      apply andb_true_iff in Hp; destruct Hp as [Hu1 Hn].
      apply PeanoNat.Nat.eqb_eq in Hn; subst n.
      apply is_prop_val with (v:=v) in Hu1; rewrite Hu1; cbn.
      apply orb_true_iff in H; destruct H as [H|H].
      pose proof (val_minus_one u2 v); lled; lia.
      apply is_prop_val with (v:=v) in H; now rewrite H. }
    intros HH v Hv.
    apply no_prop_not_zero_le_zero' with (v:=v) in Hp.
    rewrite (val_fold_right u1) in *.
    destruct (Universe.exprs u1) as [e1 u1']; clear u1.
    rewrite <- !fold_left_rev_right in *; cbn in *.
    induction (List.rev u1'); cbn in *.
    - apply orb_true_iff in HH; destruct HH as [H|H].
      + exfalso. apply andb_true_iff in H; destruct H as [He1 Hn].
        apply UnivExpr.is_prop_val with (v:=v) in He1.
        destruct n; [|discriminate]. lia.
      + apply leqb_expr_univ_n_spec0 in H. specialize (H v Hv); cbn in H.
        lled; lia.
    - set (z := (fold_right (fun e x => Z.max (val v e) x) (val v e1) l)) in *.
      apply andb_true_iff in HH; destruct HH as [H HH].
      apply orb_true_iff in H; destruct H as [Han|H].
      + assert (ee : Z.max (val v a) z = z). {
          apply andb_true_iff in Han; destruct Han as [Ha Hn].
          apply UnivExpr.is_prop_val with (v:=v) in Ha.
          destruct n; [|discriminate]. lia. }
        rewrite ee in *; clear ee. apply IHl; tas.
      + apply leqb_expr_univ_n_spec0 in H. specialize (H v Hv). cbn in H.
        destruct (Z.max_dec (val v a) z) as [ee|ee]; rewrite ee in *.
        * lled; lia.
        * apply IHl; tas.
  Qed.

  Lemma leqb_universe_n_spec n u1 u2
        (Hu1  : gc_levels_declared u1)
        (Hu2  : gc_levels_declared u2)
    : leqb_universe_n n u1 u2
      <-> gc_leq_universe_n n uctx.2 u1 u2.
  Proof.
    split; [apply leqb_universe_n_spec0|].
    unfold leqb_universe_n; intro HH.
    case_eq (Universe.is_prop u1 && (n =? 0)); intro Hp. {
      toProp Hp as [Hp1 Hp2]. toProp Hp2; subst n.
      destruct HC as [v0 Hv0]. specialize (HH v0 Hv0); cbn in HH.
      apply is_prop_val with (v:=v0) in Hp1; rewrite Hp1 in HH.
      lled; cbnr. apply val_is_prop with (v:=v0). lia. }

    case_eq (Universe.exprs u1); intros e1 uu1 Huu1.
    rewrite (fold_left_andb_forallb (fun e => _)).
    pose proof (Universe.exprs_spec' u1) as X; rewrite Huu1 in X; cbn in X.
    rewrite X. apply forallb_Forall. apply Forall_forall.
    intros ei Hei.
    case_eq (UnivExpr.is_prop ei && (n =? 0)); cbnr; intro Hpi.
    apply InA_In_eq, UnivExprSetFact.elements_2 in Hei.
    specialize (Hu1 _ Hei).
    eapply leqb_expr_univ_n_spec; tas.
    intros v Hv. specialize (HH v Hv). rewrite Universe.val_make'.
    apply no_prop_not_zero_le_zero with (v:=v) in Hpi.
    apply lle_le in HH. apply le_lle'; tas.
    apply Z.le_add_le_sub_l. apply Z.le_add_le_sub_l in HH.
    eapply (val_ge_caract u1 v (val v u2 - Z.of_nat n)%Z).p2 in HH; tea.
  Qed.



  Definition check_leqb_universe (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (prop_sub_type && Universe.is_prop u1)
    || Universe.eqb u1 u2
    || leqb_universe_n 0 u1 u2.

  Lemma check_leqb_universe_spec u1 u2
        (Hu1  : gc_levels_declared u1)
        (Hu2  : gc_levels_declared u2)
    : check_leqb_universe u1 u2 <-> gc_leq_universe uctx.2 u1 u2.
  Proof.
    unfold check_leqb_universe, gc_leq_universe.
    destruct check_univs; split; cbn; trivial; intro H.
    - toProp H as [H|H]; [|now apply leqb_universe_n_spec0].
      toProp H as [H|H].
      + toProp H as [H1 H2].
        intros v Hv. rewrite is_prop_val; tas.
        apply le_lle; tas. apply val_minus_one.
      + apply eqb_true_iff in H; subst. intros v Hv; reflexivity.
    - apply leqb_universe_n_spec in H; tas. rewrite H.
      now rewrite orb_true_r.
  Qed.

  Definition check_eqb_universe (u1 u2 : Universe.t) :=
    ~~ check_univs
    || Universe.eqb u1 u2
    || (leqb_universe_n 0 u1 u2 && leqb_universe_n 0 u2 u1).

  Lemma check_eqb_universe_spec u1 u2
        (Hu1  : gc_levels_declared u1)
        (Hu2  : gc_levels_declared u2)
    : check_eqb_universe u1 u2 <-> gc_eq_universe uctx.2 u1 u2.
  Proof.
    unfold check_eqb_universe, gc_eq_universe.
    destruct check_univs; split; cbn; trivial; intro H.
    - toProp H as [H|H].
      + apply eqb_true_iff in H; subst. intros v Hv; reflexivity.
      + toProp H as [H1 H2].
        apply leqb_universe_n_spec0 in H1. apply leqb_universe_n_spec0 in H2.
        intros v Hv. specialize (H1 v Hv); specialize (H2 v Hv).
        lled; lia.
    - toProp; right.
      toProp; apply leqb_universe_n_spec; tas; intros v Hv; specialize (H v Hv); lled; lia.
  Qed.

  Lemma check_eqb_universe_refl :
    forall u, check_eqb_universe u u.
  Proof.
    intro u. unfold check_eqb_universe.
    rewrite Universe.eqb_refl.
    rewrite ssrbool.orbT. reflexivity.
  Qed.

  Definition check_gc_constraint (gc : GoodConstraint.t) :=
    negb check_univs || match gc with
                       | gc_le l l' => leqb_no_prop_n 0 l l'
                       | gc_lt l l' => leqb_no_prop_n 1 l l'
                       | gc_lt_set n => leqb_no_prop_n 1 lSet (Var n)
                       | gc_eq_set n => leqb_no_prop_n 0 (Var n) lSet
                       end.

  Definition check_gc_constraints
    := GoodConstraintSet.for_all check_gc_constraint.

  Definition check_constraints ctrs :=
    match gc_of_constraints ctrs with
    | Some ctrs => check_gc_constraints ctrs
    | None => false
    end.

  Lemma check_gc_constraint_spec gc
    : check_gc_constraint gc
      -> if check_univs then forall v, gc_satisfies v uctx.2 -> gc_satisfies0 v gc else True.
  Proof.
    unfold check_gc_constraint. destruct check_univs; [cbn|trivial].
    destruct gc as [l l'|l l'|n|n].
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn in *. toProp.
      pose proof (val_level_of_variable_level v l).
      pose proof (val_level_of_variable_level v l').
      destruct l, l'; cbn in *; lled; lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn -[Z.of_nat] in HH. unfold gc_satisfies0. toProp.
      pose proof (val_level_of_variable_level v l) as H1.
      pose proof (val_level_of_variable_level v l') as H2.
      cbn in *. rewrite !UnivExpr.val_make_npl in *.
      rewrite NoPropLevel.val_to_level in *.
      rewrite H1, H2 in HH. clear -HH. lled; lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
  Qed.

  Lemma check_gc_constraints_spec ctrs
    : check_gc_constraints ctrs
      -> if check_univs then forall v, gc_satisfies v uctx.2 -> gc_satisfies v ctrs else True.
  Proof.
    pose proof check_gc_constraint_spec as XX.
    unfold check_gc_constraint. destruct check_univs; [cbn|trivial].
    intros HH v Hv.
    apply GoodConstraintSet.for_all_spec. now intros x y [].
    apply GoodConstraintSet.for_all_spec in HH. 2: now intros x y [].
    intros gc Hgc. specialize (HH gc Hgc).
    apply XX; assumption.
  Qed.

  Definition eqb_univ_instance (u1 u2 : Instance.t) : bool
    := forallb2 (fun l1 l2 => check_eqb_universe
                             (Universe.make l1) (Universe.make l2)) u1 u2.

End CheckLeq.





(* This section: specif in term of raw uctx *)
Section CheckLeq2.
  Context {cf:checker_flags}.

  Definition is_graph_of_uctx G uctx
    := on_Some (fun uctx => make_graph uctx = G) (gc_of_uctx uctx).

  Context (G : universes_graph)
          uctx (Huctx: global_uctx_invariants uctx) (HC : consistent uctx.2)
          (HG : is_graph_of_uctx G uctx).

  Let uctx' : VSet.t × GoodConstraintSet.t.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    exact (no_prop_levels uctx.1, ctrs).
    contradiction HG.
  Defined.

  Let Huctx': global_gc_uctx_invariants uctx'.
    subst uctx'; cbn.
    eapply gc_of_uctx_invariants; tea.
    unfold is_graph_of_uctx, gc_of_uctx in *. cbn.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    reflexivity. contradiction HG.
  Qed.

  Let HC' : gc_consistent uctx'.2.
    subst uctx'; cbn. clear Huctx'.
    apply gc_consistent_iff in HC.
    unfold is_graph_of_uctx, gc_of_uctx in *.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    exact HC. contradiction HG.
  Qed.

  Let HG' : G = make_graph uctx'.
    subst uctx'; cbn. clear Huctx'.
    unfold is_graph_of_uctx, gc_of_uctx in *.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    symmetry; exact HG. contradiction HG.
  Qed.

  Let level_declared (l : Level.t) := LevelSet.In l uctx.1.

  Let expr_declared (e : UnivExpr.t)
    := on_Some_or_None (fun l : NoPropLevel.t => level_declared l)
                       (UnivExpr.get_noprop e).

  Let levels_declared (u : Universe.t)
    := UnivExprSet.For_all expr_declared u.

  Lemma level_gc_declared_declared l
    : level_declared l -> gc_level_declared uctx' l.
  Proof.
    clear. subst uctx'.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2); [|contradiction HG].
    cbn; clear HG. unfold level_declared, gc_level_declared; cbn.
    destruct l; cbn; trivial; intro;
      now apply no_prop_levels_no_prop_level.
  Qed.

  Lemma expr_gc_declared_declared e
    : expr_declared e -> gc_expr_declared uctx' e.
  Proof.
    destruct e as [|[l b]]; cbn; trivial.
    intro; apply (level_gc_declared_declared l) in H.
    red in H. now rewrite NoPropLevel.of_to_level in H.
  Qed.

  Lemma levels_gc_declared_declared u
    : levels_declared u -> gc_levels_declared uctx' u.
  Proof.
    unfold levels_declared, gc_levels_declared.
    intros HH e He; specialize (HH e He).
    now apply expr_gc_declared_declared.
  Qed.

  Lemma leqb_univ_expr_n_spec' n e1 u
        (He1 : expr_declared e1)
        (Hu : levels_declared u)
    : leqb_expr_univ_n G n e1 u
      <-> leq_universe_n n uctx.2 (Universe.make' e1) u.
  Proof.
    etransitivity.
    apply (leqb_expr_univ_n_spec G uctx' Huctx' HC' HG'); tas.
    - apply expr_gc_declared_declared; tas.
    - apply levels_gc_declared_declared; tas.
    - symmetry. etransitivity. apply gc_leq_universe_n_iff.
      subst uctx'; cbn; clear -HG.
      unfold is_graph_of_uctx, gc_of_uctx in *.
      destruct (gc_of_constraints uctx.2) as [ctrs|].
      reflexivity. contradiction HG.
  Qed.

  (* todo complete *)
  Lemma check_leqb_universe_spec' u1 u2
    : check_leqb_universe G u1 u2 -> leq_universe uctx.2 u1 u2.
  Proof.
    unfold check_leqb_universe, leq_universe.
    destruct check_univs; cbn; [|trivial].
    case_eq (prop_sub_type && Universe.is_prop u1). {
      intros e _ v Hv. toProp e as [Hp Hu1].
      rewrite (is_prop_val _ Hu1 v). apply le_lle; tas.
      apply val_minus_one. }
    intros _.
    case_eq (Universe.eqb u1 u2). {
      intros e _ v Hv. apply eqb_true_iff in e. now destruct e. }
    intros _; cbn.
    intro H; unshelve eapply (leqb_universe_n_spec0 G uctx' Huctx' HC' HG'
                                                    _ _ _) in H.
    eapply gc_leq_universe_n_iff.
    unfold uctx' in H.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2). cbn in *. exact H.
    exact I.
  Qed.

  Lemma check_eqb_universe_spec' u1 u2
    : check_eqb_universe G u1 u2 -> eq_universe uctx.2 u1 u2.
  Proof.
    unfold check_eqb_universe, eq_universe.
    destruct check_univs; cbn; [|trivial].
    case_eq (Universe.eqb u1 u2). {
      intros e _ v Hv. apply eqb_true_iff in e. now destruct e. }
    intros _; cbn.
    intro H. apply andb_prop in H. destruct H as [H1 H2].
    unshelve eapply (leqb_universe_n_spec0 G uctx' Huctx' HC' HG' _ _ _) in H1.
    unshelve eapply (leqb_universe_n_spec0 G uctx' Huctx' HC' HG'
                                           _ _ _) in H2.
    unfold uctx' in H1, H2.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    apply eq_leq_universe.
    split; eapply gc_leq_universe_n_iff;
      (destruct (gc_of_constraints uctx.2); [cbn in *|contradiction HG]); tas.
  Qed.
  
  Lemma eq_universe_spec' u1 u2 :
    levels_declared u1 ->
    levels_declared u2 ->
    eq_universe uctx.2 u1 u2 ->
    check_eqb_universe G u1 u2.
  Proof.
    intros decl1 decl2.
    apply levels_gc_declared_declared in decl1.
    apply levels_gc_declared_declared in decl2.
    rewrite gc_eq_universe_iff.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    intros eq.
    apply <- check_eqb_universe_spec; eauto.
    exact eq.
  Qed.

  (* todo complete *)
  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints uctx.2 ctrs.
  Proof.
    unfold check_constraints, valid_constraints.
    case_eq (gc_of_constraints ctrs); [|discriminate].
    intros ctrs' Hctrs' HH.
    eapply (check_gc_constraints_spec _ uctx' Huctx' HC' HG') in HH.
    destruct check_univs; cbn; [|trivial].
    intros v Hv.
    apply gc_of_constraints_spec.
    apply gc_of_constraints_spec in Hv.
    rewrite Hctrs'; cbn. apply HH.
    clear -HG Hv.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    now destruct (gc_of_constraints uctx.2).
  Qed.
End CheckLeq2.



(* If I would restart: *)
(*   - maybe use nat everywhere instead of Z and Pos *)
(*   - maybe not put Prop in UnivExprs but in Universes only *)
(*   - more generally keep the graph closer to the spec (valuation = labelling ?)
       but the the quoting is more complicated ... *)
