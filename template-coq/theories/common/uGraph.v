(* Distributed under the terms of the MIT license. *)
Require Import ssrbool MSetWeakList MSetFacts MSetProperties.
From MetaCoq.Template Require Import utils config Universes wGraph.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Import ConstraintType.

Import MCMonadNotation.

Arguments Z.add : simpl nomatch.
Arguments Nat.leb : simpl nomatch.
Arguments Nat.eqb : simpl nomatch.

Definition Z_of_bool (b : bool) : Z :=
  match b with
  | true => 1
  | false => 0
  end.
Notation "⎩ b ⎭" := (Z_of_bool b).

Derive NoConfusion for universes.

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
      rewrite H in H0. discriminate. intuition.
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

  Definition to_noprop (l : t) : Level.t :=
    match l with
    | Level s => Level.Level s
    | Var n => Level.Var n
    end.

  Definition to_level (l : t) : Level.t := to_noprop l.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | Level s => Pos.to_nat (v.(valuation_mono) s)
               | Var x => (v.(valuation_poly) x)
               end.
End VariableLevel.

Coercion VariableLevel.to_noprop : VariableLevel.t >-> Level.t.


Module GoodConstraint.
  Inductive t_ :=
  (* l + z <= l' *)
  | gc_le : VariableLevel.t -> Z -> VariableLevel.t -> t_
  (* Set + k < Level n *)
  | gc_lt_set_level : nat -> string -> t_
  (* Set + k <= Var n *)
  | gc_le_set_var : nat -> nat -> t_
  (* Level n <= Set + k *)
  | gc_le_level_set : string -> nat -> t_
  (* Var n <= Set + k *)
  | gc_le_var_set : nat -> nat -> t_.
  Definition t : Set := t_.
  Definition eq : t -> t -> Prop := Logic.eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. all: try apply VariableLevel.eq_dec.
    apply Z.eq_dec. all:apply string_dec || apply Peano_dec.eq_nat_dec.
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
  | gc_le l z l' => (Z.of_nat (val v l) <=? Z.of_nat (val v l') - z)%Z
  | gc_lt_set_level k l => k <? Pos.to_nat (v.(valuation_mono) l)
  | gc_le_set_var k l => k <=? v.(valuation_poly) l
  | gc_le_level_set l k => Pos.to_nat (v.(valuation_mono) l) <=? k
  | gc_le_var_set l k => v.(valuation_poly) l <=? k
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
     (* Set _ _ *)
     | (Level.lSet, Le z, r) => 
      match Z.compare z 0 with
      | Datatypes.Eq => empty
      | Datatypes.Lt => (* Set <= l + n *) empty
      | Datatypes.Gt => (* Set + n <= l *) 
        match r with
        | Level.lSet => None
        | Level.Level s => singleton (gc_lt_set_level (Z.to_nat (z - 1)) s)
        | Level.Var n => singleton (gc_le_set_var (Z.to_nat z) n)
        end
      end
     | (Level.lSet, Eq, Level.lSet) => empty
     | (Level.lSet, Eq, Level.Level _) => None
     | (Level.lSet, Eq, Level.Var n) => singleton (gc_le_var_set n 0%nat)

     (* Level _ _ *)
     | (Level.Level l, Le z, Level.lSet) => 
       (* l - n <= Set <-> l <= Set + n *)
        if (z <=? 0)%Z then singleton (gc_le_level_set l (Z.to_nat (Z.abs z)))
        else None
     
     | (Level.Level l, Le z, Level.Level l')
       => singleton (gc_le (Level l) z (Level l'))
     | (Level.Level l, Le z, Level.Var n) => singleton (gc_le (Level l) z (Var n))
     | (Level.Level _, Eq, Level.lSet) => None
     | (Level.Level l, Eq, Level.Level l')
       => pair (gc_le (Level l) 0 (Level l')) (gc_le (Level l') 0 (Level l))
     | (Level.Level l, Eq, Level.Var n)
       => pair (gc_le (Level l) 0 (Var n)) (gc_le (Var n) 0 (Level l))

     (* Var _ _ *)
     | (Level.Var n, Le z, Level.lSet) => 
      (* l - n <= Set <-> l <= Set + n *)
      if (z <=? 0)%Z then singleton (gc_le_var_set n (Z.to_nat (Z.abs z)))
      else None

     | (Level.Var n, Le z, Level.Level l) => singleton (gc_le (Var n) z (Level l))
     | (Level.Var n, Le z, Level.Var n') => singleton (gc_le (Var n) z (Var n'))
     | (Level.Var n, Eq, Level.lSet) => singleton (gc_le_var_set n 0)
     | (Level.Var n, Eq, Level.Level l)
       => pair (gc_le (Var n) 0%Z (Level l)) (gc_le (Level l) 0%Z (Var n))

     | (Level.Var n, Eq, Level.Var n')
       => pair (gc_le (Var n) 0 (Var n')) (gc_le (Var n') 0 (Var n))
     end.

Section GC.

Context `{cf : checker_flags}.

Lemma gc_satisfies_singleton v c :
  gc_satisfies0 v c <->
  gc_satisfies v (GoodConstraintSet.singleton c).
Proof.
  split.
  - intros H; unfold gc_satisfies.
    eapply GoodConstraintSet.for_all_spec; auto. proper.
    intros x xin. eapply GoodConstraintSet.singleton_spec in xin.
    now subst.
  - unfold gc_satisfies.
    intros gc.
    eapply GoodConstraintSet.for_all_spec in gc; auto. 2:proper.
    specialize (gc c). 
    rewrite -> GoodConstraintSet.singleton_spec in gc.
    now apply gc.
Qed.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (gc_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1; destruct l, l'; try constructor.
    all: cbn -[GoodConstraintSet_pair] in *.
    all: lled; cbn -[GoodConstraintSet_pair]; try reflexivity.
    all: rewrite ?if_true_false; repeat toProp ; try lia.
    all: try solve [destruct (Z.compare_spec z 0); simpl; try constructor; lia].
    destruct (Z.compare_spec z 0); simpl; try constructor; try lia.
    apply gc_satisfies_singleton.
    simpl. apply Nat.ltb_lt. lia.
    all:try (destruct (Z.compare_spec z 0); simpl; try constructor; try lia;
    apply gc_satisfies_singleton; simpl; try (apply Nat.ltb_lt||apply Nat.leb_le); lia).
    all:try (destruct (Z.leb_spec z 0); simpl; try constructor; try lia;
      apply gc_satisfies_singleton; simpl; apply Nat.leb_le; lia).
    all: apply gc_satisfies_pair; split; cbn; toProp; try lia.
  - destruct uc as [[[] []] []]; intro H; constructor.
    all: cbn -[GoodConstraintSet_pair] in *; try contradiction.
    all: rewrite -> ?if_true_false in *; lled; cbn -[GoodConstraintSet_pair] in *;
      try contradiction; repeat toProp; try lia.
    all:try (destruct (Z.compare_spec z 0); simpl in H; auto; try lia;
      apply gc_satisfies_singleton in H; simpl in H; 
      (apply Nat.ltb_lt in H || apply Nat.leb_le in H);
      try lia).
    all:try (destruct (Z.leb_spec z 0); simpl in H; auto; try lia;
      apply gc_satisfies_singleton in H; simpl in H; 
      (apply Nat.ltb_lt in H || apply Nat.leb_le in H);
      try lia).
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
      intros X HX; rewrite HX in HH; cbn in HH.
      apply IHl. split.
      * intros uc H0. apply H1. now apply InA_cons_tl.
      * intros gc H0. apply GoodConstraintSetFact.union_1 in H0.
        induction H0. intuition.
        apply GoodConstraintSetFact.for_all_2 in HH.
        apply HH. assumption.
        intros x y []; reflexivity.
    + intros HH.
      case_eq (gc_of_constraint a).
      * intros X HX; rewrite HX in HH; cbn in HH.
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

Local Open Scope univ_scope.

Definition gc_leq_universe_n n ctrs (u u' : Universe.t)
  := forall v, gc_satisfies v ctrs -> ⟦ u ⟧_v <_n ⟦u'⟧_v.

Definition gc_eq_universe0 φ (u u' : Universe.t) :=
  forall v, gc_satisfies v φ -> ⟦ u ⟧_v = ⟦ u' ⟧_v.

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
    + intros ctrs' e. cbn. intros v Hv.
      apply H. apply gc_of_constraints_spec.
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

Lemma gc_leq_universe_0_iff ctrs u u':
  leq_universe0 ctrs u u'
  <-> on_Some_or_None (fun ctrs => gc_leq_universe_n 0 ctrs u u')
                      (gc_of_constraints ctrs).
Proof.
  rewrite leq_universe0_leq_universe_n.
  apply gc_leq_universe_n_iff.
Qed.


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
  apply gc_leq_universe_0_iff.
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

Module Import wGraph := WeightedGraph Level LevelSet.
Module VSet := LevelSet.
Local Notation lSet := Level.lSet.
(* vtn = variable to noprop *)
Local Notation vtn := VariableLevel.to_noprop.

Definition universes_graph := t.
Definition init_graph : universes_graph
  := (VSet.singleton lSet, EdgeSet.empty, lSet).

Lemma init_graph_invariants : invariants init_graph.
Proof.
  repeat split; cbn in *.
  1-2: inversion H. sets.
  apply VSet.singleton_spec in H. subst.
  exists (paths_refl _ _). simpl. sq. lia.
Defined.

Definition declared : Level.t -> LevelSet.t -> Prop := LevelSet.In.

Definition uctx_invariants (uctx : ContextSet.t)
  := ConstraintSet.For_all (fun '(l, _, l') => declared l uctx.1 /\ declared l' uctx.1)
                           uctx.2.

Definition global_uctx_invariants (uctx : ContextSet.t)
  := LevelSet.In Level.lSet uctx.1 /\ uctx_invariants uctx.

Definition global_gc_uctx_invariants (uctx : VSet.t * GoodConstraintSet.t)
  := VSet.In lSet uctx.1 /\ GoodConstraintSet.For_all (fun gc => match gc with
                 | gc_le l z l' => VSet.In (vtn l) uctx.1
                                 /\ VSet.In (vtn l') uctx.1
                 | gc_lt_set_level _ n
                 | gc_le_level_set n _ => VSet.In (Level.Level n) uctx.1
                 | gc_le_var_set n _
                 | gc_le_set_var _ n => VSet.In (Level.Var n) uctx.1
                 end) uctx.2.

Definition gc_of_uctx `{checker_flags} (uctx : ContextSet.t)
  : option (VSet.t * GoodConstraintSet.t)
  := ctrs <- gc_of_constraints uctx.2 ;;
     ret (uctx.1, ctrs).

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
  - apply Hi0.
  - red in Hi.
    destruct uctx as [levels ctrs0]; cbn in *.
    intros gc Hgc.
    eapply gc_of_constraint_iff in Hgc; tea.
    destruct Hgc as [e [He HH]].
    specialize (Hi e He); cbn in Hi.
    clear -Hi HH.
    destruct e as [[l ct] l']; simpl in Hi.
    destruct l, ct, l'; cbn in HH; destruct prop_sub_type; cbn in HH.
    change VSet.In with LevelSet.In.
    all:repeat match goal with
         | HH : context [ (?z ?= 0)%Z ] |- _ => 
          destruct (Z.compare_spec z 0); simpl in HH; auto
          | HH : context [ (?z <=? 0)%Z ] |- _ => 
          destruct (Z.leb_spec z 0); simpl in HH; auto
         | HH : False |- _ => contradiction HH
         | HH : GoodConstraintSet.In ?A GoodConstraintSet.empty |- _
           => apply GoodConstraintSetFact.empty_iff in HH; contradiction HH
         | HH : GoodConstraintSet.In ?A (GoodConstraintSet.singleton ?B) |- _
           => apply GoodConstraintSetFact.singleton_1 in HH; subst gc
         | HH : GoodConstraintSet.In ?A (GoodConstraintSet_pair ?B _) |- _
           => apply GoodConstraintSet_pair_In in HH; destruct HH as [HH|HH]; subst gc
         end.
    all: try split; try apply Hi;
      try apply Hi.
Qed.

Definition edge_of_level (l : VariableLevel.t) : EdgeSet.elt :=
  match l with
  | Level l => (lSet, 1%Z, Level.Level l)
  | Var n => (lSet, 0%Z, Level.Var n)
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edge_of_constraint (gc : GoodConstraint.t) : EdgeSet.elt :=
  match gc with
  | gc_le l z l' => (vtn l, z, vtn l')
  | gc_lt_set_level k s => (lSet, Z.of_nat (S k), vtn (Level s)) 
  | gc_le_set_var k n => (lSet, Z.of_nat k, vtn (Var n))
  | gc_le_level_set s k => (vtn (Level s), (- Z.of_nat k)%Z, lSet)
  | gc_le_var_set n k => (vtn (Var n), (- Z.of_nat k)%Z, lSet)
  end.


Lemma source_edge_of_level g : (edge_of_level g)..s = lSet.
Proof.
  destruct g; reflexivity.
Qed.

Lemma target_edge_of_level g : (edge_of_level g)..t = vtn g.
Proof.
  destruct g; reflexivity.
Qed.

Definition variable_of_level (l : Level.t) : option VariableLevel.t
  := match l with
      | Level.lSet => None
      | Level.Level s => Some (VariableLevel.Level s)
      | Level.Var n => Some (VariableLevel.Var n)
      end.

Definition option_edge_of_level l : option EdgeSet.elt :=
  match variable_of_level l with
  | None => None
  | Some ll => Some (edge_of_level ll)
  end.

Definition add_level_edges :=
  VSet.fold
  (fun l E =>
      match variable_of_level l with
      | None => E
      | Some ll => EdgeSet.add (edge_of_level ll) E
      end).

Lemma edgeset_equal s s' : EdgeSet.Equal s s' -> s = s'.
Proof.
  intros Heq; now apply EdgeSet.eq_leibniz.
Qed.

Definition add_cstrs ctrs := 
  GoodConstraintSet.fold (fun ctr => EdgeSet.add (edge_of_constraint ctr)) ctrs.

Lemma add_cstrs_spec e x g : 
  EdgeSet.In e (add_cstrs x g) <->
  (exists c, edge_of_constraint c = e /\ GoodConstraintSet.In c x) \/ EdgeSet.In e g.
Proof.
  rewrite /add_cstrs GoodConstraintSet.fold_spec.
  transitivity 
    ((exists c, edge_of_constraint c = e /\ In c (GoodConstraintSet.elements x)) \/ EdgeSet.In e g).
  - induction (GoodConstraintSet.elements x) in g |- *; simpl.
    intuition auto. now destruct H0 as [c [_ F]].
    rewrite IHl.
    rewrite EdgeSet.add_spec.
    split.
    * intros [[c [eq inl]]|?].
      subst e. firstorder auto.
      destruct H as [->|ing]; [left|right]; auto.
      exists a; firstorder auto.
    * intros [[c [eq [->|inl]]]|?]; auto.
      left; exists c; auto.
  - setoid_rewrite (GoodConstraintSetFact.elements_iff x).
    now setoid_rewrite InA_In_eq.
Qed.

#[global] Instance add_cstrs_proper : Proper (GoodConstraintSet.Equal ==> Logic.eq ==> Logic.eq)%signature add_cstrs.
Proof.
  intros s s' eq x y ->.
  eapply wGraph.EdgeSet.eq_leibniz.
  intro e.
  rewrite !add_cstrs_spec.
  firstorder auto.
Qed.

Definition make_graph (uctx : VSet.t * GoodConstraintSet.t) : t :=
  let init_edges := add_level_edges uctx.1 EdgeSet.empty in
  let edges := add_cstrs  uctx.2 init_edges in
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
    unfold add_level_edges; rewrite VSet.fold_spec. generalize EdgeSet.empty.
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
  split.
  - intros e He. apply make_graph_E in He.
    destruct He as [[l [Hl He]]|[gc [Hgc He]]].
    + subst e. split. rewrite source_edge_of_level. apply Hi.
      rewrite target_edge_of_level; tas.
    + subst e. split. destruct gc; try apply (Hi.p2 _ Hgc). apply Hi.
      simpl. apply Hi.
      destruct gc; try apply (Hi.p2 _ Hgc). apply Hi.
      simpl. apply Hi.
  - apply Hi.
  - cbn. intros l Hl. sq. destruct l.
    exists (paths_refl _ _). sq. simpl. reflexivity.
    assert (He: EdgeSet.In (edge_of_level (Level s)) (wGraph.E (make_graph uctx))). {
      apply make_graph_E. left. exists (Level s). intuition. }
    unshelve eexists _.
    econstructor. 2: constructor. 
    eexists; exact He. simpl. sq; lia.
    assert (He: EdgeSet.In (edge_of_level (Var n)) (wGraph.E (make_graph uctx))). {
      apply make_graph_E. left. exists (Var n). intuition. }
    unshelve eexists _.
    econstructor. 2: constructor. 
    eexists; exact He. simpl. sq; auto. lia.
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
           | Level.Level l => Pos.to_nat (v.(valuation_mono) l)
           | Level.Var n => (v.(valuation_poly) n)
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
      assert (HH: EdgeSet.In (lSet, Z.of_nat 1, vtn (Level s)) (wGraph.E G)). {
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
        destruct ctr as [[] z []|[] []| |n|n]; cbn in *; toProp H; try lia.
        all:try destruct t0; cbn in *; try lia.
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (proj2 (make_graph_E uctx (edge_of_constraint gc))
                        (or_intror (ex_intro _ gc (conj Hgc eq_refl)))) as XX.
      specialize (H.p2 _ XX).
      destruct gc as [[] z []|k ?| |n|n]; intro HH; cbn in *; toProp; try lia.
  Qed.

  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) uctx.2 <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) uctx.2.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling. intuition.
    rewrite !valuation_labelling_eq; tas. 3:now apply H.
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
Global Existing Instance gc_of_uctx_invariants.

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
  pose proof (gc_of_uctx_invariants uctx (uctx.1, ctrs)) as XX.
  cbn in XX; rewrite Hctrs in XX; specialize (XX eq_refl Huctx).
  etransitivity. apply make_graph_invariants in XX.
  etransitivity. apply is_acyclic_spec; tas.
  apply acyclic_caract1; tas.
  symmetry; apply (make_graph_spec2 (uctx.1, ctrs)); tas.
Qed.


(* This section: specif in term of gc_uctx *)
Section CheckLeq.
  Context {cf:checker_flags}.

  Context (G : universes_graph)
          uctx (Huctx: global_gc_uctx_invariants uctx) (HC : gc_consistent uctx.2)
          (HG : G = make_graph uctx).

  Definition on_inl {A B : Type} (P : A -> Prop) (x : A + B) :=
    match x with
    | inl x0 => P x0
    | inr _ => True
    end.

  
  Definition gc_level_declared l
    := VSet.In l uctx.1.

  Lemma gc_level_declared_make_graph (l : Level.t) :
    gc_level_declared l -> VSet.In l (wGraph.V G).
  Proof.
    intros Hl;subst;assumption.
  Qed.

  Definition gc_expr_declared e
    := on_Some_or_None (fun l => VSet.In l uctx.1) (UnivExpr.get_noprop e).

  Definition gc_levels_declared (u : Universe.nonEmptyUnivExprSet)
    := UnivExprSet.For_all gc_expr_declared u.

  Definition gc_levels_declared_univ (u : Universe.t)
    := match u with
       | Universe.lSProp | Universe.lProp => True
       | Universe.lType l => gc_levels_declared l
       end.

  Lemma val_level_of_variable_level v (l : VariableLevel.t)
    : val v (l : Level.t) = val v l.
  Proof.
    destruct l; cbn; lia.
  Qed.

  Local Open Scope univ_scope.

  Lemma val_labelling_of_valuation v (l : Level.t)
    : ⟦ Universe.make l ⟧_v = UType (labelling_of_valuation v l).
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_labelling_of_valuation' v (l : Level.t) n :
    val v (Universe.make' (l, n))
    = n + labelling_of_valuation v l.
  Proof.
    destruct l; cbnr. 
  Qed.

  Lemma val_valuation_of_labelling' L  (l : Level.t) n
        (e := (l, n)) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) e = (n + (L l))%nat.
  Proof.
    intros Hl [HG1 HG2]. subst G. simpl in HG1.
    destruct l as [|l|l]; rewrite ?HG1; cbnr.
    pose proof (make_graph_E uctx (edge_of_level (VariableLevel.Level l))).p2 as H.
    forward H. {
      left. eexists; split; try reflexivity; tas. }
    specialize (HG2 _ H); cbn in HG2. rewrite HG1 in HG2; cbn in HG2.
    f_equal. clear -HG2. set (L (Level.Level l)) in *; clearbody n.
    destruct n; try lia.
  Qed.

  Lemma val_valuation_of_labelling L  (l : Level.t) :
    gc_level_declared l ->
    correct_labelling G L ->
    val (valuation_of_labelling L) l = (L l).
  Proof.
    intros Hl HL.
    exact (val_valuation_of_labelling' L l 0 Hl HL).
  Qed.

  (** ** Check of leq ** *)

  Lemma leq_universe_vertices0 n (l l' : Level.t)
    : leq_vertices G n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intros H v Hv. subst G.
    apply make_graph_spec in Hv; tas.
    specialize (H _ Hv).
    rewrite !val_labelling_of_valuation. lled; try lia.
  Qed.

  Lemma leq_universe_vertices1 n (l l' : Level.t)
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
    rewrite H0 H1 in HH. simpl in HH. lia.
  Qed.

  Lemma leq_universe_vertices n (l l' : Level.t)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l')
      <-> leq_vertices G n l l'.
  Proof.
    split.
    - intros H v Hv. apply leq_universe_vertices1; tas.
    - apply leq_universe_vertices0.
  Qed.

  Definition leqb_level_n n (l l' : Level.t)
    := leqb_vertices G n l l'.
    
  Lemma leqb_level_n_spec0 n l l'
    : leqb_level_n n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intro HH. apply leq_universe_vertices0.
    apply leqb_vertices_correct; tas; clear HH; subst G; exact _.
  Qed.

  Lemma leqb_level_n_spec n (l l' : Level.t)
        (Hl : VSet.In l uctx.1) (Hl' : VSet.In l' uctx.1)
    : leqb_level_n n l l'
      <-> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof with try exact _.
    symmetry. etransitivity. apply leq_universe_vertices; subst G; assumption.
    etransitivity. subst G; apply leqb_vertices_correct...
    unfold leqb_level_n; now subst G.
  Qed.
  
  (* this is function [check_smaller_expr] of kernel/uGraph.ml *)
  Definition leqb_expr_n lt (e1 e2 : UnivExpr.t) :=
    match e1, e2 with
    | (l1, k), (l2, k') => 
      (* l1 + k < n = l2 + k' <-> l1 < n + (k - k') = l2 *)
      leqb_level_n (lt + (Z.of_nat k - Z.of_nat k')) l1 l2 
    end.

  Lemma leqb_expr_n_spec0 lt e e'
    : leqb_expr_n lt e e'
      -> gc_leq_universe_n lt uctx.2 (Universe.of_expr e) (Universe.of_expr e').
  Proof.
    unfold leqb_expr_n.
    destruct e as [l k], e' as [l' k'];
      try solve [try (cbn in *; discriminate);
      intros H v Hv; cbn;
        apply leqb_level_n_spec0 in H;
        specialize (H v Hv); cbn in H;lled;lia].
  Qed.

  Local Ltac tac1
    := match goal with
       | H : gc_leq_universe_n _ _ _ _ |- is_true (leqb_level_n _ _ _)
         => let v := fresh "v" in
           apply leqb_level_n_spec; tas; try apply Huctx;
           [..|intros v Hv; specialize (H v Hv)]; 
           cbn in *; rewrite ?UnivExpr.val_make_npl in *
       end.

  Lemma andb_is_true (b b' : bool) : b /\ b' -> b && b'.
  Proof. destruct b, b'; simpl; firstorder. Qed.

  Lemma leqb_expr_n_spec n e e'
        (HHl  : gc_expr_declared e)
        (HHl' : gc_expr_declared e')
    : leqb_expr_n ⎩ n ⎭ e e'
      <-> gc_leq_universe_n ⎩ n ⎭ uctx.2 (Universe.of_expr e) (Universe.of_expr e').
  Proof.
    split; [apply leqb_expr_n_spec0|].
    unfold leqb_expr_n.
    destruct e as [l k] eqn:eqe, e' as [l' k'] eqn:eqe'; cbn; intro H;
      destruct HC as [v0 Hv0]; pose proof (H v0 Hv0) as H0; cbn in H0.
     simpl in H0 |- *.
    apply leqb_level_n_spec; tas.
    intros v Hv.
    specialize (H v Hv). simpl in H. cbn in H.
    rewrite !Universe.val_make_npl.
    lled; try lia.
  Qed.
  
  (* this is function [exists_bigger] of kernel/uGraph.ml *)
  Definition leqb_expr_univ_n lt (e1 : UnivExpr.t ) (u : Universe.t) :=
    match u with
    | Universe.lSProp | Universe.lProp => false
    (* CHECKME:SPROP: should we use [prop_sub_type] here somehow? *)
    (* if UnivExpr.is_prop e1 && (n =? 0) then *)
    (*   prop_sub_type || Universe.is_prop u *)
                                             (* else *)
      | Universe.lType l =>
      let '(e2, u) := Universe.exprs l in
      List.fold_left (fun b e2 => leqb_expr_n lt e1 e2 || b)
                     u (leqb_expr_n lt e1 e2)
    end.

  Lemma leqb_expr_univ_n_spec0 n e1 u
    : leqb_expr_univ_n n e1 u
      -> gc_leq_universe_n n uctx.2 (Universe.lType (Universe.make' e1)) u.
  Proof.
    unfold leqb_expr_univ_n, gc_leq_universe_n; cbn.
    intros H v Hv. destruct u; try discriminate;cbn in *.
    rewrite val_fold_right.
    destruct (Universe.exprs n0) as [e u'] eqn:Ht0;cbn in *.
    rewrite <- !fold_left_rev_right in H; cbn in *.
    induction (List.rev u'); cbn in *.
    - apply leqb_expr_n_spec0; tas.
    - apply orb_true_iff in H. destruct H as [H|H].
      + apply leqb_expr_n_spec0 in H. specialize (H v Hv); cbn in *.
        lled; lia.
      + apply IHl in H; clear IHl. lled; lia.
  Qed.

  Import Nbar Datatypes.

  Coercion Universe.lType : Universe.nonEmptyUnivExprSet >-> Universe.t_.

  Lemma val_le_caract' (u : Universe.nonEmptyUnivExprSet) v k :
    (exists e, UnivExprSet.In e u /\ Z.of_nat k <= Z.of_nat (val v e))%Z <-> (Z.of_nat k <= Z.of_nat (val v u))%Z.
  Proof.
    epose proof (val_le_caract u v k).
    intuition auto.
    apply inj_le, H0.
    destruct H as [e [? ?]]. exists e; split; auto.
    lia.
    assert (k <= val v u)%nat. lia.
    destruct (H1 H2) as [e [? ?]]. exists e; split; auto.
    lia.
  Qed.

  Lemma val_ge_caract' (u : Universe.nonEmptyUnivExprSet) v k :
    (forall e, UnivExprSet.In e u -> (Z.of_nat (val v e) <= Z.of_nat k)%Z) <-> (Z.of_nat (val v u) <= Z.of_nat k)%Z.
  Proof.
    epose proof (val_ge_caract u v k).
    intuition auto.
    apply inj_le, H0.
    intros e hin. specialize (H e hin). lia.
    assert (val v u <= k)%nat. lia.
    specialize (H1 H3 e H2). lia.
  Qed.

  Lemma Z_of_nat_bool_to_nat x b : (Z.of_nat x + ⎩ b ⎭)%Z = Z.of_nat (x + if b then 1%nat else 0%nat).
  Proof. destruct b; simpl; lia. Qed.

  Lemma Z_of_nat_inj_bool (x : bool) : Z.of_nat (if x then 1%nat else 0%nat) = ⎩ x ⎭.
  Proof. destruct x; simpl; auto. Qed.

  Definition neg_forall p u := 
    UnivExprSet.for_all p u = false.

  Lemma exists_neg_forall p u : neg_forall p u <-> UnivExprSet.exists_ (fun x => ~~ (p x)) u.
  Proof.
    unfold neg_forall.
    split. intros nf.
    now apply UnivExprSet_for_all_false in nf.
    intros ex.
    apply not_true_iff_false; intro HH.
    eapply UnivExprSet.for_all_spec in HH. 2:proper.
    red in ex.
    eapply UnivExprSet.exists_spec in ex as [x [inx npx]]. 2:proper.
    specialize (HH _ inx). simpl in HH. rewrite HH in npx. simpl in npx. congruence. 
  Qed.

  Definition lsp_expr G l (ei : UnivExpr.t) : Nbar.t := 
    let '(li, bi) := ei in (lsp G l li + Some (Z.of_nat bi))%nbar.
  
  Local Open Scope Z_scope.

  Definition is_lt (x y : Nbar.t) : bool :=
    ~~ le_lt_dec y x.
  
  Lemma is_lt_spec x y : is_lt x y -> (x < y)%nbar.
  Proof.
    unfold is_lt. destruct le_lt_dec. simpl. discriminate. simpl.
    auto.
  Qed.

  (* Non trivial lemma *)
  (* l + n  <= max (l1, ... ln)  -> exists i, l+n <= li *)
  Lemma gc_leq_universe_n_sup lt (l : Level.t) b (u : Universe.nonEmptyUnivExprSet)
        (e := (l, b)) :
      gc_level_declared l ->
      gc_levels_declared u ->
      gc_leq_universe_n ⎩ lt ⎭ uctx.2 (Universe.make' e) u ->
      exists (e' : UnivExpr.t), UnivExprSet.In e' u
            /\ gc_leq_universe_n ⎩ lt ⎭ uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    intros Hl Hu H.
    assert (HG1 : invariants G) by (subst; exact _).
    assert (HG2 : acyclic_no_loop G) by (subst; exact _).
    assert (Hs : wGraph.s G = lSet) by now subst G.
    assert (Vs : VSet.In lSet (wGraph.V G)).
    { rewrite <-Hs. now apply source_vertex. }
    case_eq (lsp G l lSet).
    (* case where there is a path from l to Set, so l <= Set+ (-m).
      This implies that -m + b <= val v u.
    *)
    - intros lset Hlset. red in H.
      (** Needs to strengthen the argument using a valuations of l with - m *)
      assert (Hinl : VSet.In l (wGraph.V G)). {
        red in Hl;  cbn in Hl;
          now subst G. }
      epose proof (lsp_to_s G Hinl).
      rewrite Hs in H0. specialize (H0 Hlset).
      pose proof (lsp_s G _ Hinl) as [sl [lspsl slpos]].
      assert (Hl' : forall v, gc_satisfies v uctx.2 -> (val v l <= Z.to_nat (- lset))%nat). {
        intros v Hv. apply make_graph_spec in Hv.
        rewrite <- HG in Hv.
        eapply correct_labelling_lsp in Hlset; tea.
        cbn in Hlset.
        change (labelling_of_valuation v l) with (val v l) in Hlset. lia. }
      assert (Hl'' : forall v, gc_satisfies v uctx.2 -> (Z.to_nat sl <= val v l)%nat). {
          intros v Hv. apply make_graph_spec in Hv.
          rewrite <- HG in Hv. rewrite Hs in lspsl.
          eapply correct_labelling_lsp in lspsl; tea.
          cbn in lspsl.
          change (labelling_of_valuation v l) with (val v l) in lspsl. lia. }
      assert (UnivExprSet.for_all
        (fun ei => is_lt (lsp_expr G l ei - Some (Z.of_nat b))%nbar (Some ⎩ lt ⎭))%Z
        u = false) as HH. {
        apply not_true_iff_false; intro HH.
        apply UnivExprSet.for_all_spec in HH; proper.
        set (G' := wGraph.Subgraph1.G' G lSet l lset) in *.
        assert (HG'1 : invariants G'). {
          subst G'; apply Subgraph1.HI'; tas. }
        assert (HG'2 : acyclic_no_loop G'). {
          subst G'; apply Subgraph1.HG'; tas. }
        eapply (Subgraph1.correct_labelling_lsp_G' G) in Hlset as Hlab; tas.
        fold G' in Hlab; cbn in Hlab.
        set (lab := fun x => to_label (lsp G' (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv). specialize (Hl' _ Hv).
        specialize (Hl'' _ Hv).
        unfold univ_le_n in H. simpl in H.
        rewrite Universe.val_make' in H.
        rewrite (val_valuation_of_labelling' _ l b) in H; tas.
        apply switch_minus in H.
        subst e.
        rewrite Z_of_nat_bool_to_nat in H.
        eapply val_le_caract' in H.
        destruct H as [ei [Hei H]]. specialize (HH ei Hei); cbn in HH.
        specialize (Hu ei Hei).
        destruct ei as [li bi]; cbn in *.
        assert (Vli : VSet.In li (wGraph.V G)).
        { rewrite HG. now cbn. }

        simpl in H. unfold is_lt in HH.
        match goal with
        | H : ~~ is_left ?X = true |- _ =>
          destruct X as [HH'|Hlt]; [discriminate|]; clear H
        end.
        rewrite val_valuation_of_labelling in H; tas.
        rewrite !Nat2Z.inj_add in H.
        rewrite Z_of_nat_inj_bool in H.
        assert (Z.of_nat (lab l) = - lset).
        { unfold lab. 
          epose proof (Subgraph1.lsp_G'_spec_left G _ _ Hinl Vs _ Hlset l).
          fold G' in H1. rewrite Hs H1. clear H1.
          rewrite lsp_xx. 
          pose proof (lsp_sym _ Hlset).
          destruct (lsp_s G l Hinl) as [sl' [lspsl' w]].
          rewrite Hs in lspsl'. rewrite lspsl' in H1 |- *.
          simpl in H1. cbn -[to_label].
          rewrite Z_of_to_label_pos //; lia. }
        rewrite H1 in H.
        destruct (lsp_s G' li) as [ni [Hni nipos]].
        { cbn. now rewrite HG. }
        generalize (Subgraph1.lsp_G'_spec_left G lSet l Hinl Vs _ Hlset li).
        fold G'. simpl in Hni.
        rewrite <-Hs, Hni.
        destruct (lsp_s G li Vli) as [sli [lspsli wsli]].
        rewrite lspsli. rewrite Hs in Hni, lspsli, lspsl.
        assert (⎩ lt ⎭ <= - Z.of_nat b + lset + Z.of_nat bi + Z.of_nat (lab li)) by lia.
        destruct (lsp G l li) as [lli|] eqn:elli.
        2:{ elimtype False.
          generalize (lsp_codistance G l lSet li).
          now rewrite elli Hlset lspsli. }
        simpl in Hlt.
        assert (lli + Z.of_nat bi - Z.of_nat b < - Z.of_nat b + lset + Z.of_nat bi + Z.of_nat (lab li)) by lia.
        assert (lli < lset + Z.of_nat (lab li)) by lia.
        unfold lab in H. rewrite Hs in H.
        rewrite Hni in H.
        rewrite Z_of_to_label_pos in H; try lia.
        intros hmax.
        symmetry in hmax.
        apply eq_max in hmax as [[= eq]|eq]. subst ni.
        unfold lab in H4. rewrite Hs Hni in H4.
        rewrite Z_of_to_label_pos in H4; try lia.
        pose proof (lsp_codistance G l lSet li). rewrite Hlset lspsli elli in H5.
        simpl in H5. lia.
        simpl in eq. noconf eq.
        lia. }
      apply UnivExprSet_for_all_false in HH.
      apply UnivExprSet.exists_spec in HH; proper.
      unfold UnivExprSet.Exists in *.
      destruct HH as [[li bi] [He' HH]]. unfold is_lt in HH.
      rewrite negb_involutive in HH.
      eexists; split; tea.
      match goal with
      | H : ssrbool.is_left ?X = true |- _ =>
        destruct X as [HH'|HH']; try discriminate; clear H
      end.
      cbn in HH'.
      rewrite Hs in lspsl.
      case_eq (lsp G l li).
      2: intros X; rewrite X in HH'; destruct bi, b; contradiction.
      intros nl Hnl v Hv; rewrite Hnl in HH'.
      simpl in HH'.
      unfold univ_le_n. simpl.
      rewrite (val_labelling_of_valuation' v li bi); cbn.
      specialize (Hl' _ Hv).
      specialize (Hl'' _ Hv).
      pose proof Hv as Hv'.
      apply make_graph_spec in Hv; tas. rewrite <- HG in Hv.
      apply (correct_labelling_lsp _ Hnl) in Hv. cbn in Hv.
      apply switch_minus.
      rewrite !Nat2Z.inj_add.
      enough (Z.of_nat b + Z.of_nat (val v l) + ⎩ lt ⎭ - Z.of_nat bi <= Z.of_nat (labelling_of_valuation v li)) by lia.
      etransitivity; [|eassumption].
      assert (Z.of_nat (val v l) = Z.of_nat (labelling_of_valuation v l)).
      reflexivity. rewrite H1. lia.

    (* case where there is no path from l to Set *)
    - intros HlSet. subst e.
      assert (Hl' : VSet.In l (wGraph.V G)). {
        red in Hl; cbn in Hl; now subst G. }

      assert (UnivExprSet.for_all
                (fun ei => match ei with
                        | (li, bi) =>
                          le_lt_dec (Some (Z.of_nat bi)
                          + Some (match b with 0%nat => 1%Z | _ => (- (Z.pred (Z.of_nat b)))%Z end)
                          + lsp G l li)
                          (Some ⎩ lt ⎭)%Z
                        end)%nbar
                u = false) as HH. {
        apply not_true_iff_false; intro HH.
        destruct (lsp_s G _ Hl') as [nl [Hnl nlpos]]; cbn in Hnl.

        assert (exists K : Z, (nl <= K)%Z /\
                UnivExprSet.For_all
                  (fun ei => match ei with
                            | (li, bi) =>
                              match lsp G (wGraph.s G) li with
                              | None => True
                              | Some ni => ((Z.of_nat bi) + ni < K)%Z
                              end
                                 end) u) as XX. {
          exists (UnivExprSet.fold
               (fun ei K => match ei with
                         | (li, bi) =>
                           match lsp G (wGraph.s G) li with
                           | None => K
                           | Some ni => Z.max K (Z.succ (Z.of_nat bi) + ni)
                           end
                         end) u nl).
          clear -Hu HG HG1 HG2. split.
          - rewrite UnivExprSet.fold_spec. rewrite <- fold_left_rev_right.
            induction (List.rev (UnivExprSet.elements u)). reflexivity.
            cbn. destruct a as [li bi]; tas.
            destruct (lsp G (wGraph.s G) li); tas; lia.
          - intros [li bi] Hei; trivial.
            specialize (Hu _ Hei); cbn in Hu.
            destruct (lsp_s G li) as [ni' [Hni' ni'pos]].
            { now subst G. }
            rewrite Hni'.
            rewrite UnivExprSet.fold_spec. rewrite <- fold_left_rev_right.
            apply UnivExprSetFact.elements_1, InA_In_eq, in_rev in Hei.
            change (In (li, bi)
                       (@List.rev UnivExprSet.elt (UnivExprSet.elements u))) in Hei.
            induction (List.rev (UnivExprSet.elements u)); inv Hei.
            + subst a; cbn. rewrite Hni'. lia.
            + specialize (IHl H). cbn. destruct a as [li' bi'].
              destruct (lsp G (wGraph.s G) li'); lia. }
        destruct XX as [K [HK1 HK2]].
        assert (Hs' : VSet.In lSet (wGraph.V G)). {
          rewrite <- Hs; apply HG1. }
        set (G' := wGraph.G' G lSet l K) in *.
        assert (lsG : l <> wGraph.s G). intros eq. 
        { rewrite eq in HlSet, Hnl.
          congruence. }
        assert (HG'1 : invariants G'). {
          subst G'; apply HI'; tas. }
        assert (HG'2 : acyclic_no_loop G'). {
          subst G'; apply HG'; tas. }
        apply correct_labelling_lsp_G' with (K:=K) in HlSet as Hlab; tas.
        fold G' in Hlab; cbn in Hlab.
        set (lab := fun x => to_label (lsp G' (wGraph.s G) x)) in *.
        pose proof (make_graph_spec' _ Huctx lab) as Hv.
        forward Hv; [now rewrite <- HG|].
        specialize (H _ Hv); clear Hv.
        unfold univ_le_n in H. simpl in H.
        rewrite Universe.val_make' in H.
        rewrite val_valuation_of_labelling' in H; tas.

        apply switch_minus in H.
        rewrite Z_of_nat_bool_to_nat in H.
        apply val_le_caract' in H.
        destruct H as [ei [Hei H]].
        apply UnivExprSet.for_all_spec in HH; proper.
        specialize (HH _ Hei); cbn in HH.
        specialize (Hu _ Hei).
        destruct ei as [li bi]; cbn in H.
        rewrite val_valuation_of_labelling in H; tas.
        match goal with
        | H : is_left ?X = true |- _ =>
          destruct X as [HH'|HH']; try discriminate; clear H
        end.
        assert (lab l = to_label (Some K)) as XX. {
          subst lab; cbn. subst G'. rewrite -> Hs in *.
          rewrite lsp_G'_spec_left; tas. rewrite Hnl.
          unfold lsp. rewrite acyclic_lsp0_xx; tas.
          simpl. assert (Z.max nl (K + 0) = K). lia. now rewrite H0. }
        rewrite XX in H.
        destruct (lsp_s G li) as [ni [Hni nipos]].
        { now subst G. }
        specialize (HK2 _ Hei); cbn in HK2. rewrite Hni in HK2.

        case_eq (lsp G l li).
        - intros ki Hki. rewrite Hki in HH'; cbn in HH'.
          destruct (Z.leb_spec ni (K + ki)).
          assert (lab li = to_label (Some (K + ki)%Z)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. rewrite Hki.
            rewrite Hni; cbn.
            assert (Z.max ni (K + ki) = K + ki)%Z as ->. lia.
            reflexivity. }
          rewrite XX' in H.
          rewrite !Nat2Z.inj_add in H.
          rewrite !Z_of_to_label in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 (K + ki)); [|].
          rewrite Z_of_nat_inj_bool in H.
          destruct b; cbn in *; lia.
          destruct b, lt; cbn in *; lia.
          assert (lab li = to_label (Some ni)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. rewrite Hki Hni; simpl.
            enough (Z.max ni (K + ki) = ni)%Z as ->; auto. lia. }
          rewrite XX' in H.
          rewrite !Nat2Z.inj_add !Z_of_to_label Z_of_nat_inj_bool in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 ni); [|lia].
          destruct b, lt; cbn in *; lia.

        - intro Hki.
          assert (lab li = to_label (Some ni)) as XX'. {
            subst lab; cbn. subst G'. rewrite -> Hs in *.
            rewrite lsp_G'_spec_left; tas. now rewrite Hki Hni. }
          rewrite XX' in H. 
          rewrite !Nat2Z.inj_add !Z_of_to_label Z_of_nat_inj_bool in H.
          destruct (Z.leb_spec 0 K); [|lia].
          destruct (Z.leb_spec 0 ni); [|lia].
          destruct b, lt; cbn in *; lia. }

    apply UnivExprSet_for_all_false in HH.
    apply UnivExprSet.exists_spec in HH; proper.
    destruct HH as [[li bi] [He' HH]].
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
    unfold univ_le_n; simpl.
    rewrite !val_labelling_of_valuation'.
    destruct b, lt; cbn in *; lled; lia.
  Qed.

  Lemma leqb_expr_univ_n_spec lt e1 (u : Universe.t)
        (He1 : gc_expr_declared e1)
        (Hu  : gc_levels_declared_univ u)
    : leqb_expr_univ_n ⎩ lt ⎭ e1 u
      <-> gc_leq_universe_n ⎩ lt ⎭ uctx.2 (Universe.make' e1) u.
  Proof.
    split; [apply leqb_expr_univ_n_spec0|].
    unfold leqb_expr_univ_n; intro HH.
    destruct u.
    - (*contradiction *)
      cbn in *. destruct HC as [v Hv];specialize (HH v Hv); cbn in HH.
      auto.
    - (*contradiction *)
      cbn in *. destruct HC as [v Hv];specialize (HH v Hv); cbn in HH.
      destruct lt; simpl in *; lled;lia.
    - case_eq (Universe.exprs n). intros e u' ee.
      assert (Hu': gc_expr_declared e /\ Forall gc_expr_declared u'). {
      split. apply Hu. apply Universe.In_exprs. left. now rewrite ee.
      apply Forall_forall. intros e' He'. apply Hu.
      apply Universe.In_exprs. right. now rewrite ee. }
      destruct e1 as [l1 b1].
      apply gc_leq_universe_n_sup in HH; tas.
      destruct HH as [e' [He' HH]]. apply leqb_expr_n_spec in HH; tas.
      2:{ now apply Hu. }
      apply Universe.In_exprs in He'. rewrite ee in He'; cbn in He'.
      rewrite <- !fold_left_rev_right.
      clear -He' HH. destruct He' as [H|H]; [subst|].
      * induction (List.rev u'); tas;cbn -[leqb_expr_n].
        now rewrite IHl orb_true_r.
      * apply In_rev in H.
        induction (List.rev u'); cbn -[leqb_expr_n]; invs H.
        now rewrite HH. now rewrite IHl; auto; rewrite orb_true_r.
  Qed.

  (* this is function [real_check_leq] of kernel/uGraph.ml *)
  Definition leqb_universe_n lt (u1 u2 : Universe.t) :=
    match u1 with
    | Universe.lSProp => negb lt && Universe.is_sprop u2
    | Universe.lProp =>
      (~~ lt && Universe.is_prop u2) ||
      (prop_sub_type && ~~ Universe.is_sprop u2 && implb lt (negb (Universe.is_prop u2)))
    | Universe.lType l =>
      let '(e1, u1) := Universe.exprs l in
      List.fold_left (fun b e1 => leqb_expr_univ_n ⎩ lt ⎭ e1 u2 && b)
                     u1 (leqb_expr_univ_n ⎩ lt ⎭ e1 u2)
    end.
  
  (* this is function [real_check_leq] of kernel/uGraph.ml *)
  Definition leqb_universe_exprs_n n (l1 l2 : Universe.nonEmptyUnivExprSet) :=
      let '(e1, u1) := Universe.exprs l1 in
      List.fold_left (fun b e1 => leqb_expr_univ_n n e1 l2 && b)
                     u1 (leqb_expr_univ_n n e1 l2).

  (* Lemma level_not_zero_le_zero' u n :
    (Universe.is_sprop u || Universe.is_prop u) && (n =? 0) = false
    -> forall v, (0 <= Z.of_nat n + val v u)%Z.
  Proof.
    intros Hp v. apply andb_false_iff in Hp as [H|H].
    - toProp H as [? ?].
      apply (is_prop_and_is_sprop_val_false u) with (v:=v) in H. lia. assumption.
    - pose proof (val_minus_one u v).
      destruct n; [discriminate|lia].
  Qed. *)
  
  Lemma trichotomy u : 
    Universe.is_sprop u || Universe.is_prop u || 
    ~~ (Universe.is_prop u || Universe.is_sprop u).
  Proof.
    destruct u; auto.
  Qed.

  Lemma is_sprop_is_prop {u} : Universe.is_sprop u -> ~~ Universe.is_prop u.
  Proof. destruct u; auto. Qed.

  Lemma is_prop_is_sprop {u} : Universe.is_prop u -> ~~ Universe.is_sprop u.
  Proof. destruct u; auto. Qed.

  Lemma fold_right_xpred0 {A} (l : list A) : fold_right (fun _ => xpred0) false l = false.
  Proof. induction l; simpl; auto. Qed.

  Lemma leqb_universe_n_spec0 lt (u1 u2 : Universe.t)
    : leqb_universe_n lt u1 u2 -> gc_leq_universe_n ⎩ lt ⎭ uctx.2 u1 u2.
  Proof.
    unfold leqb_universe_n, gc_leq_universe_n.
    move/orP: (trichotomy u1) => [/orP [issp1|isp1]|diff];
    destruct u1 eqn:Hu1;cbn;intros H v Hv; try discriminate.
    - move/orP: (trichotomy u2) => [/orP [issp|isp]|].
      * rewrite issp /= andb_true_r in H.
        apply is_sprop_val with (v:=v) in issp; rewrite issp; cbn.
        destruct lt; simpl in *; lled => //; try lia.
      * destruct u2; try discriminate. simpl.
        now move/andP: H => [? ?].
      * rewrite negb_orb; move/andP=> [isp issp].
        destruct u2; try discriminate. simpl.
        now rewrite (negbTE issp) andb_false_r in H.
    - move/orP: (trichotomy u2) => [/orP [issp|isp]|].
      * rewrite issp (negbTE (is_sprop_is_prop issp)) andb_false_r /= in H.
        apply is_sprop_val with (v:=v) in issp; rewrite issp; cbn.
        destruct lt; simpl in *; lled => //; try lia.
      * rewrite isp /= andb_true_r in H.
        destruct lt; simpl in * => //.
        now rewrite andb_false_r in H.
        apply is_prop_val with (v:=v) in isp. now rewrite isp.
      * rewrite negb_orb. move/andP => [isp issp].
        rewrite isp issp (negbTE isp) andb_false_r implybT !andb_true_r /= in H.
        destruct (⟦ u2 ⟧_v) eqn:vu2.
        eapply val_is_prop in vu2. now rewrite vu2 in isp.
        eapply val_is_sprop in vu2. now rewrite vu2 in issp.
        now rewrite H.
    - unfold val, Universe.Evaluable'.
      destruct (Universe.exprs n) as [e1 u1'] eqn:Hu1'.
      subst u1.
      rewrite <- fold_left_rev_right in *; cbn in *.
      induction (List.rev u1'); cbn in *.
      + apply leqb_expr_univ_n_spec0 in H.
        specialize (H v Hv); cbn in H. assumption.
      + set (z := (fold_right (fun e x => Nat.max (val v e) x) (val v e1) l)) in *.
        toProp as [H HH].
        apply leqb_expr_univ_n_spec0 in H. specialize (H v Hv). cbn in H.
        destruct (Nat.max_dec (val v a) z) as [ee|ee]; rewrite ee.
        * assumption.
        * apply IHl; tas.
  Qed.

  Lemma leqb_universe_expr_n_spec lt (l1 l2 : Universe.nonEmptyUnivExprSet)
        (Hu1  : gc_levels_declared l1)
        (Hu2  : gc_levels_declared l2)
    : leqb_universe_n lt l1 l2
      <-> gc_leq_universe_n ⎩ lt ⎭ uctx.2 l1 l2.
  Proof.
    split; [apply leqb_universe_n_spec0|].
    unfold leqb_universe_n; intro HH.
    case_eq (Universe.exprs l1); intros e1 uu1 Huu1.
    rewrite (fold_left_andb_forallb (fun e => _)).
    pose proof (Universe.exprs_spec' l1) as X; rewrite Huu1 in X; cbn in X.
    rewrite X. apply forallb_Forall. apply Forall_forall.
    intros ei Hei.
    apply InA_In_eq, UnivExprSetFact.elements_2 in Hei.
    specialize (Hu1 _ Hei).
    eapply leqb_expr_univ_n_spec; tas.
    intros v Hv. specialize (HH v Hv).
    simpl in HH |- *.
    transitivity (Z.of_nat (val v l1)); eauto.
    eapply (val_ge_caract' l1 v (val v l1)).p2. lia. auto.
  Qed.

  Lemma leqb_universe_n_spec lt (u1 u2 : Universe.t)
        (Hu1  : gc_levels_declared_univ u1)
        (Hu2  : gc_levels_declared_univ u2)
    : leqb_universe_n lt u1 u2
      <-> gc_leq_universe_n ⎩ lt ⎭ uctx.2 u1 u2.
  Proof.
    split;[apply leqb_universe_n_spec0|].
    destruct u1; cbn; auto.
    - intros H. unfold gc_leq_universe_n in *;cbn in *.
      destruct HC as [v Hv]. specialize (H v Hv).
      move/orP: (trichotomy u2) => [/orP [isp|issp]|isp].
      rewrite isp. rewrite (is_sprop_val _ isp v) in H.
      destruct lt; simpl in *; auto; lled; try lia.
      destruct u2 => //. simpl in *.
      destruct lt => //.
      destruct u2; simpl in * => //.
      rewrite andb_false_r implybT !andb_true_r /=.
      destruct prop_sub_type; auto.
    - intros H. unfold gc_leq_universe_n in *;cbn in *.
      unfold is_true; repeat rewrite orb_true_iff;auto.
      destruct HC as [v Hv]; specialize (H v Hv).
      destruct u2;cbn;auto => //. simpl in H.
      now destruct lt.
    - intros.
      destruct HC as [v Hv]. specialize (H v Hv) as HH;cbn in *.
      destruct u2;cbn in *; lled;try lia;
        apply leqb_universe_expr_n_spec;auto.
  Qed.

  Definition check_leqb_universe (u1 u2 : Universe.t) :=
    ~~ check_univs
    || (prop_sub_type && Universe.is_prop u1 && ~~ Universe.is_sprop u2)
    || Universe.eqb u1 u2
    || leqb_universe_n false u1 u2.

  Lemma check_leqb_universe_spec (u1 u2 : Universe.t)
        (Hu1  : gc_levels_declared_univ u1)
        (Hu2  : gc_levels_declared_univ u2)
    : check_leqb_universe u1 u2 <-> gc_leq_universe uctx.2 u1 u2.
  Proof.
    unfold check_leqb_universe, gc_leq_universe.
    destruct check_univs; split; cbn; trivial; intro H.
    - move/orP: H => [/orP [/andP [/andP [ps isp] issp]|ps]|].
      destruct u1 => //.
      apply (leqb_universe_n_spec0 false). simpl.
      now rewrite ps issp orb_true_r.
      apply eqb_true_iff in ps. subst.
      intros v Hv. reflexivity.
      now apply leqb_universe_n_spec.
    - apply (leqb_universe_n_spec false) in H; tas. cbn in *. rewrite H.
      now rewrite orb_true_r.
  Qed.

  Definition check_eqb_universe (u1 u2 : Universe.t) :=
    ~~ check_univs
    || Universe.eqb u1 u2
    || (leqb_universe_n false u1 u2 && leqb_universe_n false u2 u1).

  Lemma check_eqb_universe_exprs_spec (l1 l2 : Universe.nonEmptyUnivExprSet)
        (Hu1  : gc_levels_declared l1)
        (Hu2  : gc_levels_declared l2)
    : check_eqb_universe l1 l2 <-> gc_eq_universe uctx.2 l1 l2.
  Proof.
    unfold check_eqb_universe, gc_eq_universe.
    destruct check_univs; split;auto;intro H.
    - toProp H as [H|H].
      + apply univ_expr_eqb_true_iff in H; subst. intros v Hv; reflexivity.
      + toProp H as [H1 H2].
        apply leqb_universe_n_spec0 in H1. apply leqb_universe_n_spec0 in H2.
        intros v Hv. specialize (H1 v Hv); specialize (H2 v Hv).
        simpl in *. f_equal; lia.
    - toProp; right.
      toProp; apply leqb_universe_n_spec; tas; intros v Hv; specialize (H v Hv).
      rewrite H. reflexivity.
      rewrite H. reflexivity.
  Qed.

  Let levels_declared (u : Universe.t)
  := match u with
     | Universe.lSProp | Universe.lProp => True
     | Universe.lType l => gc_levels_declared l
     end.

  Lemma fold_left_false {A} l : fold_left (B:=A) (fun _ : bool => xpred0) l false = false.
  Proof.
    induction l; simpl; eauto.
  Qed.

  Lemma check_eqb_universe_spec (u1 u2 : Universe.t)
        (Hu1  : levels_declared u1)
        (Hu2  : levels_declared u2)
    : check_eqb_universe u1 u2 <-> gc_eq_universe uctx.2 u1 u2.
  Proof.
    destruct u1, u2; simpl; rewrite ?check_eqb_universe_exprs_spec; auto; cbn; unfold check_eqb_universe; 
    repeat rewrite ?orb_true_r ?orb_false_r ?andb_true_r ?andb_false_r; cbn.
    9:reflexivity.
    all:unfold gc_eq_universe; destruct check_univs eqn:cu; cbn; try split; auto; try discriminate.
    intros. all: try (red; intros v gc; simpl; auto).
    all:try solve [intros Hgc; destruct HC as [v Hv]; specialize (Hgc v Hv); simpl in Hgc; try discriminate].
    rewrite !andb_true_r in v.
    intros Hgc.
    destruct (Universe.exprs n).
    now rewrite fold_left_false andb_false_r in v.
    destruct (Universe.exprs n).
    now rewrite fold_left_false /= in v.
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
                       | gc_le l z l' => leqb_level_n z l l'
                       | gc_lt_set_level k l => leqb_level_n (Z.of_nat (S k)) lSet (Level l)
                       | gc_le_set_var k n => leqb_level_n (Z.of_nat k) lSet (Var n)
                       | gc_le_level_set l k => leqb_level_n (- Z.of_nat k)%Z (Level l) lSet
                       | gc_le_var_set n k => leqb_level_n (- Z.of_nat k)%Z (Var n) lSet
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
    destruct gc as [l z l'|k l|k n|l k|n k].
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in *. toProp.
      pose proof (val_level_of_variable_level v l).
      pose proof (val_level_of_variable_level v l').
      destruct l, l'; cbn in *; lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn -[Z.of_nat] in HH. unfold gc_satisfies0. toProp.
      cbn in *. lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
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

Section CheckLeq'.
  Context {cf:checker_flags}.

  Context (G : universes_graph)
          uctx (Huctx: global_gc_uctx_invariants uctx) (HC : gc_consistent uctx.2)
          (HG : G = make_graph uctx).
 
  (*Lemma check_gc_constraint_complete gcs
    : gc_consistent gcs -> check_gc_constraints G gcs.
  Proof.
    unfold check_gc_constraints. cbn.
    intros [v Hv].
    unfold gc_satisfies in Hv.
    apply GoodConstraintSetFact.for_all_iff in Hv; eauto. 2:typeclasses eauto.
    apply GoodConstraintSetFact.for_all_iff; eauto. typeclasses eauto.
    intros gc hc. specialize (Hv gc hc). cbn in Hv.
    unfold gc_satisfies0 in Hv.
    destruct gc as [l z l'|k l|k n|l k|n k].
    - cbn. apply (leqb_level_n_spec G uctx Huctx HC HG). admit. admit.
      intros v' Hv'. cbn.
      specialize (HH v Hv). cbn in *. toProp.
      pose proof (val_level_of_variable_level v l).
      pose proof (val_level_of_variable_level v l').
      destruct l, l'; cbn in *; lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn -[Z.of_nat] in HH. unfold gc_satisfies0. toProp.
      cbn in *. lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
    - intros HH v Hv; apply leqb_level_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lled; lia.
  Qed. *)
End CheckLeq'.

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
    exact (uctx.1, ctrs).
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
    := on_Some_or_None (fun l : Level.t => level_declared l)
                       (UnivExpr.get_noprop e).

  Let levels_declared (u : Universe.t)
    := match u with
       | Universe.lSProp | Universe.lProp => True
       | Universe.lType l => UnivExprSet.For_all expr_declared l
       end.

  Lemma level_gc_declared_declared l
    : level_declared l -> gc_level_declared uctx' l.
  Proof.
    clear. subst uctx'.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2); [|contradiction HG].
    cbn; clear HG. unfold level_declared, gc_level_declared; cbn.
    destruct l; cbn; trivial; intro.
  Qed.

  Lemma expr_gc_declared_declared e
    : expr_declared e -> gc_expr_declared uctx' e.
  Proof.
    destruct e as [l b]; cbn; trivial.
    intro; now apply (level_gc_declared_declared l) in H.
  Qed.

  Lemma levels_gc_declared_declared (u : Universe.t)
    : levels_declared u -> gc_levels_declared_univ uctx' u.
  Proof.
    unfold levels_declared, gc_levels_declared.
    destruct ?;auto.
    intros HH e He; specialize (HH e He).
    now apply expr_gc_declared_declared.
  Qed.

  Lemma leqb_univ_expr_n_spec' lt e1 u
        (He1 : expr_declared e1)
        (Hu : levels_declared u)
    : leqb_expr_univ_n G ⎩ lt ⎭ e1 u
      <-> leq_universe_n ⎩ lt ⎭ uctx.2 (Universe.make' e1) u.
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

  Lemma check_leqb_universe_spec' u1 u2
    : check_leqb_universe G u1 u2 -> leq_universe uctx.2 u1 u2.
  Proof.
    unfold check_leqb_universe, leq_universe.
    destruct check_univs; cbn; [|trivial].
    case_eq (prop_sub_type && Universe.is_prop u1 && ~~ Universe.is_sprop u2). {
      simpl. intros e e' v Hv. toProp e as [Hp Hu1]. toProp Hp as [ps isp].
      rewrite (is_prop_val _ isp v).
      destruct u2; try easy. simpl. now rewrite ps. }
    intros _. simpl.
    case_eq (Universe.eqb u1 u2). {
      intros e _ v Hv. apply eqb_true_iff in e. now destruct e. }
    intros _; cbn.
    intro H; unshelve eapply (leqb_universe_n_spec0 G uctx' Huctx' HC' HG'
                                                    _ _ _) in H.
    eapply gc_leq_universe_0_iff.
    unfold uctx' in H.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2). cbn in *. exact H.
    exact I.
  Qed.

  Lemma check_leqb_universe_complete u1 u2 :
    levels_declared u1 ->
    levels_declared u2 ->
    leq_universe uctx.2 u1 u2 ->
    check_leqb_universe G u1 u2.
  Proof.
    intros decl1 decl2.
    apply levels_gc_declared_declared in decl1.
    apply levels_gc_declared_declared in decl2.
    rewrite gc_leq_universe_iff.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    intros eq.
    apply <- check_leqb_universe_spec; eauto.
    exact eq.
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
    split; eapply gc_leq_universe_0_iff;
      (destruct (gc_of_constraints uctx.2); [cbn in *|contradiction HG]); tas.
  Qed.
  
  Lemma check_eqb_universe_complete u1 u2 :
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

  Definition leq_level_n z l l' :=
    leq_universe_n z uctx.2 (Universe.make l) (Universe.make l').

  Definition valid_gc_constraint (gc : GoodConstraint.t) :=
    match gc with
    | gc_le l z l' => leq_level_n z l l'
    | gc_lt_set_level k l => leq_level_n (Z.of_nat (S k)) lSet (Level l)
    | gc_le_set_var k n => leq_level_n (Z.of_nat k) lSet (Var n)
    | gc_le_level_set l k => leq_level_n (- Z.of_nat k)%Z (Level l) lSet
    | gc_le_var_set n k => leq_level_n (- Z.of_nat k)%Z (Var n) lSet
    end.

  Definition valid_gc_constraints (gcs : GoodConstraintSet.t) :=
    GoodConstraintSet.For_all valid_gc_constraint gcs.
    
  Lemma leq_level_n_complete z l l' :
    level_declared l ->
    level_declared l' ->
    leq_level_n z l l' ->
    leqb_level_n G z l l'.
  Proof.
    intros decll decll'.
    unfold leq_level_n.
    intros le; eapply gc_leq_universe_n_iff in le.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct gc_of_constraints; [cbn in *|contradiction HG].
    now apply (leqb_level_n_spec G _ Huctx' HC' HG' z l l' decll decll').
  Qed.

  Definition gc_levels_declared' (vset : VSet.t) gc :=
     match gc with
    | gc_le l _ l' => VSet.In (VariableLevel.to_noprop l) vset /\ 
      VSet.In (VariableLevel.to_noprop l') vset
     | gc_lt_set_level _ n | gc_le_level_set n _ =>
	     VSet.In (Level.Level n) vset
    | gc_le_set_var _ n | gc_le_var_set n _ => VSet.In (Level.Var n) vset
     end.
  
  Definition gcs_levels_declared (vset : VSet.t) gcs :=
    GoodConstraintSet.For_all (gc_levels_declared' vset) gcs.
  
  Lemma check_gc_constraint_complete cstr :
    gc_levels_declared' uctx.1 cstr ->
    valid_gc_constraint cstr ->
    check_gc_constraint G cstr.
  Proof.
    rewrite /check_gc_constraint.
    destruct check_univs eqn:cu => //=.
    destruct cstr; cbn; intros hin;
    apply leq_level_n_complete; intuition auto.
    all:apply Huctx.
  Qed.

  Lemma check_gc_constraints_complete cstrs :
    gcs_levels_declared uctx.1 cstrs ->
    valid_gc_constraints cstrs ->
    check_gc_constraints G cstrs.
  Proof.
    rewrite /gcs_levels_declared /valid_gc_constraints /check_gc_constraints
      /check_gc_constraints.
    intros hdecl hval.
    eapply GoodConstraintSetFact.for_all_iff. typeclasses eauto.
    intros cstr hcstr. specialize (hdecl cstr hcstr).
    specialize (hval cstr hcstr). eapply check_gc_constraint_complete => //.
  Qed.

  Definition valid_gc_constraints_ext gc :=
    forall v, satisfies v uctx.2 -> gc_satisfies v gc.

  Lemma valid_gc_constraints_aux gc :
    valid_gc_constraints_ext gc ->
    valid_gc_constraints gc.
  Proof.
    intros Hv v inv.
    unfold gc_satisfies in Hv.
    destruct v; cbn in *; red;
    intros v Hv'; specialize (Hv _ Hv');
    eapply GoodConstraintSetFact.for_all_iff in Hv; try typeclasses eauto;
    specialize (Hv _ inv); cbn in Hv; cbn; 
    rewrite ?val_level_of_variable_level //.

    now eapply Z.leb_le in Hv.
    eapply Nat.leb_le in Hv. lia. 
    apply Nat.leb_le in Hv. lia.
    apply Nat.leb_le in Hv. lia.
    apply Nat.leb_le in Hv. lia.
  Qed.

  Lemma valid_valid_gc cstrs gc :
    check_univs ->
    valid_constraints uctx.2 cstrs ->
    gc_of_constraints cstrs = Some gc ->
    valid_gc_constraints gc.
  Proof.
    intros cu Hgc vgc. apply valid_gc_constraints_aux.
    intros v Hv.
    pose proof (gc_of_constraints_spec v cstrs).
    rewrite vgc /= in H. apply H.
    rewrite /valid_constraints cu in Hgc. apply Hgc. apply Hv.
  Qed.

  Lemma gc_of_constraints_declared cstrs levels gc :
    global_uctx_invariants (levels, cstrs) ->
    gc_of_constraints cstrs = Some gc ->
    gcs_levels_declared levels gc.
  Proof.
    intros Hlev hc.
    pose proof (gc_of_uctx_invariants (levels, cstrs) (levels, gc)).
    cbn in H. rewrite hc in H. specialize (H eq_refl). now apply H.
  Qed.

  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints uctx.2 ctrs.
  Proof.
    unfold check_constraints, valid_constraints.
    case_eq (gc_of_constraints ctrs); [|try discriminate].
    intros ctrs' Hctrs' HH.
    epose proof (check_gc_constraints_spec _ uctx' Huctx' HC' HG' _ HH).
    destruct check_univs => //=.
    intros v Hv.
    cbn. 
    apply gc_of_constraints_spec.
    apply gc_of_constraints_spec in Hv.
    rewrite Hctrs'; cbn. eapply H.
    clear -HG Hv.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2) => //; cbn in uctx', HG.
  Qed.

  (* Completeness holds only for well-formed constraints sets *)
  Lemma check_constraints_complete ctrs :
    check_univs ->
    global_uctx_invariants (uctx.1, ctrs) ->
    valid_constraints uctx.2 ctrs -> 
    check_constraints G ctrs.
  Proof.
    intros cu gu vc.
    unfold check_constraints.
    case_eq (gc_of_constraints ctrs); [|try discriminate].
    2:{ destruct HC as [v Hv].
        pose proof (gc_of_constraints_spec v ctrs).
        intros.
        rewrite /valid_constraints cu in vc.
        specialize (vc v Hv).
        rewrite H0 in H. intuition. }
    intros cstr gc.
    eapply check_gc_constraints_complete.
    { eapply gc_of_constraints_declared. 2:tea. cbn. red in gu.  unfold is_graph_of_uctx, gc_of_uctx in HG.
      destruct (gc_of_constraints uctx.2) => //; cbn in uctx', HG. }
    eapply valid_valid_gc; tea.
  Qed.

End CheckLeq2.

(* Show proof irrelevance: we are using sets with canonical representations to represent the graph *)
Lemma graph_eq : forall (G G' : universes_graph),
    VSet.Equal G.1.1 G'.1.1
    -> EdgeSet.Equal G.1.2 G'.1.2
    -> G.2 = G'.2
    -> G = G'.
Proof.
  intros G G' veq eeq seq.
  destruct G as [[l e] s], G' as [[l' e'] s']. simpl.
  f_equal; auto.
  f_equal.
  now apply VSet.eq_leibniz.
  now apply EdgeSet.eq_leibniz.
Qed.

Require Import ssreflect.
Require Import MSetDecide.
Module EdgeSetDecide := WDecide (EdgeSet).
Module GoodConstraintSetDecide := WDecide (GoodConstraintSet).
Module GCS := GoodConstraintSet.
Ltac esets := EdgeSetDecide.fsetdec.
Ltac gcsets := GoodConstraintSetDecide.fsetdec.

Section AddLevelsCstrs.

  Definition add_uctx (uctx : VSet.t × GoodConstraintSet.t)
             (G : universes_graph) : universes_graph
    := let levels := VSet.union uctx.1 G.1.1 in
       let edges := add_level_edges uctx.1 G.1.2 in
       let edges := add_cstrs uctx.2 edges in
       (levels, edges, G.2).

  Definition uctx_of_udecl u : ContextSet.t :=
    (levels_of_udecl u, constraints_of_udecl u).

  Lemma gcs_elements_union s s' : GoodConstraintSet.Empty s' -> 
    GoodConstraintSet.Equal (GoodConstraintSet.union s s') s.
  Proof. gcsets. Qed.

  Lemma add_level_edges_spec e x g : 
    EdgeSet.In e (add_level_edges x g) <->
    (exists c, option_edge_of_level c = Some e /\ VSet.In c x) \/ EdgeSet.In e g.
  Proof.
    rewrite /add_level_edges VSet.fold_spec.
    setoid_rewrite (VSetFact.elements_iff x). setoid_rewrite InA_In_eq at 2.
    induction (VSet.elements x) in g |- *; simpl.
    intuition auto. now destruct H0 as [c [_ F]].
    rewrite {}IHl.
    split.
    * intros [[c [eq inl]]|?]; firstorder auto.
      destruct a; simpl in *; auto.
      rewrite -> EdgeSet.add_spec in H. intuition auto.
      subst e. left; exists (Level.Level s); intuition auto.
      rewrite -> EdgeSet.add_spec in H. intuition auto.
      subst e. left; eexists; intuition eauto. reflexivity.
    * intros [[[] [[= <-] [->|inl]]]|?]; simpl; auto;
      rewrite -> ?EdgeSet.add_spec; simpl; intuition auto.
      left. exists (Level.Level s); auto.
      left. exists (Level.Var n); auto.
      destruct a; simpl; rewrite -> ?EdgeSet.add_spec; simpl; intuition auto.
  Qed.

  Lemma add_cstrs_union g ctrs1 ctrs2 : 
    add_cstrs (GoodConstraintSet.union ctrs1 ctrs2) g =
    add_cstrs ctrs1 (add_cstrs ctrs2 g).
  Proof.
    apply edgeset_equal. intros e.
    rewrite !add_cstrs_spec.
    setoid_rewrite GoodConstraintSet.union_spec.
    firstorder eauto.
  Qed.

  Lemma add_level_edges_union g l1 l2 :
    add_level_edges (VSet.union l1 l2) g =
    add_level_edges l1 (add_level_edges l2 g).
  Proof.
    apply edgeset_equal. intros e.
    rewrite !add_level_edges_spec.
    setoid_rewrite VSet.union_spec.
    firstorder eauto.
  Qed.

  Lemma add_level_edges_add_cstrs_comm l c g : 
    add_level_edges l (add_cstrs c g) = 
    add_cstrs c (add_level_edges l g).
  Proof.
    apply edgeset_equal. intros e.
    rewrite !add_level_edges_spec !add_cstrs_spec add_level_edges_spec.
    firstorder auto.
  Qed.

  Lemma add_uctx_make_graph levels1 levels2 ctrs1 ctrs2
  : add_uctx (levels1, ctrs1) (make_graph (levels2, ctrs2))
    = make_graph (VSet.union levels1 levels2,
                  GoodConstraintSet.union ctrs1 ctrs2).
  Proof.
    rewrite /make_graph /= /add_uctx /=.
    f_equal. f_equal. unfold GoodConstraintSet.t in ctrs1.
    rewrite add_cstrs_union. f_equal.
    rewrite add_level_edges_union.
    now rewrite add_level_edges_add_cstrs_comm.
  Qed.

  Definition gc_result_eq (x y : option GoodConstraintSet.t) :=
    match x, y with
    | Some x, Some y => GoodConstraintSet.eq x y
    | None, None => True
    | _, _ => False
    end.

  Lemma add_gc_of_constraint_spec {cf:checker_flags} gc t :
    match add_gc_of_constraint gc (Some t) with
    | Some t' => 
      exists gcs, gc_of_constraint gc = Some gcs /\
      GCS.Equal t' (GCS.union t gcs)
    | None => gc_of_constraint gc = None
    end.
  Proof.
    unfold add_gc_of_constraint.
    simpl.
    destruct gc_of_constraint; simpl; auto.
    eexists; split; eauto. reflexivity.
  Qed.

  Lemma fold_left_add_gc_None {cf:checker_flags} l : fold_left (fun a e => add_gc_of_constraint e a) l None = None.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma fold_left_add_gc_Some_subset {cf:checker_flags} l t t':
    fold_left (fun a e => add_gc_of_constraint e a) l (Some t) = Some t' ->
    GCS.Subset t t'.
  Proof.
    induction l in t |- *; simpl; auto. intros [= ->]. reflexivity.
    pose proof (add_gc_of_constraint_spec a t).
    destruct add_gc_of_constraint; simpl.
    intros. specialize (IHl _ H0).
    destruct H as [gcs [gca eq]].
    rewrite -> eq in IHl. gcsets.
    now rewrite fold_left_add_gc_None.
  Qed.

  Variant gc_of_constraints_view {cf:checker_flags} (s : ConstraintSet.t) : option GoodConstraintSet.t -> Type := 
  | gc_of_constraints_ok l : 
    (forall gc, GoodConstraintSet.In gc l <-> 
    (exists c gcs, gc_of_constraint c = Some gcs /\ ConstraintSet.In c s /\ GoodConstraintSet.In gc gcs)) ->
    (forall c, ConstraintSet.In c s -> 
      exists gcs, gc_of_constraint c = Some gcs /\ GoodConstraintSet.Subset gcs l) ->
    gc_of_constraints_view s (Some l)
  | gc_of_constraints_none :
    (exists c, ConstraintSet.In c s /\ gc_of_constraint c = None) ->
    gc_of_constraints_view s None.

  Lemma gc_of_constraintsP {cf:checker_flags} s : gc_of_constraints_view s (gc_of_constraints s).
  Proof.
    unfold gc_of_constraints.
    rewrite ConstraintSet.fold_spec.
    destruct fold_left eqn:eq.
    - constructor.
      + intros.
        setoid_rewrite ConstraintSetFact.elements_iff; setoid_rewrite InA_In_eq at 2.
        transitivity ((exists (c : UnivConstraint.t) (gcs : GoodConstraintSet.t),
          gc_of_constraint c = Some gcs /\
          In c (ConstraintSet.elements s) /\ GoodConstraintSet.In gc gcs) \/ GCS.In gc GCS.empty).
        2:gcsets.
        revert eq.
        generalize (GCS.empty).
        induction (ConstraintSet.elements s) in t0 |- *; simpl in *.
        intros ? [= ->]. firstorder auto.
        intros t' Ht'.
        pose proof (add_gc_of_constraint_spec a t').
        destruct add_gc_of_constraint eqn:addgc.
        destruct H as [gcs [gceq cseq]].
        specialize (IHl _ _ Ht').
        rewrite {}IHl.
        rewrite cseq GCS.union_spec.
        split.
        * intros [[c [gcs' [gceq' [incl ingcgcs']]]]|[]]; auto.
          left. exists c, gcs'; intuition auto.
          left.
          exists a, gcs; intuition auto.
        * intros [[c [gcs' [gceq' [[->|incl] ingcgcs']]]]|?]; auto.
          ++ rewrite gceq in gceq'. noconf gceq'. auto.
          ++ left. exists c, gcs'. intuition auto.
        * rewrite fold_left_add_gc_None in Ht'. discriminate.
      + intros c.
        setoid_rewrite ConstraintSetFact.elements_iff; setoid_rewrite InA_In_eq at 1.
        revert eq.
        generalize (GCS.empty).
        induction (ConstraintSet.elements s) in t0 |- *; simpl in *.
        intros ? [= ->]. firstorder auto.
        intros t' Ht'.
        pose proof (add_gc_of_constraint_spec a t').
        destruct add_gc_of_constraint eqn:addgc.
        destruct H as [gcs [gceq cseq]].
        specialize (IHl _ _ Ht').
        intros [->|incl]. eexists; split; eauto.
        intros gc gcin.
        apply fold_left_add_gc_Some_subset in Ht'.
        rewrite -> cseq in Ht'. gcsets.
        now specialize (IHl incl).
        now rewrite fold_left_add_gc_None in Ht'.
    - constructor.
      setoid_rewrite ConstraintSetFact.elements_iff; setoid_rewrite InA_In_eq at 1.
      revert eq.
      generalize GCS.empty.
      induction (ConstraintSet.elements s); simpl in * => //.
      intros t' eq.
      pose proof (add_gc_of_constraint_spec a t').
      destruct add_gc_of_constraint eqn:addgc.
      destruct H as [gcs [gceq cseq]].
      specialize (IHl _ eq).
      destruct IHl as [c [incl gcn]].
      exists c; intuition auto.
      exists a; intuition auto.
  Qed.

  Lemma gc_of_constraints_union {cf:checker_flags} S S' :
    gc_result_eq (gc_of_constraints (ConstraintSet.union S S'))
      (S1 <- gc_of_constraints S ;;
      S2 <- gc_of_constraints S' ;;
      ret (GoodConstraintSet.union S1 S2)).
  Proof.
    case: (gc_of_constraintsP S) => [GS HS HS0|[c [incs gcn]]]; simpl.
    case: (gc_of_constraintsP S') => [GS' HS' HS'0|GS']; simpl.
    case: (gc_of_constraintsP (ConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c [inc gcn]]].
    simpl.
    - intros gc.
      rewrite HSS' GCS.union_spec HS HS'.
      setoid_rewrite ConstraintSet.union_spec.
      split. intros [c [gcs ?]]. intuition auto.
      left; firstorder auto.
      right; firstorder auto.
      intros [[c [gcs ?]]|[c [gcs ?]]]; exists c, gcs; intuition auto.
    - cbn. apply ConstraintSet.union_spec in inc.
      destruct inc.
      specialize (HS0 _ H). rewrite gcn in HS0. now destruct HS0.
      specialize (HS'0 _ H). rewrite gcn in HS'0. now destruct HS'0.
    - destruct GS' as [c [inc gcn]].
      case: (gc_of_constraintsP (ConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c' [inc' gcn']]].
      cbn.
      specialize (HSS'0 c).
      rewrite -> ConstraintSet.union_spec in HSS'0.
      specialize (HSS'0 (or_intror inc)) as [gcs [eq _]].
      now congruence.
      split.
    - case: (gc_of_constraintsP (ConstraintSet.union S S')) => [GSS' HSS' HSS'0|[c' [inc' gcn']]].
      cbn.
      specialize (HSS'0 c).
      rewrite -> ConstraintSet.union_spec in HSS'0.
      specialize (HSS'0 (or_introl incs)) as [gcs [eq _]].
      now congruence.
      split.
  Qed.

End AddLevelsCstrs.
