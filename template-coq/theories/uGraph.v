Require Import Nat Bool String BinInt List Relations Lia.
Import ListNotations.
Require Import MSetFacts MSetProperties.
From MetaCoq.Template Require Import utils config Universes wGraph.
Import ConstraintType.
Local Open Scope nat_scope.

Definition on_Some {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => False
        end.

Definition on_Some_or_None {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => True
        end.


Module ConstraintSetFact := WFactsOn UnivConstraintDec ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraintDec ConstraintSet.



Inductive variable_level := mLevel (_ : string) | mVar (_ : nat).

Inductive good_constraint :=
(* l <= l' *)
| gc_le : variable_level -> variable_level -> good_constraint
(* l < l' *)
| gc_lt : variable_level -> variable_level -> good_constraint
(* Set < Var n *)
| gc_lt_set : nat -> good_constraint
(* Set = Var n *)
| gc_eq_set : nat -> good_constraint.


Module GoodConstraintDec.
  Definition t : Set := good_constraint.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition variable_level_dec : forall x y : variable_level, {x = y} + {x <> y}.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. all: try apply variable_level_dec.
    all: apply Peano_dec.eq_nat_dec.
  Defined.
End GoodConstraintDec.
Module GoodConstraintSet := MSets.MSetWeakList.Make GoodConstraintDec.
Module GoodConstraintSetFact := WFactsOn GoodConstraintDec GoodConstraintSet.
Module GoodConstraintSetProp := WPropertiesOn GoodConstraintDec GoodConstraintSet.

Definition GoodConstraintSet_pair x y
  := GoodConstraintSet.add y (GoodConstraintSet.singleton x).

Definition gc_val0 (v : valuation) (l : variable_level) : nat :=
  match l with
  | mLevel s => Pos.to_nat (v.(valuation_mono) s)
  | mVar x => v.(valuation_poly) x
  end.

Definition gc_satisfies0 v (gc : good_constraint) : bool :=
  match gc with
  | gc_le l l' => gc_val0 v l <=? gc_val0 v l'
  | gc_lt l l' => gc_val0 v l <? gc_val0 v l'
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
  cbn; destruct (GoodConstraintDec.eq_dec gc2 gc1); cbn;
    rewrite if_true_false.
  now destruct e. symmetry. apply andb_and.
Defined.

(* None -> not satisfiable *)
(* Some empty -> useless *)
(* else: singleton or two elements set (l = l' -> {l<=l', l'<=l}) *)
Definition gc_of_constraint (uc : univ_constraint) : option GoodConstraintSet.t
  := let empty := Some GoodConstraintSet.empty in
     let singleton := fun x => Some (GoodConstraintSet.singleton x) in
     let pair := fun x y => Some (GoodConstraintSet_pair x y) in
     match uc with
     (* Prop _ _ *)
     | (Level.lProp, Le, _) => empty
     | (Level.lProp, Eq, Level.lProp) => empty
     | (Level.lProp, Eq, _) => None
     | (Level.lProp, Lt, Level.lProp) => None
     | (Level.lProp, Lt, _) => empty

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
       => singleton (gc_le (mLevel l) (mLevel l'))
     | (Level.Level l, Le, Level.Var n) => singleton (gc_le (mLevel l) (mVar n))
     | (Level.Level _, Eq, Level.lProp) => None
     | (Level.Level _, Eq, Level.lSet) => None
     | (Level.Level l, Eq, Level.Level l')
       => pair (gc_le (mLevel l) (mLevel l')) (gc_le (mLevel l') (mLevel l))
     | (Level.Level l, Eq, Level.Var n)
       => pair (gc_le (mLevel l) (mVar n)) (gc_le (mVar n) (mLevel l))
     | (Level.Level _, Lt, Level.lProp) => None
     | (Level.Level _, Lt, Level.lSet) => None
     | (Level.Level l, Lt, Level.Level l')
       => singleton (gc_lt (mLevel l) (mLevel l'))
     | (Level.Level l, Lt, Level.Var n) => singleton (gc_lt (mLevel l) (mVar n))

     (* Var _ _ *)
     | (Level.Var _, Le, Level.lProp) => None
     | (Level.Var n, Le, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Le, Level.Level l) => singleton (gc_le (mVar n) (mLevel l))
     | (Level.Var n, Le, Level.Var n') => singleton (gc_le (mVar n) (mVar n'))
     | (Level.Var _, Eq, Level.lProp) => None
     | (Level.Var n, Eq, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Eq, Level.Level l)
       => pair (gc_le (mVar n) (mLevel l)) (gc_le (mLevel l) (mVar n))

     | (Level.Var n, Eq, Level.Var n')
       => pair (gc_le (mVar n) (mVar n')) (gc_le (mVar n') (mVar n))
     | (Level.Var _, Lt, Level.lProp) => None
     | (Level.Var _, Lt, Level.lSet) => None
     | (Level.Var n, Lt, Level.Level l) => singleton (gc_lt (mVar n) (mLevel l))
     | (Level.Var n, Lt, Level.Var n') => singleton (gc_lt (mVar n) (mVar n'))
     end.


Ltac gc_of_constraint_tac :=
  match goal with
  | |- is_true (if _ then true else false) => rewrite if_true_false
  | |- is_true (_ <? _) => apply PeanoNat.Nat.ltb_lt
  | |- is_true (_ <=? _) => apply PeanoNat.Nat.leb_le
  | |- is_true (_ =? _) => apply PeanoNat.Nat.eqb_eq
  | |- is_true (gc_satisfies _ (GoodConstraintSet_pair _ _))
               => apply gc_satisfies_pair; cbn -[Nat.leb Nat.eqb]; split
  | H : is_true (if _ then true else false) |- _ => rewrite if_true_false in H
  | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
  | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
  | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
  | H : is_true (gc_satisfies _ (GoodConstraintSet_pair _ _)) |- _
               => apply gc_satisfies_pair in H; cbn -[Nat.leb Nat.eqb] in H;
                 destruct H
  end.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (gc_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1; destruct l, l'; try constructor; try reflexivity.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *.
    all: repeat gc_of_constraint_tac; lia.
  - destruct uc as [[[] []] []]; simpl; try (now inversion 1); constructor.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *; try lia.
    all: repeat gc_of_constraint_tac; lia.
Qed.

Definition add_gc_of_constraint uc (S : option GoodConstraintSet.t)
  := match S with
     | None => None
     | Some S1 => match gc_of_constraint uc with
                 | None => None
                 | Some S2 => Some (GoodConstraintSet.union S1 S2)
                 end
     end.

Definition gc_of_constraints (ctrs : constraints) : option GoodConstraintSet.t
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
  transitivity ((forall uc, InA eq uc l -> satisfies0 v uc) /\
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



Definition gc_leq_universe_n n ctrs u u'
  := forall v, gc_satisfies v ctrs -> (Z.of_nat n + val v u <= val v u')%Z.


Lemma gc_leq_universe_iff n ctrs u u' :
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



(* no_prop_levels of the graph are levels which are not Prop *)
(* vtn : variable to no_prop *)
Inductive no_prop_level := lSet | vtn (l : variable_level).

Coercion vtn : variable_level >-> no_prop_level.

Lemma transitive_string_lt : Transitive string_lt.
Proof.
  intro s; induction s; unfold string_lt.
  - induction y; cbn. intuition.
Admitted.

Lemma CompareSpec_string s s'
  : CompareSpec (s = s') (string_lt s s') (string_lt s' s) (string_compare s s').
Proof.
  revert s'; induction s; intro s'; cbn.
  - destruct s'; constructor; reflexivity.
  - destruct s'. constructor; reflexivity.
Admitted.

Lemma CompareSpec_Proper : Proper (iff ==> iff ==> iff ==> Logic.eq ==> iff) CompareSpec.
  intros A A' HA B B' HB C C' HC c c' [].
  destruct c; split; inversion 1; constructor; intuition.
Qed.

Module GcLevel.
  Definition t := variable_level.
  Definition lt : t -> t -> Prop :=
    fun x y => match x, y with
            | mLevel _, mVar _ => True
            | mLevel s, mLevel s' => string_lt s s'
            | mVar n, mVar n' => n < n'
            | mVar _, mLevel _ => False
            end.
  Definition lt_strorder : StrictOrder lt.
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
            | mLevel _, mVar _ => Datatypes.Lt
            | mLevel s, mLevel s' => string_compare s s'
            | mVar n, mVar n' => Nat.compare n n'
            | mVar _, mLevel _ => Datatypes.Gt
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
End GcLevel.

Module No_Prop_LevelDec.
  Definition t : Set := no_prop_level.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition lt : t -> t -> Prop :=
    fun x y => match x, y with
            | lSet, lSet => False
            | lSet, vtn _ => True
            | vtn v, vtn v' => GcLevel.lt v v'
            | vtn _, lSet => False
            end.
  Definition lt_strorder : StrictOrder lt.
    split.
    - intros [|v] H; cbn in H; intuition.
      now apply GcLevel.lt_strorder in H.
    - intros [|v1] [|v2] [|v3]; cbn; intuition.
      eapply GcLevel.lt_strorder; eassumption.
  Qed.
  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1, H2.
  Qed.
  Definition compare : t -> t -> comparison :=
    fun x y => match x, y with
            | lSet, lSet => Datatypes.Eq
            | lSet, vtn _ => Datatypes.Lt
            | vtn v, vtn v' => GcLevel.compare v v'
            | vtn _, lSet => Datatypes.Gt
            end.
  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
    intros [|v] [|v']; cbn; try now constructor.
    destruct (GcLevel.compare_spec v v'); constructor; congruence.
  Qed.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality. apply GcLevel.eq_dec.
  Defined.
End No_Prop_LevelDec.


Module Import wGraph := wGraph.WeightedGraph No_Prop_LevelDec.

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

Definition edge_of_level (l : variable_level) : EdgeSet.elt :=
  match l with
  | mLevel l => (lSet, 1, vtn (mLevel l))
  | mVar n => (lSet, 0, vtn (mVar n))
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edges_of_constraint (gc : good_constraint) : list EdgeSet.elt :=
  match gc with
  | gc_le l l' => [edge_of_level l; edge_of_level l'; (vtn l, 0, vtn l')]
  | gc_lt l l' => [edge_of_level l; edge_of_level l'; (vtn l, 1, vtn l')]
  | gc_lt_set n => [(lSet, 1, vtn (mVar n))]
  | gc_eq_set n => [(vtn (mVar n), 0, lSet); (lSet, 0, vtn (mVar n))]
  end.

Definition add_edges edges := fold_left add_edge edges.

Definition add_gc_constraint := add_edges ∘ edges_of_constraint.

Definition add_gc_constraints := GoodConstraintSet.fold add_gc_constraint.

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

Lemma Paths_add_edge {G e x y} : Paths G x y -> Paths (add_edge G e) x y.
Proof.
  induction 1 as [|x y z e' p p']. constructor.
  econstructor. 2: eassumption.
  exists e'.π1. apply EdgeSet.add_spec; right; exact e'.π2.
Defined.

Lemma Paths_add_edge' {G n x y} : Paths (add_edge G (x, n, y)) x y.
  econstructor. eexists.
  eapply EdgeSet.add_spec. left; reflexivity.
  constructor.
Defined.


Ltac paths :=
  match goal with
  | |- Paths _ ?x ?x => constructor
  (* | H : Edges ?G ?x ?y |- Paths ?G ?x ?y => econstructor; [eapply H|reflexivity] *)
  (* | H : Paths _ ?x ?y |- Paths _ ?x ?y => eassumption *)
  | |- _ => eassumption
  | H : _ |- Paths _ ?x ?y => eapply Paths_add_edge'
  | H : _ |- Paths _ ?x ?y => eapply Paths_add_edge; paths
  (* | |- _ => econstructor; paths *)
  end.

Ltac rdestruct H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [rdestruct H|rdestruct H]
  | _ /\ _ => let H' := fresh H in
            destruct H as [H|H']; [rdestruct H|rdestruct H']
  | _ => idtac
  end.

Lemma add_gc_constraint_invariants {G} (HG : invariants G)
      (HG' : wGraph.s G = lSet) {gc}
  : invariants (add_gc_constraint gc G).
Proof.
  destruct HG as [H1 [H2 H3]].
  destruct gc as [g g0|g g0|n|n].
  - split; [intros e H; split|split]; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      rdestruct H; subst; cbn. 4: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets.
      rdestruct H; subst; cbn. 4: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets. repeat right; assumption.
    + intros x H.
      match goal with
      | |- ∥ Paths ?X _ _ ∥ => set (G' := X)
      end.
      simplify_sets.
      rdestruct H; subst. 
      2-4: sq; destruct g0; cbn in *; paths.
      1-3: sq; destruct g; cbn in *; paths.
      specialize (H3 _ H); sq; paths.
  (* This bullet is a copy and paste of the first one *)
  - split; [intros e H; split|split]; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      rdestruct H; subst; cbn. 4: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets.
      rdestruct H; subst; cbn. 4: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets. repeat right; assumption.
    + intros x H.
      match goal with
      | |- ∥ Paths ?X _ _ ∥ => set (G' := X)
      end.
      simplify_sets.
      rdestruct H; subst. 
      2-4: sq; destruct g0; cbn in *; paths.
      1-3: sq; destruct g; cbn in *; paths.
      specialize (H3 _ H); sq; paths.
  - split; [intros e H; split|split]; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      rdestruct H; subst; cbn. 2: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets.
      rdestruct H; subst; cbn. 2: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets. repeat right; assumption.
    + intros x H.
      match goal with
      | |- ∥ Paths ?X _ _ ∥ => set (G' := X)
      end.
      simplify_sets.
      rdestruct H; subst. 
      3: specialize (H3 _ H). all: sq; paths.
  - split; [intros e H; split|split]; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      rdestruct H; subst; cbn. 3: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets.
      rdestruct H; subst; cbn. 3: destruct (H1 _ H).
      all: auto 7.
    + simplify_sets. repeat right; assumption.
    + intros x H.
      match goal with
      | |- ∥ Paths ?X _ _ ∥ => set (G' := X)
      end.
      simplify_sets.
      rdestruct H; subst. 
      5: specialize (H3 _ H). all: sq; paths.
Qed.

Definition make_graph (ctrs : GoodConstraintSet.t) : universes_graph
  := add_gc_constraints ctrs init_graph.

Definition labelling_of_valuation (v : valuation) : labelling
  := fun x => match x with
           | lSet => 0
           | vtn (mLevel l) => Pos.to_nat (v.(valuation_mono) l)
           | vtn (mVar n) => v.(valuation_poly) n
           end.

Definition valuation_of_labelling (l : labelling) : valuation
  := {| valuation_mono := fun s => Pos.of_nat (l (vtn (mLevel s)));
        valuation_poly := fun n => l (vtn (mVar n)) |}.


Lemma make_graph_ind (P : t -> Prop) (P0 : P init_graph)
      (P1 : forall G gc, P G -> P (add_gc_constraint gc G))
      : forall ctrs, P (make_graph ctrs).
Proof.
  unfold make_graph, add_gc_constraints.
  intro ctrs. rewrite GoodConstraintSet.fold_spec.
  set (G := init_graph) in *. clearbody G; revert G P0.
  set (l := GoodConstraintSet.elements ctrs); induction l.
  - easy.
  - intros G P0; cbn. apply IHl. now apply P1.
Qed.

Definition add_edges_E := fold_left (fun E0 e => EdgeSet.add e E0).

Lemma edges_add_edge G E :
  wGraph.E (add_edges E G) = add_edges_E E (wGraph.E G).
Proof.
  revert G; induction E; cbn; intro G. reflexivity.
  apply IHE.
Qed.

Lemma In_add_edges lE SE e
  : EdgeSet.In e (add_edges_E lE SE) <-> In e lE \/ EdgeSet.In e SE.
Proof.
  revert SE. induction lE; cbn.
  - intuition.
  - intros SE; split; intro H.
    pose proof (proj1 (IHlE _) H) as HH; clear IHlE H.
    destruct HH. intuition. simplify_sets. destruct H; auto.
    apply IHlE. destruct H as [[|]|].
    right; simplify_sets. all: intuition.
Qed.


Lemma InA_In_eq {A} x (l : list A) : InA eq x l <-> In x l.
Proof.
  etransitivity. eapply InA_alt.
  firstorder. now subst.
Qed.


Section MakeGraph.
  Context (ctrs : GoodConstraintSet.t).
  Let G : universes_graph := make_graph ctrs.

  Lemma make_graph_invariants : invariants G /\ wGraph.s G = lSet.
  Proof.
    subst G; apply make_graph_ind; clear ctrs.
    - split. apply init_graph_invariants. reflexivity.
    - intros G gc HG; split. 
      + now apply add_gc_constraint_invariants.
      + destruct HG as [_ HG].
        revert G HG. unfold add_gc_constraint.
        induction (edges_of_constraint gc). easy.
        intros G HG. cbn; apply IHl; assumption.
  Qed.

  Definition source_make_graph := proj2 make_graph_invariants.

  Instance invariants_make_graph : invariants G
    := proj1 make_graph_invariants.

  Definition vtn_inj x y : vtn x = vtn y -> x = y.
  Proof.
    now inversion 1.
  Defined.

  Definition vtn_lSet x : vtn x <> lSet.
  Proof.
    now inversion 1.
  Defined.

  Lemma source_edge_of_level g : (edge_of_level g)..s = lSet.
  Proof.
    destruct g; reflexivity.
  Qed.

  Lemma target_edge_of_level g : (edge_of_level g)..t = g.
  Proof.
    destruct g; reflexivity.
  Qed.


  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x (wGraph.V G)
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof.
    destruct x; cbn.
    - intros _. apply proj1 in Hl; cbn in Hl.
      etransitivity. symmetry; eassumption.
      f_equal. apply source_make_graph.
    - destruct l0; cbn. 2: reflexivity.
      intro Hs. apply Nat2Pos.id.
      assert (HH: EdgeSet.In (lSet, 1, vtn (mLevel s)) (wGraph.E G)). {
        clear l Hl; subst G. revert s Hs.
        apply make_graph_ind; clear ctrs.
        - intros l H; cbn in *; simplify_sets. inversion H.
        - intros G gc HG l H.
          destruct gc; cbn in *; simplify_sets.
          + rewrite !source_edge_of_level, !target_edge_of_level in H. right.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply vtn_inj in H. subst; auto.
            firstorder.
          + rewrite !source_edge_of_level, !target_edge_of_level in H. right.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply vtn_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply vtn_inj in H. subst; auto.
            firstorder.
          + destruct H. inversion H.
            destruct H. inversion H. firstorder.
          + destruct H. inversion H.
            destruct H. inversion H.
            destruct H. inversion H.
            destruct H. inversion H. firstorder. }
      apply (proj2 Hl) in HH; cbn in HH. lia.
  Qed.


  Lemma edges_make_graph :
    wGraph.E G =
    GoodConstraintSet.fold (fun gc E => add_edges_E (edges_of_constraint gc) E)
                           ctrs EdgeSet.empty.
  Proof.
    subst G; unfold make_graph, add_gc_constraints.
    rewrite !GoodConstraintSet.fold_spec.
    set (ctrs' := GoodConstraintSet.elements ctrs); clearbody ctrs'; clear ctrs.
    set (G := init_graph).
    change EdgeSet.empty with (wGraph.E G).
    clearbody G; revert G.
    induction ctrs'; cbn.
    - reflexivity.
    - intros G. rewrite IHctrs'. f_equal. apply edges_add_edge.
  Qed.

  Lemma edges_make_graph' e :
    EdgeSet.In e (wGraph.E G) <-> 
    (GoodConstraintSet.Exists (fun gc => In e (edges_of_constraint gc)) ctrs).
  Proof.
    rewrite edges_make_graph. clear G.
    rewrite !GoodConstraintSet.fold_spec.
    etransitivity. shelve.
    eapply iff_ex.
    intro x. eapply and_iff_compat_r. symmetry; etransitivity.
    eapply GoodConstraintSetProp.FM.elements_iff. eapply InA_In_eq.
    Unshelve.
    set (ctrs' := GoodConstraintSet.elements ctrs) in *.
    clearbody ctrs'; clear ctrs.
    set (SE := EdgeSet.empty) in *.
    transitivity ((exists gc, In gc ctrs' /\ In e (edges_of_constraint gc))
                  \/ EdgeSet.In e SE).
    2: etransitivity; [eapply or_iff_compat_l, EdgeSetFact.empty_iff|intuition].
    clearbody SE; revert SE. induction ctrs'; cbn; intros SE; split.
    - now right.
    - firstorder.
    - intro H. specialize (IHctrs' (add_edges_E (edges_of_constraint a) SE)).
      apply proj1 in IHctrs'.
      specialize (IHctrs' H); clear H.
      destruct IHctrs'. left. firstorder.
      apply In_add_edges in H. destruct H; firstorder.
    - intro H. apply IHctrs'. clear -H.
      eapply or_iff_compat_l. apply In_add_edges.
      destruct H as [[gc [[H1|H1] H2]]|H]; subst; firstorder.
  Qed.


  Lemma make_graph_spec v :
    gc_satisfies v ctrs <-> correct_labelling G (labelling_of_valuation v).
  Proof.
    unfold gc_satisfies, correct_labelling. split; intro H.
    - split. now rewrite source_make_graph.
      intros e He. 
      apply edges_make_graph' in He.
      destruct He as [gc [H0 H1]].
      apply GoodConstraintSet.for_all_spec in H.
      2: intros x y []; reflexivity.
      specialize (H _ H0). cbn in *.
      clear -H H1.
        destruct gc as [g g0|g g0|n|n]; try apply PeanoNat.Nat.leb_le in H.
      + destruct H1; subst. rewrite source_edge_of_level.
        destruct g; cbn; lia.
        destruct H0; subst. rewrite source_edge_of_level.
        destruct g0; cbn; lia.
        destruct H0 as [|[]]; subst. destruct g, g0; cbn in *; lia.
      + destruct H1; subst. rewrite source_edge_of_level.
        destruct g; cbn; lia.
        destruct H0; subst. rewrite source_edge_of_level.
        destruct g0; cbn; lia.
        destruct H0 as [|[]]; subst. destruct g, g0; cbn in *; lia.
      + destruct H1 as [|[]]; subst. cbn. assumption. 
      + destruct H1 as [|[|[]]]; subst; cbn.
        apply PeanoNat.Nat.eqb_eq in H. lia. lia.
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (fun e p => proj2 (edges_make_graph' e)
                                (ex_intro _ gc (conj Hgc p))) as H0.
      destruct H as [_ H].
      pose proof (fun e p => H e (H0 e p)) as HH. clear -HH.
        destruct gc as [g g0|g g0|n|n]; cbn in HH; try apply PeanoNat.Nat.leb_le.
      4: apply PeanoNat.Nat.eqb_eq.
      simple refine (let HH' := HH (vtn g, 0, vtn g0) _ in _);
        [intuition|clearbody HH'; clear HH];
        destruct g, g0; cbn in *; lia.
      simple refine (let HH' := HH (vtn g, 1, vtn g0) _ in _);
        [intuition|clearbody HH'; clear HH];
        destruct g, g0; cbn in *; lia.
      simple refine (let HH' := HH (lSet, 1, vtn (mVar n)) _ in _);
        [intuition|clearbody HH'; clear HH];
        cbn in *; lia.
      simple refine (let HH' := HH (vtn (mVar n), 0, lSet) _ in _);
        [intuition|clearbody HH'; clear HH];
        cbn in *; lia.
  Qed.


  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) ctrs <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) ctrs.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling; intuition.
    now rewrite source_make_graph.
    pose proof invariants_make_graph.
    rewrite !valuation_labelling_eq; firstorder. 
  Qed.

  Corollary make_graph_spec2 :
    gc_consistent ctrs <-> exists l, correct_labelling G l.
  Proof.
    split.
    - intros [v H]. exists (labelling_of_valuation v).
      apply make_graph_spec. assumption.
    - intros [l Hl]. exists (valuation_of_labelling l).
      apply make_graph_spec'. assumption.
  Defined.

  Corollary consistent_no_loop : gc_consistent ctrs -> acyclic_no_loop G.
  Proof.
    intro. apply acyclic_caract1, make_graph_spec2.
    exact _. assumption.
  Defined.
End MakeGraph.

Existing Instance invariants_make_graph.
Existing Class acyclic_no_loop.
Existing Class gc_consistent.
Existing Instance consistent_no_loop.

(** ** Check of consistency ** *)

Definition is_consistent (ctrs : constraints) :=
  match gc_of_constraints ctrs with
  | Some ctrs => is_acyclic (make_graph ctrs)
  | None => false
  end.

Lemma is_consistent_spec ctrs
  : is_consistent ctrs <-> consistent ctrs.
Proof with try exact _.
  etransitivity. 2: symmetry; apply gc_consistent_iff.
  unfold is_consistent.
  destruct (gc_of_constraints ctrs) as [ctrs'|]; clear ctrs; cbn.
  2: split; [discriminate|inversion 1].
  etransitivity. apply is_acyclic_spec...
  etransitivity. apply acyclic_caract1...
  symmetry; apply make_graph_spec2.
Qed.


Section CheckLeq.

  (** ** Check of leq ** *)

  Definition level_of_variable l :=
    match l with
    | mLevel s => Level.Level s
    | mVar n => Level.Var n
    end.

  Definition level_of_no_prop l :=
    match l with
    | lSet => Level.lSet
    | vtn l => level_of_variable l
    end.

  Coercion level_of_no_prop : no_prop_level >-> Level.t.

  Lemma val_level_of_variable_level v (l : variable_level)
    : val0 v l = Z.of_nat (gc_val0 v l).
  Proof.
    destruct l; cbn; lia.
  Qed.

  Lemma labelling_of_valuation_val0 v (l : no_prop_level)
    : Z.of_nat (labelling_of_valuation v l) = val0 v l.
  Proof.
    destruct l; cbn. reflexivity.
    destruct l; cbn; rewrite ?Z_of_pos_alt; reflexivity.
  Qed.

  Context (G : universes_graph) (ctrs : GoodConstraintSet.t)
          (HG1 : make_graph ctrs = G) (HG2 : gc_consistent ctrs).

  Lemma leq_universe_vertices0 (HC : gc_consistent ctrs) n l l'
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l')
      -> leq_vertices G n l l'.
  Proof.
    subst G. intros H v Hv.
    pose proof (H _ (make_graph_spec' _ _ Hv)) as HH.
    rewrite <- (valuation_labelling_eq _ _ Hv l Hl).
    rewrite <- (valuation_labelling_eq _ _ Hv l' Hl').
    pose proof (labelling_of_valuation_val0 (valuation_of_labelling v) l).
    pose proof (labelling_of_valuation_val0 (valuation_of_labelling v) l').
    cbn in *; lia.
  Qed.

  Definition constrained l
    := l = lSet
       \/ exists e, GoodConstraintSet.Exists
                (fun gc => In e (edges_of_constraint gc) /\ (e..s = l \/ e..t = l)) ctrs.

  Definition constrained_dec l
    : {constrained l} + {~ constrained l}.
  Proof.
    destruct (No_Prop_LevelDec.eq_dec l lSet).
    - left; left; assumption.
  Admitted.

  Lemma sqsd l
    : constrained l -> VSet.In l (wGraph.V G).
  Proof.
    subst G. intros [Hl|Hl].
    - subst l. erewrite <- source_make_graph. apply invariants_make_graph.
    - destruct Hl as [e [gc [Hg [He1 He2]]]].
      destruct He2; subst l; apply invariants_make_graph;
      apply edges_make_graph'; eexists; split; eassumption.
  Qed.

  Definition update_valuation v l k :=
    match l with
    | mLevel s => {| valuation_mono := fun s' => if string_dec s s' then k else
                                                v.(valuation_mono) s';
                  valuation_poly := v.(valuation_poly)|}
    | mVar n => {| valuation_mono := v.(valuation_mono);
                  valuation_poly := fun n' => if n =? n' then Pos.to_nat k else
                                             v.(valuation_poly) n' |}
    end.

  Lemma Zpos_to_pos z : (z <= Z.pos (Z.to_pos z))%Z.
  Proof.
    destruct z; cbn; lia.
  Qed.


  Lemma qsf n (l l' : no_prop_level)
    : gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l')
                        -> (l = l' /\ n = 0) \/ (constrained l /\ constrained l').
  Proof.
    intro HH.
    assert (XX : {l = l' /\ n = 0} + {l <> l' \/ n <> 0}). admit.
    destruct XX as [XX|XX]; [now left|right]. split.
    - destruct l as [|l]; [now left|].
      destruct (constrained_dec l) as [|H]; [assumption|apply False_rect].
      destruct HG2 as [v Hv].
      destruct (No_Prop_LevelDec.eq_dec l l') as [YY|YY].
      + destruct XX as [XX|XX]; [contradiction|]. destruct YY.
        specialize (HH _ Hv); cbn in HH. lia.
      + pose (K := Z.to_pos (val0 v l' + 1)).
        assert (Hv' : gc_satisfies (update_valuation v l K) ctrs).
        admit.
        specialize (HH _ Hv'); cbn in HH.
        assert (eq : val0 (update_valuation v l K) l' = val0 v l') by admit.
        rewrite eq in HH; clear eq.
        assert (eq : val0 (update_valuation v l K) (level_of_variable l)
                     = Z.pos K) by admit.
        rewrite eq in HH; clear eq.
        subst K.
        pose proof (Zpos_to_pos (val0 v l' + 1)). lia.
    - destruct l' as [|l']; [now left|].
      destruct (constrained_dec l') as [|H]; [assumption|apply False_rect].
      destruct HG2 as [v Hv].
      destruct (No_Prop_LevelDec.eq_dec l l') as [YY|YY].
      + destruct XX as [XX|XX]; [contradiction|]. destruct YY.
        specialize (HH _ Hv); cbn in HH. lia.
      + pose (K := Z.to_pos (val0 v l' + 1)).
  Abort.


  (* Inductive constrain : no_prop_level -> good_constraint -> Prop := *)
  (* | constrain_le1 : forall (l l' : variable_level), constrain l (gc_le l l') *)
  (* | constrain_le2 : forall (l l' : variable_level), constrain l' (gc_le l l') *)
  (* | constrain_lt1 : forall (l l' : variable_level), constrain l (gc_lt l l') *)
  (* | constrain_lt2 : forall (l l' : variable_level), constrain l' (gc_lt l l') *)
  (* | constrain_lt_Set : forall n, constrain (mVar n) (gc_lt_set n) *)
  (* | constrain_eq_Set : forall n, constrain (mVar n) (gc_eq_set n). *)

  (* Definition constrained l ctrs *)
  (*   := l = lSet \/ GoodConstraintSet.Exists (constrain l) ctrs. *)

  (* Lemma qsf n (l l' : no_prop_level) *)
  (*   : gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l') *)
  (*                       -> constrained l ctrs /\ constrained l' ctrs. *)
  (* Proof. *)
    
  (* Admitted. *)

  (* Lemma constrain_iff l gc *)
  (*   : (l = lSet \/ constrain l gc) <-> exists e, In e (edges_of_constraint gc) *)
  (*                                        /\ (e..s = l \/ e..t = l). *)
  (* Proof. *)
  (*   split. *)
  (*   - intros [Hl|Hl]. *)
  (*     + subst l. destruct gc; cbn. *)
  (*       * exists (edge_of_level v). rewrite source_edge_of_level; intuition. *)
  (*       * exists (edge_of_level v). rewrite source_edge_of_level; intuition. *)
  (*       * exists (lSet, 1, vtn (mVar n)); cbn; intuition. *)
  (*       * exists (lSet, 0, vtn (mVar n)); cbn; intuition. *)
  (*     + destruct Hl; cbn. *)
  (*       * exists (edge_of_level l). rewrite target_edge_of_level; intuition. *)
  (*       * exists (edge_of_level l'). rewrite target_edge_of_level; intuition. *)
  (*       * exists (edge_of_level l). rewrite target_edge_of_level; intuition. *)
  (*       * exists (edge_of_level l'). rewrite target_edge_of_level; intuition. *)
  (*       * exists (lSet, 1, vtn (mVar n)); cbn; intuition. *)
  (*       * exists (lSet, 0, vtn (mVar n)); cbn; intuition. *)
  (*   - intros [e [He1 He2]]; destruct gc; cbn in *. *)
  (*     + rdestruct He1; try subst e; cbn in *; *)
  (*         rewrite ?source_edge_of_level, ?target_edge_of_level in *. *)
  (*       all: destruct He2; subst l; (intuition || right; constructor). *)
  (*     + rdestruct He1; try subst e; cbn in *; *)
  (*         rewrite ?source_edge_of_level, ?target_edge_of_level in *. *)
  (*       all: destruct He2; subst l; (intuition || right; constructor). *)
  (*     + rdestruct He1; try subst e; cbn in *; *)
  (*         rewrite ?source_edge_of_level, ?target_edge_of_level in *. *)
  (*       all: destruct He2; subst l; (intuition || right; constructor). *)
  (*     + rdestruct He1; try subst e; cbn in *; *)
  (*         rewrite ?source_edge_of_level, ?target_edge_of_level in *. *)
  (*       all: destruct He2; subst l; (intuition || right; constructor). *)
  (* Qed. *)

  (* Lemma sqsd l *)
  (*   : constrained l ctrs -> VSet.In l (wGraph.V G). *)
  (* Proof. *)
  (*   subst G. destruct (No_Prop_LevelDec.eq_dec l lSet). *)
  (*   - subst l. intros _. erewrite <- source_make_graph. apply invariants_make_graph. *)
  (*   - intros [Hl|Hl]; [intuition|]. *)
  (*     destruct Hl as [gc [Hgc H]]. *)
  (*     assert (H' : l = lSet \/ constrain l gc) by (right; assumption). *)
  (*     apply constrain_iff in H'; destruct H' as [e [He1 He2]]. *)
  (*     destruct He2; subst l; apply invariants_make_graph; *)
  (*     apply edges_make_graph'; eexists; split; eassumption. *)
  (* Qed. *)

  Lemma qsf n (l l' : no_prop_level)
    : gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l')
      -> (l = l' /\ n = 0) \/ (VSet.In l (wGraph.V G) /\ VSet.In l' (wGraph.V G)).
  Proof.
  Admitted.

  Lemma leq_universe_vertices n (l l' : no_prop_level)
    : gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l')
      <-> leq_vertices G n l l'.
  Proof.
    split.
    - intros H v Hv.
      destruct (qsf n l l' H) as [[H1 H2]|[H1 H2]].
      + subst; lia.
      + apply leq_universe_vertices0; assumption.
    - intros H v Hv. subst G.
      apply make_graph_spec in Hv.
      specialize (H _ Hv). cbn.
      rewrite <- !labelling_of_valuation_val0. lia.
  Qed.


  Definition is_leq_no_prop_n n (l l' : no_prop_level)
    := is_leq_vertices G n l l'.


  Lemma is_leq_no_prop_n_spec (HC : gc_consistent ctrs) n l l'
    : is_leq_no_prop_n n l l'
      <-> gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l').
  Proof with try exact _.
    symmetry. etransitivity. apply leq_universe_vertices; subst G; assumption.
    etransitivity. subst G; apply is_leq_vertices_correct...
    unfold is_leq_no_prop_n; now subst G.
  Qed.


  Definition no_prop_of_level l :=
    match l with
    | Level.lProp => None
    | Level.lSet => Some lSet
    | Level.Level s => Some (vtn (mLevel s))
    | Level.Var n => Some (vtn (mVar n))
    end.

  Definition is_leq_level_n n l l' :=
    match no_prop_of_level l, no_prop_of_level l' with
    | None, None => n =? 0
    | None, Some l' => match n with
                      | O => true
                      | S n => is_leq_no_prop_n n lSet l'
                      end
    | Some l, None => false
    | Some l, Some l' => is_leq_no_prop_n n l l'
    end.


  Lemma no_prop_of_level_inv {l l0}
    : no_prop_of_level l = Some l0 -> level_of_no_prop l0 = l.
  Proof.
    destruct l; inversion 1; reflexivity.
  Qed.


  Ltac toProp :=
    match goal with
    | |- is_true (_ <? _) => apply PeanoNat.Nat.ltb_lt
    | |- is_true (_ <=? _) => apply PeanoNat.Nat.leb_le
    | |- is_true (_ =? _) => apply PeanoNat.Nat.eqb_eq
    | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
    | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
    | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
    end.


  Lemma is_leq_level_n_spec n l l'
    : is_leq_level_n n l l'
      <-> gc_leq_universe_n n ctrs (Universe.make l) (Universe.make l').
  Proof.
    unfold is_leq_level_n.
    case_eq (no_prop_of_level l).
    - intros l0 Hl. case_eq (no_prop_of_level l').
      + intros l0' Hl'. etransitivity.
        eapply is_leq_no_prop_n_spec; try eassumption.
        now erewrite !no_prop_of_level_inv by eassumption.
      + destruct l'; inversion 1.
        split; [discriminate|].
        intros HH. destruct HG2 as [v Hv].
        specialize (HH v Hv); cbn in HH.
        destruct l; try (now inversion Hl); cbn in HH; lia.
    - destruct l; inversion 1. case_eq (no_prop_of_level l').
      + intros l0' Hl'. destruct n.
        * split; [intros _|reflexivity].
          intros v Hv; cbn.
          destruct l'; inversion Hl'; cbn; lia.
        * etransitivity. eapply is_leq_no_prop_n_spec; try eassumption.
          split; intros HH v Hv; specialize (HH v Hv); cbn - [Z.of_nat] in *.
          -- erewrite <- (no_prop_of_level_inv Hl'); lia.
          -- erewrite (no_prop_of_level_inv Hl'); lia.
      + destruct l'; inversion 1. split; intro HH; toProp.
        subst. intros v Hv; lia.
        destruct HG2 as [v Hv]. specialize (HH v Hv); cbn in HH; lia.
  Qed.

  Definition is_leq_level := is_leq_level_n 0.

  Definition is_eq_level l l' := is_leq_level l l' && is_leq_level l' l.


  Definition is_leq_expr_n n (e1 e2 : Universe.Expr.t) :=
    match e1.2 && negb (Level.is_prop e1.1), e2.2 && negb (Level.is_prop e2.1) with
    | false, false
    | true, true => is_leq_level_n n e1.1 e2.1
    | true, false => is_leq_level_n (S n) e1.1 e2.1
    | false, true => is_leq_level_n (Peano.pred n) e1.1 e2.1  (* surprising! *)
    end.

  Lemma no_prop_of_level_not_is_prop {l l0}
    : no_prop_of_level l = Some l0 -> Level.is_prop l = false.
  Proof.
    destruct l; inversion 1; reflexivity.
  Qed.

  Lemma no_prop_of_level_is_prop {l}
    : no_prop_of_level l = None -> Level.is_prop l = true.
  Proof.
    destruct l; inversion 1; reflexivity.
  Qed.

  Ltac rew_no_prop :=
    match goal with
    | H : no_prop_of_level _ = Some _ |- _
      => rewrite !(no_prop_of_level_not_is_prop H) in *
    | H : no_prop_of_level _ = None |- _
      => rewrite !(no_prop_of_level_is_prop H) in *
    end.

  Opaque Z.of_nat.

  Lemma bla l l'
    :  (forall v, gc_satisfies v ctrs -> (val0 v l <= val0 v l' + 1)%Z) ->
       forall v, gc_satisfies v ctrs -> (val0 v l <= val0 v l')%Z.
  Admitted.


  Lemma is_leq_expr_n_spec n e e'
    : is_leq_expr_n n e e'
      <-> gc_leq_universe_n n ctrs (Universe.make' e) (Universe.make' e').
  Proof.
    unfold is_leq_expr_n.
    destruct e as [l []], e' as [l' []]; cbn.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
        (case_eq (no_prop_of_level l'); [intros l0' Hl'|intros Hl']); rew_no_prop;
          cbn; (etransitivity; [eapply is_leq_level_n_spec|]).
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn. split.
          -- intros HH v Hv; specialize (HH v Hv); lia.
          -- apply bla.
        * split; intros HH v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
          cbn; (etransitivity; [eapply is_leq_level_n_spec|]).
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l'); [intros l0 Hl|intros Hl]; rew_no_prop;
          cbn; (etransitivity; [eapply is_leq_level_n_spec|]).
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn. split.
          -- intros HH v Hv; specialize (HH v Hv); lia.
          -- apply bla.
        * split; intros HH v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - etransitivity; [eapply is_leq_level_n_spec|].
      split; intros HH v Hv; specialize (HH v Hv); cbn in *; lia.
  Qed.


  Fixpoint is_leq_univ_expr_n n (u : universe) (e2 : Universe.Expr.t) :=
    match u with
    | NEL.sing e1 => is_leq_expr_n n e1 e2
    | NEL.cons e1 u => is_leq_expr_n n e1 e2 && is_leq_univ_expr_n n u e2
    end.

  Lemma is_leq_univ_expr_n_spec n u e2
    : is_leq_univ_expr_n n u e2
      <-> gc_leq_universe_n n ctrs u (Universe.make' e2).
  Proof.
    induction u; cbn.
    - apply is_leq_expr_n_spec.
    - etransitivity. apply andb_true_iff.
      etransitivity. eapply and_iff_compat_l. eassumption.
      etransitivity. eapply and_iff_compat_r. eapply is_leq_expr_n_spec.
      split.
      + intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
        rewrite val_cons; cbn in *; lia.
      + intro H; split; intros v Hv; specialize (H v Hv);
        rewrite val_cons in H; cbn in *; lia.
  Qed.

  Definition is_leq_univ_expr := is_leq_univ_expr_n 0.

  (* This function is correct but not complete! *)
  Fixpoint try_is_leq_universe_n n (u1 u2 : universe) :=
    match u2 with
    | NEL.sing e => is_leq_univ_expr_n n u1 e
    | NEL.cons e u2 => is_leq_univ_expr_n n u1 e || try_is_leq_universe_n n u1 u2
    end.

  Lemma try_is_leq_universe_n_spec n u1 u2
    : try_is_leq_universe_n n u1 u2 -> gc_leq_universe_n n ctrs u1 u2.
  Proof.
    induction u2; cbn.
    - apply is_leq_univ_expr_n_spec.
    - intro H; apply orb_true_iff in H; destruct H as [H|H];
        [apply is_leq_univ_expr_n_spec in H|apply IHu2 in H];
        intros v Hv; specialize (H v Hv); rewrite val_cons; cbn in *; lia.
  Qed.

  Context `{checker_flags}.

  Definition try_is_leq_universe u1 u2 :=
    negb check_univs || try_is_leq_universe_n 0 u1 u2.

  Definition try_is_eq_universe u1 u2
    := try_is_leq_universe u1 u2 && try_is_leq_universe u2 u1.

  Definition is_eq_univ_instance (u1 u2 : universe_instance)
    := forallb2 is_eq_level u1 u2.

  Definition check_gc_constraint (gc : good_constraint) :=
    match gc with
    | gc_le l l' => is_leq_no_prop_n 0 l l'
    | gc_lt l l' => is_leq_no_prop_n 1 l l'
    | gc_lt_set n => is_leq_no_prop_n 1 lSet (mVar n)
    | gc_eq_set n => is_leq_no_prop_n 0 (mVar n) lSet
    end.

  Definition check_gc_constraints
    := GoodConstraintSet.for_all check_gc_constraint.

  Definition check_constraints ctrs :=
    match gc_of_constraints ctrs with
    | Some ctrs => check_gc_constraints ctrs
    | None => false
    end.

End CheckLeq.

Extract Constant constrained_dec => "(fun g ctrs l -> assert false)".


(* Definition G := make_graph *)
(*   (GoodConstraintSet.add (gc_lt (mVar 0) (mVar 1)) *)
(*  (GoodConstraintSet_pair (gc_lt_set 0) (gc_eq_set 1))). *)

(* Compute (lsp G lSet (mVar 0)). *)
(* Compute (lsp G lSet (mVar 1)). *)
(* Compute (lsp G lSet lSet). *)

(* Section Test. *)

(*   Definition get_graph G0 := match G0 with *)
(*                              | Some φ => φ *)
(*                              | None => init_graph *)
(*                              end. *)

(*   Definition G0 := make_graph ConstraintSet.empty. *)
(*   Check (eq_refl : G0 = Some _). *)
(*   Definition G := get_graph G0. *)

(*   Local Existing Instance default_checker_flags. *)

(*   Check (eq_refl : check_leq G Universe.type0m Universe.type0 = true). *)
(*   Check (eq_refl : check_lt G Universe.type0m Universe.type0 = true). *)
(*   Check (eq_refl : check_lt G Universe.type0m Universe.type0m = false). *)
(*   Check (eq_refl : check_lt G Universe.type0 Universe.type0m = false). *)
(*   Check (eq_refl : check_lt G Universe.type0 Universe.type0 = false). *)
(*   Check (eq_refl : no_universe_inconsistency G = true). *)

(*   Definition ctrs0 := ConstraintSet.add (Level.Level "Top.0", Lt, Level.Level "Top.1") *)
(*                                         (ConstraintSet.singleton (Level.Var 0, Lt, Level.Var 1)). *)
(*   Definition G'0 := make_graph ctrs0. *)
(*   Check (eq_refl : G'0 = Some _). *)
(*   Definition G' := get_graph G'0. *)

(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.0")) (Universe.make (Level.Var 0)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.lProp)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.super (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.super (Level.Level "Top.1")) = true). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false). *)
(*   Check (eq_refl : check_eq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = true). *)
(*   Check (eq_refl : no_universe_inconsistency G = true). *)

(*   Check (eq_refl : check_lt G' (Universe.make (Level.Var 1)) (Universe.make (Level.Var 0)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true). *)
(*   Check (eq_refl : check_leq G' Universe.type1 Universe.type0 = false). *)
(*   Check (eq_refl : check_lt G' Universe.type1 Universe.type1 = false). *)


(*   Definition ctrs1 := ConstraintSet.add (Level.Var 1, Eq, Level.Var 2) *)
(*                                         (ConstraintSet.add (Level.Var 2, Le, Level.lSet) ctrs0). *)
(*   Definition G''0 := make_graph ctrs1. *)
(*   Check (eq_refl : G''0 = Some _). *)
(*   Definition G'' := get_graph G''0. *)

(*   Check (eq_refl : no_universe_inconsistency G'' = false). *)

(* End Test. *)
