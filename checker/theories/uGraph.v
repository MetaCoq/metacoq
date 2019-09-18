Require Import Nat Bool String BinInt List Relations Lia.
Require Import MSetFacts MSetProperties.
From MetaCoq.Template Require Import utils config Universes monad_utils.
From MetaCoq.Checker Require Import wGraph.

Import ListNotations.
Import ConstraintType MonadNotation.
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

Ltac toProp :=
  match goal with
  | |- is_true (_ <? _) => apply PeanoNat.Nat.ltb_lt
  | |- is_true (_ <=? _) => apply PeanoNat.Nat.leb_le
  | |- is_true (_ =? _) => apply PeanoNat.Nat.eqb_eq
  | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
  | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
  | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
  end.

Lemma InA_In_eq {A} x (l : list A) : InA eq x l <-> In x l.
Proof.
  etransitivity. eapply InA_alt.
  firstorder. now subst.
Qed.


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

Lemma GoodConstraintSet_pair_In x y z
  : GoodConstraintSet.In x (GoodConstraintSet_pair y z)
    -> x = y \/ x = z.
Proof.
  intro H. apply GoodConstraintSetFact.add_iff in H.
  destruct H; [intuition|].
  apply GoodConstraintSetFact.singleton_1 in H; intuition.
Qed.

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
Definition gc_of_constraint `{checker_flags} (uc : univ_constraint) : option GoodConstraintSet.t
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
  (* | H : is_true false |- _ => discriminate H *)
  | H : is_true (if _ then true else false) |- _ => rewrite if_true_false in H
  | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
  | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
  | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
  | H : is_true (gc_satisfies _ (GoodConstraintSet_pair _ _)) |- _
               => apply gc_satisfies_pair in H; cbn -[Nat.leb Nat.eqb] in H;
                 destruct H
  end.

Section GC.

Context `{cf : checker_flags}.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (gc_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1 ; destruct l, l' ; try constructor ; try reflexivity.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *.
    all: unfold lle, llt in *.
    (* all: unfold gc_of_constraint in *. *)
    all: destruct prop_sub_type.
    all: try solve [ repeat gc_of_constraint_tac ; lia ].
    all: try solve [ cbn ; easy ].
  - destruct uc as [[[] []] []].
    all: cbn - [Nat.leb Nat.eqb GoodConstraintSet_pair].
    all: try (now inversion 1).
    all: constructor.
    all: unfold lle, llt in *.
    all: destruct prop_sub_type.
    all: try solve [
               cbn - [Nat.leb Nat.eqb GoodConstraintSet_pair] in * ; lia
             ].
    all: try solve [
               cbn - [Nat.leb Nat.eqb GoodConstraintSet_pair] in * ;
               try lia ;
                repeat gc_of_constraint_tac ;
               lia
             ].
Qed.


Definition add_gc_of_constraint uc (S : option GoodConstraintSet.t)
  := S1 <- S ;;
     S2 <- gc_of_constraint uc ;;
     ret (GoodConstraintSet.union S1 S2).
  (* := match S with *)
  (*    | None => None *)
  (*    | Some S1 => match gc_of_constraint uc with *)
  (*                | None => None *)
  (*                | Some S2 => Some (GoodConstraintSet.union S1 S2) *)
  (*                end *)
  (*    end. *)

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

Definition gc_eq_universe0 φ u u' :=
  forall v, gc_satisfies v φ -> val v u = val v u'.

Definition gc_leq_universe φ u u'
  := if check_univs then gc_leq_universe_n 0 φ u u' else True.

Definition gc_eq_universe φ u u'
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


(* no_prop_levels of the graph are levels which are not Prop *)
(* vtn : "variable to no_prop" *)
Inductive no_prop_level := lSet | vtn (l : variable_level).

Coercion vtn : variable_level >-> no_prop_level.

Module VariableLevel.
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
End VariableLevel.

Module NoPropLevel.
  Definition t : Set := no_prop_level.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition lt : t -> t -> Prop :=
    fun x y => match x, y with
            | lSet, lSet => False
            | lSet, vtn _ => True
            | vtn v, vtn v' => VariableLevel.lt v v'
            | vtn _, lSet => False
            end.
  Definition lt_strorder : StrictOrder lt.
    split.
    - intros [|v] H; cbn in H; intuition.
      now apply VariableLevel.lt_strorder in H.
    - intros [|v1] [|v2] [|v3]; cbn; intuition.
      eapply VariableLevel.lt_strorder; eassumption.
  Qed.
  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1, H2.
  Qed.
  Definition compare : t -> t -> comparison :=
    fun x y => match x, y with
            | lSet, lSet => Datatypes.Eq
            | lSet, vtn _ => Datatypes.Lt
            | vtn v, vtn v' => VariableLevel.compare v v'
            | vtn _, lSet => Datatypes.Gt
            end.
  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
    intros [|v] [|v']; cbn; try now constructor.
    destruct (VariableLevel.compare_spec v v'); constructor; congruence.
  Qed.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality. apply VariableLevel.eq_dec.
  Defined.
End NoPropLevel.



Module Import wGraph := wGraph.WeightedGraph NoPropLevel.

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


Definition no_prop_of_level l :=
  match l with
  | Level.lProp => None
  | Level.lSet => Some lSet
  | Level.Level s => Some (vtn (mLevel s))
  | Level.Var n => Some (vtn (mVar n))
  end.

Definition no_prop_levels (X : LevelSet.t) : VSet.t
  := LevelSet.fold (fun l X => match no_prop_of_level l with
                            | Some l => VSet.add l X
                            | None => X
                            end)
                   X VSet.empty.

Definition declared := LevelSet.In.

Definition uctx_invariants (uctx : ContextSet.t)
  := ConstraintSet.For_all (fun '(l, _, l') => declared l uctx.1 /\ declared l' uctx.1)
                           uctx.2.

Definition global_uctx_invariants (uctx : ContextSet.t)
  := LevelSet.In Level.lSet uctx.1 /\ uctx_invariants uctx.

Definition global_gc_uctx_invariants (uctx : VSet.t * GoodConstraintSet.t)
  := VSet.In lSet uctx.1 /\ GoodConstraintSet.For_all (fun gc => match gc with
                 | gc_le l l'
                 | gc_lt l l'  => VSet.In l uctx.1 /\ VSet.In l' uctx.1
                 | gc_lt_set n
                 | gc_eq_set n => VSet.In (mVar n) uctx.1
                 end) uctx.2.

Definition gc_of_uctx `{checker_flags} (uctx : ContextSet.t)
  : option (VSet.t * GoodConstraintSet.t)
  := ctrs <- gc_of_constraints uctx.2 ;;
     ret (no_prop_levels uctx.1, ctrs).


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

Lemma no_prop_of_level_no_prop l
  : no_prop_of_level (level_of_no_prop l) = Some l.
Proof.
  destruct l; try reflexivity.
  destruct l; try reflexivity.
Qed.

Lemma no_prop_levels_no_prop_level (l : no_prop_level) levels
  : declared l levels ->  VSet.In l (no_prop_levels levels).
Proof.
  unfold no_prop_levels, declared. rewrite LevelSet.fold_spec.
  intro H. apply LevelSetFact.elements_1, InAeq_In in H.
  cut (In (l : Level.t) (LevelSet.elements levels) \/ VSet.In l VSet.empty);
    [|now left].
  clear H; generalize VSet.empty.
  induction (LevelSet.elements levels); simpl.
  - intuition.
  - intros X [[HH|HH]|HH].
    + subst a; cbn. apply IHl0.
      right. rewrite no_prop_of_level_no_prop.
      apply VSet.add_spec; intuition.
    + apply IHl0. now left.
    + apply IHl0. right.
      destruct (no_prop_of_level a); tas.
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


Definition edge_of_level (l : variable_level) : EdgeSet.elt :=
  match l with
  | mLevel l => (lSet, 1, vtn (mLevel l))
  | mVar n => (lSet, 0, vtn (mVar n))
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edge_of_constraint (gc : good_constraint) : EdgeSet.elt :=
  match gc with
  | gc_le l l' => (vtn l, 0, vtn l')
  | gc_lt l l' => (vtn l, 1, vtn l')
  | gc_lt_set n => (lSet, 1, vtn (mVar n))
  | gc_eq_set n => (vtn (mVar n), 0, lSet)
  end.


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


Definition make_graph (uctx : VSet.t * GoodConstraintSet.t) : wGraph.t :=
  let init_edges := VSet.fold (fun l E => match l with
                                       | vtn l => EdgeSet.add (edge_of_level l) E
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
        destruct a as [|l']. right; tas.
        apply EdgeSet.add_spec in HH. destruct HH.
        left. exists l'. intuition. right; tas.
      * intros [[l' [[H1|H1] H2]]|H].
        right. subst a. apply EdgeSet.add_spec. left; tas.
        left. exists l'; intuition.
        right. destruct a; tas. apply EdgeSet.add_spec. right; tas.
Qed.


Lemma make_graph_invariants uctx (Hi : global_gc_uctx_invariants uctx)
  : invariants (make_graph uctx).
Proof.
  split; [|split].
  - intros e He. apply make_graph_E in He.
    destruct He as [[l [Hl He]]|[gc [Hgc He]]].
    + subst e. split. rewrite source_edge_of_level. apply Hi.
      rewrite target_edge_of_level; tas.
    + subst e. split. destruct gc; try apply (Hi..2 _ Hgc). apply Hi.
      destruct gc; try apply (Hi..2 _ Hgc). apply Hi.
  - apply Hi.
  - cbn. intros l Hl. sq. destruct l. constructor.
    econstructor. 2: constructor.
    assert (He: EdgeSet.In (edge_of_level l) (wGraph.E (make_graph uctx))). {
      apply make_graph_E. left. exists l. intuition. }
    destruct l; eexists; exact He.
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

Ltac rdestruct H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [rdestruct H|rdestruct H]
  | _ /\ _ => let H' := fresh H in
            destruct H as [H|H']; [rdestruct H|rdestruct H']
  | _ => idtac
  end.

Definition labelling_of_valuation (v : valuation) : labelling
  := fun x => match x with
           | lSet => 0
           | vtn (mLevel l) => Pos.to_nat (v.(valuation_mono) l)
           | vtn (mVar n) => v.(valuation_poly) n
           end.

Definition valuation_of_labelling (l : labelling) : valuation
  := {| valuation_mono := fun s => Pos.of_nat (l (vtn (mLevel s)));
        valuation_poly := fun n => l (vtn (mVar n)) |}.


Section MakeGraph.
  Context uctx (Huctx : global_gc_uctx_invariants uctx).
  Let ctrs := uctx.2.
  Let G : universes_graph := make_graph uctx.

  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x uctx.1
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof.
    destruct x; cbn.
    - intros _. now apply proj1 in Hl; cbn in Hl.
    - destruct l0; cbn. 2: reflexivity.
      intro Hs. apply Nat2Pos.id.
      assert (HH: EdgeSet.In (lSet, 1, vtn (mLevel s)) (wGraph.E G)). {
        subst G. apply make_graph_E. left.
        exists (mLevel s). intuition. }
      apply (proj2 Hl) in HH; cbn in HH. lia.
  Qed.

  Lemma make_graph_spec v :
    gc_satisfies v ctrs <-> correct_labelling G (labelling_of_valuation v).
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
        destruct ctr as [g g0|g g0|n|n]; try apply PeanoNat.Nat.leb_le in H;
          unfold gc_val0 in *; cbn in *; try lia.
        destruct (valuation_poly v n); [reflexivity|discriminate].
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (proj2 (make_graph_E uctx (edge_of_constraint gc)) (or_intror (ex_intro _ gc (conj Hgc eq_refl)))) as XX.
      specialize (H..2 _ XX).
      destruct gc; intro HH; try apply PeanoNat.Nat.leb_le.
      4: apply PeanoNat.Nat.eqb_eq.
      cbn in *; unfold gc_val0; lia.
      cbn in *; unfold gc_val0; lia.
      assumption.
      cbn in HH. lia.
  Qed.

  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) ctrs <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) ctrs.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling. intuition.
    rewrite !valuation_labelling_eq; tas. now apply H.
    all: now apply make_graph_invariants.
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
    now apply make_graph_invariants. assumption.
  Defined.
End MakeGraph.

Existing Class invariants.
Existing Instance make_graph_invariants.
Existing Class acyclic_no_loop.
Existing Class gc_consistent.
Existing Class global_gc_uctx_invariants.
Existing Class global_uctx_invariants.
Existing Instance consistent_no_loop.
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

  (** ** Check of leq ** *)

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

  Lemma leq_universe_vertices0 n (l l' : no_prop_level)
    : leq_vertices G n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intros H v Hv. subst G.
    apply make_graph_spec in Hv; tas.
    specialize (H _ Hv). cbn.
    rewrite <- !labelling_of_valuation_val0. lia.
  Qed.

  Lemma leq_universe_vertices1 n l l'
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l')
      -> leq_vertices G n l l'.
  Proof.
    subst G. intros H v Hv.
    pose proof (H _ (make_graph_spec' _ Huctx _ Hv)) as HH.
    rewrite <- (valuation_labelling_eq _ _ Hv l Hl).
    rewrite <- (valuation_labelling_eq _ _ Hv l' Hl').
    pose proof (labelling_of_valuation_val0 (valuation_of_labelling v) l).
    pose proof (labelling_of_valuation_val0 (valuation_of_labelling v) l').
    cbn in *; lia.
  Qed.

  (* Definition update_valuation v l k := *)
  (*   match l with *)
  (*   | mLevel s => {| valuation_mono := fun s' => if string_dec s s' then k else *)
  (*                                               v.(valuation_mono) s'; *)
  (*                 valuation_poly := v.(valuation_poly)|} *)
  (*   | mVar n => {| valuation_mono := v.(valuation_mono); *)
  (*                 valuation_poly := fun n' => if n =? n' then Pos.to_nat k else *)
  (*                                            v.(valuation_poly) n' |} *)
  (*   end. *)

  (* Lemma Zpos_to_pos z : (z <= Z.pos (Z.to_pos z))%Z. *)
  (* Proof. *)
  (*   destruct z; cbn; lia. *)
  (* Qed. *)

  Lemma leq_universe_vertices n (l l' : no_prop_level)
        (Hl : VSet.In l (wGraph.V G)) (Hl' : VSet.In l' (wGraph.V G))
    : gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l')
      <-> leq_vertices G n l l'.
  Proof.
    split.
    - intros H v Hv. apply leq_universe_vertices1; tas.
    - apply leq_universe_vertices0.
  Qed.


  Definition leqb_no_prop_n n (l l' : no_prop_level)
    := leqb_vertices G n l l'.


  Lemma leqb_no_prop_n_spec0 n l l'
    : leqb_no_prop_n n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    intro HH. apply leq_universe_vertices0.
    apply leqb_vertices_correct; tas; subst G; exact _.
  Qed.

  Lemma leqb_no_prop_n_spec n l l'
        (Hl : VSet.In l uctx.1) (Hl' : VSet.In l' uctx.1)
    : leqb_no_prop_n n l l'
      <-> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof with try exact _.
    symmetry. etransitivity. apply leq_universe_vertices; subst G; assumption.
    etransitivity. subst G; apply leqb_vertices_correct...
    unfold leqb_no_prop_n; now subst G.
  Qed.


  Definition leqb_level_n n l l' :=
    match no_prop_of_level l, no_prop_of_level l' with
    | None, None => n =? 0
    | None, Some l' => match n with
                      | O => true
                      | S n => leqb_no_prop_n n lSet l'
                      end
    | Some l, None => false
    | Some l, Some l' => leqb_no_prop_n n l l'
    end.


  Lemma no_prop_of_level_inv {l l0}
    : no_prop_of_level l = Some l0 -> level_of_no_prop l0 = l.
  Proof.
    destruct l; inversion 1; reflexivity.
  Qed.

  Definition gc_level_declared l
    := on_Some_or_None (fun l => VSet.In l uctx.1) (no_prop_of_level l).

  Lemma leqb_level_n_spec0 n l l'
    : leqb_level_n n l l'
      -> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    unfold leqb_level_n.
    case_eq (no_prop_of_level l).
    - intros l0 Hl. case_eq (no_prop_of_level l').
      + intros l0' Hl'. intro HH. apply leqb_no_prop_n_spec0 in HH.
        now rewrite !no_prop_of_level_inv in HH by eassumption.
      + destruct l'; inversion 1. discriminate.
    - destruct l; inversion 1. case_eq (no_prop_of_level l').
      + intros l0' Hl'. destruct n.
        * intros _ v Hv; cbn.
          destruct l'; inversion Hl'; cbn; lia.
        * intro HH; apply leqb_no_prop_n_spec0 in HH.
          intros v Hv; specialize (HH v Hv); cbn - [Z.of_nat] in *.
          erewrite <- (no_prop_of_level_inv Hl'); lia.
      + destruct l'; inversion 1. intro HH; toProp.
        subst. intros v Hv; lia.
  Qed.

  Lemma leqb_level_n_spec n l l'
        (HHl  : gc_level_declared l)
        (HHl' : gc_level_declared l')
    : leqb_level_n n l l'
      <-> gc_leq_universe_n n uctx.2 (Universe.make l) (Universe.make l').
  Proof.
    unfold leqb_level_n. unfold gc_level_declared in *.
    case_eq (no_prop_of_level l).
    - intros l0 Hl. rewrite Hl in HHl; cbn in HHl.
      case_eq (no_prop_of_level l').
      + intros l0' Hl'. rewrite Hl' in HHl'; cbn in HHl'.
        etransitivity. eapply leqb_no_prop_n_spec; tea.
        now erewrite !no_prop_of_level_inv by eassumption.
      + destruct l'; inversion 1.
        split; [discriminate|].
        intros HH. destruct HC as [v Hv].
        specialize (HH v Hv); cbn in HH.
        destruct l; try (now inversion Hl); cbn in HH; lia.
    - destruct l; inversion 1. clear HHl. case_eq (no_prop_of_level l').
      + intros l0' Hl'. rewrite Hl' in HHl'; cbn in HHl'. destruct n.
        * split; [intros _|reflexivity].
          intros v Hv; cbn.
          destruct l'; inversion Hl'; cbn; lia.
        * etransitivity. eapply leqb_no_prop_n_spec; tas.
          apply Huctx.
          split; intros HH v Hv; specialize (HH v Hv); cbn - [Z.of_nat] in *.
          -- erewrite <- (no_prop_of_level_inv Hl'); lia.
          -- erewrite (no_prop_of_level_inv Hl'); lia.
      + destruct l'; inversion 1. split; intro HH; toProp.
        subst. intros v Hv; lia.
        destruct HC as [v Hv]. specialize (HH v Hv); cbn in HH; lia.
  Qed.

  Definition leqb_level l l' := negb check_univs || leqb_level_n 0 l l'.

  Definition eqb_level l l' := leqb_level l l' && leqb_level l' l.

  Definition eqb_univ_instance (u1 u2 : universe_instance)
    := forallb2 eqb_level u1 u2.

  Definition leqb_expr_n n (e1 e2 : Universe.Expr.t) :=
    match e1.2 && negb (Level.is_prop e1.1), e2.2 && negb (Level.is_prop e2.1) with
    | false, false
    | true, true => leqb_level_n n e1.1 e2.1
    | true, false => leqb_level_n (S n) e1.1 e2.1
    | false, true => leqb_level_n (Peano.pred n) e1.1 e2.1  (* surprising! *)
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

  Conjecture constraint_strengthening : forall l l',
      (forall v, gc_satisfies v uctx.2 -> (val0 v l <= val0 v l' + 1)%Z) ->
      forall v, gc_satisfies v uctx.2 -> (val0 v l <= val0 v l')%Z.

  Lemma leqb_expr_n_spec0 n e e'
    : leqb_expr_n n e e'
      -> gc_leq_universe_n n uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    unfold leqb_expr_n.
    destruct e as [l []], e' as [l' []]; cbn.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
        (case_eq (no_prop_of_level l'); [intros l0' Hl'|intros Hl']); rew_no_prop; cbn;
          intro HH; apply leqb_level_n_spec0 in HH; tas.
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn.
          intros v Hv; specialize (HH v Hv); cbn in *; lia.
        * intros v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
        cbn; (intro HH; eapply leqb_level_n_spec0 in HH; tas).
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l'); [intros l0 Hl|intros Hl]; rew_no_prop;
          cbn; (intro HH; eapply leqb_level_n_spec0 in HH; tas).
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn.
          intros v Hv; specialize (HH v Hv); cbn in *; lia.
        * intros v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + intros v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - intro HH; eapply leqb_level_n_spec0 in HH; tas.
  Qed.

  Lemma leqb_expr_n_spec n e e'
        (HHl  : gc_level_declared e.1)
        (HHl' : gc_level_declared e'.1)
    : leqb_expr_n n e e'
      <-> gc_leq_universe_n n uctx.2 (Universe.make' e) (Universe.make' e').
  Proof.
    unfold leqb_expr_n.
    destruct e as [l []], e' as [l' []]; cbn.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
        (case_eq (no_prop_of_level l'); [intros l0' Hl'|intros Hl']); rew_no_prop;
          cbn; (etransitivity; [eapply leqb_level_n_spec; tas|]).
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn. split.
          -- intros HH v Hv; specialize (HH v Hv); lia.
          -- apply constraint_strengthening.
        * split; intros HH v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l); [intros l0 Hl|intros Hl]; rew_no_prop;
          cbn; (etransitivity; [eapply leqb_level_n_spec; tas|]).
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - case_eq (no_prop_of_level l'); [intros l0 Hl|intros Hl]; rew_no_prop;
          cbn; (etransitivity; [eapply leqb_level_n_spec; tas|]).
      + destruct n.
        * unfold gc_leq_universe_n. cbn.
          unfold val1; cbn. repeat rew_no_prop; cbn. split.
          -- intros HH v Hv; specialize (HH v Hv); lia.
          -- apply constraint_strengthening.
        * split; intros HH v Hv; specialize (HH v Hv); cbn in *;
            unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
      + split; intros HH v Hv; specialize (HH v Hv); cbn in *;
          unfold val1 in *; cbn in *; repeat rew_no_prop; cbn in *; try lia.
    - etransitivity; [eapply leqb_level_n_spec; tas|].
      split; intros HH v Hv; specialize (HH v Hv); cbn in *; lia.
  Qed.


  Fixpoint leqb_univ_expr_n n (u : universe) (e2 : Universe.Expr.t) :=
    match u with
    | NEL.sing e1 => leqb_expr_n n e1 e2
    | NEL.cons e1 u => leqb_expr_n n e1 e2 && leqb_univ_expr_n n u e2
    end.

  Definition gc_levels_declared (u : universe)
    := List.Forall (fun e => gc_level_declared e.1) (NEL.to_list u).

  Lemma leqb_univ_expr_n_spec0 n u e2
    : leqb_univ_expr_n n u e2
      -> gc_leq_universe_n n uctx.2 u (Universe.make' e2).
  Proof.
    induction u; cbn.
    - apply leqb_expr_n_spec0; tas.
    - intro HH. apply andb_true_iff in HH.
      destruct HH as [H1 H2]. apply IHu in H2; tas.
      eapply leqb_expr_n_spec0 in H1; tas.
      intros v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
      rewrite val_cons; cbn in *; lia.
  Qed.

  Lemma leqb_univ_expr_n_spec n u e2
        (Hu  : gc_levels_declared u)
        (He2 : gc_level_declared e2.1)
    : leqb_univ_expr_n n u e2
      <-> gc_leq_universe_n n uctx.2 u (Universe.make' e2).
  Proof.
    induction u; cbn.
    - apply leqb_expr_n_spec; tas. now inversion Hu.
    - etransitivity. apply andb_true_iff.
      inversion_clear Hu.
      etransitivity. eapply and_iff_compat_l. apply IHu; tas.
      etransitivity. eapply and_iff_compat_r. eapply leqb_expr_n_spec; tas.
      split.
      + intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
        rewrite val_cons; cbn in *; lia.
      + intro HH; split; intros v Hv; specialize (HH v Hv);
        rewrite val_cons in HH; cbn in *; lia.
  Qed.

  Definition leqb_univ_expr u e2 :=
    negb check_univs || leqb_univ_expr_n 0 u e2.


  (* This function is correct but not complete! *)
  Fixpoint try_leqb_universe_n n (u1 u2 : universe) :=
    match u2 with
    | NEL.sing e => leqb_univ_expr_n n u1 e
    | NEL.cons e u2 => leqb_univ_expr_n n u1 e || try_leqb_universe_n n u1 u2
    end.

  Lemma try_leqb_universe_n_spec n u1 u2
    : try_leqb_universe_n n u1 u2 -> gc_leq_universe_n n uctx.2 u1 u2.
  Proof.
    induction u2; cbn.
    - apply leqb_univ_expr_n_spec0; tas.
    - intro HH; apply orb_true_iff in HH; destruct HH as [HH|HH];
        [apply leqb_univ_expr_n_spec0 in HH; tas|apply IHu2 in HH; tas];
        intros v Hv; specialize (HH v Hv); rewrite val_cons; cbn in *; lia.
  Qed.

  Definition try_leqb_universe (u1 u2 : universe) :=
    negb check_univs || try_leqb_universe_n 0 u1 u2.

  Definition try_eqb_universe (u1 u2 : universe) :=
    negb check_univs || (try_leqb_universe_n 0 u1 u2 && try_leqb_universe_n 0 u2 u1).

  Definition check_gc_constraint (gc : good_constraint) :=
    negb check_univs || match gc with
                       | gc_le l l' => leqb_no_prop_n 0 l l'
                       | gc_lt l l' => leqb_no_prop_n 1 l l'
                       | gc_lt_set n => leqb_no_prop_n 1 lSet (mVar n)
                       | gc_eq_set n => leqb_no_prop_n 0 (mVar n) lSet
                       end.

  Definition check_gc_constraints
    := GoodConstraintSet.for_all check_gc_constraint.

  Definition check_constraints ctrs :=
    match gc_of_constraints ctrs with
    | Some ctrs => check_gc_constraints ctrs
    | None => false
    end.

  Lemma toto l : level_of_no_prop (vtn l) = level_of_variable l.
    destruct l; reflexivity.
  Qed.

  Transparent Z.of_nat.

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
      destruct l, l'; cbn in *; lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn -[Z.of_nat] in HH. unfold gc_satisfies0. toProp.
      pose proof (val_level_of_variable_level v l) as H1.
      pose proof (val_level_of_variable_level v l') as H2.
      rewrite !toto in *.
      rewrite H1, H2 in HH. clear -HH. lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lia.
    - intros HH v Hv; apply leqb_no_prop_n_spec0 in HH.
      specialize (HH v Hv). cbn in HH. unfold gc_satisfies0. toProp.
      lia.
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
  

  Definition level_declared l := LevelSet.In l uctx.1.

  Definition levels_declared (u : universe)
    := List.Forall (fun e => level_declared e.1) (NEL.to_list u).

  Lemma level_gc_declared_declared l
    : level_declared l -> gc_level_declared uctx' l.
  Proof.
    clear. subst uctx'.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2); [|contradiction HG].
    cbn; clear HG. unfold level_declared, gc_level_declared; cbn.
    case_eq (no_prop_of_level l); cbn; [|intuition].
    intros l' HH Hl. apply no_prop_levels_no_prop_level.
    now rewrite (no_prop_of_level_inv HH).
  Qed.

  Lemma levels_gc_declared_declared u
    : levels_declared u -> gc_levels_declared uctx' u.
  Proof.
    unfold levels_declared, gc_levels_declared.
    intro HH. eapply Forall_impl. eassumption.
    intro. apply level_gc_declared_declared.
  Qed.


  Lemma leqb_univ_expr_n_spec' n u e2
        (Hu : levels_declared u)
        (He2 : level_declared e2.1)
    : leqb_univ_expr_n G n u e2
      <-> leq_universe_n n uctx.2 u (Universe.make' e2).
  Proof.
    etransitivity.
    apply (leqb_univ_expr_n_spec G uctx' Huctx' HC' HG'); tas.
    - apply levels_gc_declared_declared; tas.
    - apply level_gc_declared_declared; tas.
    - symmetry. etransitivity. apply gc_leq_universe_n_iff.
      subst uctx'; cbn; clear -HG.
      unfold is_graph_of_uctx, gc_of_uctx in *.
      destruct (gc_of_constraints uctx.2) as [ctrs|].
      reflexivity. contradiction HG.
  Qed.


  Lemma try_leqb_universe_spec u1 u2
    : try_leqb_universe G u1 u2 -> leq_universe uctx.2 u1 u2.
  Proof.
    unfold try_leqb_universe, leq_universe.
    destruct check_univs; cbn; [|trivial].
    intro H; unshelve eapply (try_leqb_universe_n_spec G uctx' Huctx' HC' HG'
                                                       _ _ _) in H.
    eapply gc_leq_universe_n_iff.
    unfold uctx' in H.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2). cbn in *. exact H.
    exact I.
  Qed.

  Lemma eq_leq_universe φ u u' :
    eq_universe0 φ u u' <-> leq_universe0 φ u u' /\ leq_universe0 φ u' u.
  Proof.
    split.
    intro H; split; intros v Hv; specialize (H v Hv); lia.
    intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv); lia.
  Qed.


  Lemma try_eqb_universe_spec u1 u2
    : try_eqb_universe G u1 u2 -> eq_universe uctx.2 u1 u2.
  Proof.
    unfold try_eqb_universe, eq_universe.
    destruct check_univs; cbn; [|trivial].
    intro H. apply andb_prop in H. destruct H as [H1 H2].
    unshelve eapply (try_leqb_universe_n_spec G uctx' Huctx' HC' HG'
                                              _ _ _) in H1.
    unshelve eapply (try_leqb_universe_n_spec G uctx' Huctx' HC' HG'
                                              _ _ _) in H2.
    unfold uctx' in H1, H2.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    apply eq_leq_universe.
    split; eapply gc_leq_universe_n_iff;
      (destruct (gc_of_constraints uctx.2); [cbn in *|contradiction HG]); tas.
  Qed.


  (* Lemma check_gc_constraints_spec ctrs *)
  (*   : check_gc_constraints ctrs *)
  (*     -> if check_univs then forall v, gc_satisfies v uctx.2 -> gc_satisfies v ctrs else True. *)
  (* Proof. *)
  (*   pose proof check_gc_constraint_spec as XX. *)
  (*   unfold check_gc_constraint. destruct check_univs; [cbn|trivial]. *)
  (*   intros HH v Hv. *)
  (*   apply GoodConstraintSet.for_all_spec. now intros x y []. *)
  (*   apply GoodConstraintSet.for_all_spec in HH. 2: now intros x y []. *)
  (*   intros gc Hgc. specialize (HH gc Hgc). *)
  (*   apply XX; assumption. *)
  (* Qed. *)

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


(* Extract Constant constrained_dec => "(fun g ctrs l -> assert false)". *)


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
