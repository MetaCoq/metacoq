From Coq Require Import ssreflect MSetList MSetFacts MSetProperties MSetDecide.
From Coq Require Import Structures.OrdersEx.
From MetaCoq.Template Require Import utils BasicAst config Levels.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

(** TODO: Use Sort families when applicable ? *)

Record sort_valuation :=
  { valuation_global : ident -> nat ;
    valuation_var : nat -> nat }.

Class EvaluableSort (A : Type) :=
  sort_val : sort_valuation -> A -> nat.

(** ** Families of sorts *)
(* defined either globally or in the local sort context *)
Module SortFamily.

  Inductive t_ :=
  | sfType (* harcoded because it has a special status *)
  | sfGlobal (_ : ident) (* name of a globally defined sort *)
  | sfVar (_ : nat) (* deBruijin index in the local sort context *)
  .

  Definition t := t_.

  Instance: EvaluableSort t :=
    fun (sval : sort_valuation) (sr : t) =>
      match sr with
      | sfType => 0
      | sfGlobal s => valuation_global sval s
      | sfVar i => valuation_var sval i
      end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltTypeGlobal i : lt_ sfType (sfGlobal i)
  | ltTypeVar i : lt_ sfType (sfVar i)
  | ltGlobalGlobal i j : string_lt i j -> lt_ (sfGlobal i) (sfGlobal j)
  | ltGlobalVar i j : lt_ (sfGlobal i) (sfVar j)
  | ltVarVar i j : Nat.lt i j -> lt_ (sfVar i) (sfVar j).

  Definition lt := lt_.

  Local Existing Instance transitive_string_lt.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [| |] X; inversion X; [eapply string_lt_irreflexive|eapply Nat.lt_irrefl]; tea.
    - intros [| |] [| |] [| |] X1 X2; inversion X1; inversion X2;  constructor.
      all: etransitivity; tea.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; subst; reflexivity. Qed.

  Definition compare (sd1 sd2 : t) : comparison :=
    match sd1, sd2 with
    | sfType, sfType => Eq
    | sfType, _ => Lt
    | _, sfType => Gt
    | sfGlobal i, sfGlobal j => string_compare i j
    | sfGlobal _, _ => Lt
    | _, sfGlobal _ => Gt
    | sfVar i, sfVar j => Nat.compare i j
    end.

  Definition eq_dec (sd1 sd2 : t) : {sd1 = sd2} + {sd1 <> sd2}.
  Proof.
    decide equality; [apply string_dec | apply Peano_dec.eq_nat_dec].
  Defined.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply CompareSpec_string. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
  Qed.

  Definition eqb (x y : t) := match compare x y with Eq => true | _ => false end.

End SortFamily.


(** ** Sorts / Universe *)

Module Sort.

  Inductive t_ :=
  | PredicativeSort (_ : SortFamily.t) (_ : UniverseLevel.t)
  | ImpredicativeSort (_ : SortFamily.t).

  Definition t := t_.

  Instance: EvaluableSort t :=
    fun (sval : sort_valuation) (s : t) =>
      match s with
      | PredicativeSort sr _ => sort_val sval sr
      | ImpredicativeSort sr => sort_val sval sr
      end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.


  Module SortFamilyLevel := PairOrderedType SortFamily UniverseLevel.

  Inductive lt_ : t -> t -> Prop :=
  | ltImpredImpred sd1 sd2 : SortFamily.lt sd1 sd2 -> lt_ (ImpredicativeSort sd1) (ImpredicativeSort sd2)
  | ltImpredPred sd1 sd2 l2 : lt_ (ImpredicativeSort sd1) (PredicativeSort sd2 l2)
  | ltPredPred sd1 l1 sd2 l2 : SortFamilyLevel.lt (sd1, l1) (sd2, l2) ->lt_ (PredicativeSort sd1 l1) (PredicativeSort sd2 l2)
  .

  Definition lt := lt_.


  Local Existing Instance SortFamily.lt_strorder.
  Local Existing Instance UniverseLevel.lt_strorder.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] X; inversion X.
      + eapply SortFamilyLevel.lt_strorder; tea.
      + eapply SortFamily.lt_strorder; tea.
    - intros [] [] [] X1 X2; inversion X1; inversion X2.
      all: constructor; subst=> // ; etransitivity; tea.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; unfold eq in *; subst; reflexivity. Qed.


  Definition compare (s1 s2 : t) : comparison :=
    match s1, s2 with
    | ImpredicativeSort sd1, ImpredicativeSort sd2 => SortFamily.compare sd1 sd2
    | ImpredicativeSort _, _ => Lt
    | _, ImpredicativeSort _ => Gt
    | PredicativeSort sd1 l1, PredicativeSort sd2 l2 =>
      SortFamilyLevel.compare (sd1, l1) (sd2, l2)
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply SortFamilyLevel.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1: by cbv=> -[-> ->].
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply SortFamily.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1:now intros ->.
      all: intro; now constructor.
  Qed.

  Definition eq_dec (s1 s2 : t) : {s1 = s2} + {s1 <> s2}.
  Proof.
    decide equality; first [apply UniverseLevel.eq_dec|apply SortFamily.eq_dec].
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition family (x : t) : SortFamily.t :=
    match x with
    | ImpredicativeSort sf => sf
    | PredicativeSort sf _ => sf
    end.

  Definition level (x : t) : UniverseLevel.t :=
    match x with
    | ImpredicativeSort _ => UniverseLevel.type0 (* should never be used in a meaningful way *)
    | PredicativeSort _ l => l
    end.
End Sort.

Module SortSet := MSetList.MakeWithLeibniz Sort.
Module SortSetFact := WFactsOn Sort SortSet.
Module SortSetProp := WPropertiesOn Sort SortSet.

(** ** Constraints on sorts *)

Module SortConstraint.

  (* An atomic constraint on sorts (litteral) *)
  Inductive t_ :=
  | Eliminable (_ _ : SortFamily.t)
  .

  Definition t := t_.

  Definition satisfiable (sval : sort_valuation) (sc : t) : bool :=
    match sc with
    | Eliminable s1 s2 => sort_val sval s1 <=? sort_val sval s2
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Module SortPair := PairOrderedType SortFamily SortFamily.

  Inductive lt_ : t -> t -> Prop :=
  | ltElimElim s1 s'1 s2 s'2 : SortPair.lt (s1, s'1) (s2, s'2) -> lt_ (Eliminable s1 s'1) (Eliminable s2 s'2).

  Definition lt := lt_.


  Local Existing Instance SortPair.lt_strorder.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] X; inversion X; eapply SortPair.lt_strorder; tea.
    - intros [] [] [] X1 X2; inversion X1; inversion X2.
      all: by (constructor; subst=> // ; etransitivity; tea).
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; unfold eq in *; subst; reflexivity. Qed.


  Definition compare (sc1 sc2 : t) : comparison :=
    match sc1, sc2 with
    | Eliminable s1 s'1, Eliminable s2 s'2 =>
      SortPair.compare (s1,s'1) (s2,s'2)
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply SortPair.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1: by cbv=> -[-> ->].
      all: intro; now constructor.
  Qed.

  Definition eq_dec (s1 s2 : t) : {s1 = s2} + {s1 <> s2}.
  Proof.
    decide equality; apply SortFamily.eq_dec.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End SortConstraint.


(* A set of constraints on sorts
   When it represents a disjunction of atomic constraints
   it is called a clause *)
Module SortConstraintSet := MSetList.MakeWithLeibniz SortConstraint.
Module SortConstraintSetFact := WFactsOn SortConstraint SortConstraintSet.
Module SortConstraintSetProp := WPropertiesOn SortConstraint SortConstraintSet.


(* A set of clause representing the conjunction of the disjunctions of literals *)
Module SortConstraintFormula.
  Include MSetList.MakeWithLeibniz SortConstraintSet.

  Definition True : t := empty.
  Definition is_True (x : t) := is_empty x.
  Definition False : t := singleton SortConstraintSet.empty.
  Definition literal (sc : SortConstraint.t) : t :=
    singleton (SortConstraintSet.singleton sc).
  Definition conjunction (sf1 sf2: t) : t := union sf1 sf2.
  Definition from_cnf (llsc : list (list SortConstraint.t)) : t :=
    let add_clause sf lsc := add (SortConstraintSetProp.of_list lsc) sf in
    fold_left add_clause llsc empty.

  (* Consider adding from_dnf *)

End SortConstraintFormula.

Module SortConstraintFormulaFact := WFactsOn SortConstraintSet SortConstraintFormula.
Module SortConstraintFormulaProp := WPropertiesOn SortConstraintSet SortConstraintFormula.
Module SortConstraintFormulaDecide := WDecide SortConstraintFormula.
Ltac sort_constraint_sets := SortConstraintFormulaDecide.fsetdec.

(** ** Sort constraints satisfiability *)

Definition clause_satisfiesb (sval : sort_valuation) : SortConstraintSet.t -> bool :=
  SortConstraintSet.exists_ (SortConstraint.satisfiable sval).

Definition formula_satisfiesb (sval : sort_valuation) :
  SortConstraintFormula.t -> bool :=
  SortConstraintFormula.for_all (clause_satisfiesb sval).


Inductive sort_satisfies_constraint (sv : sort_valuation) : SortConstraint.t -> Prop :=
| sort_satisfies_constraint_eliminable s1 s2 :
    sort_val sv s1 <= sort_val sv s2 ->
    sort_satisfies_constraint sv (SortConstraint.Eliminable s1 s2).

Definition sort_satisfies_clause sv : SortConstraintSet.t -> Prop :=
  SortConstraintSet.Exists (sort_satisfies_constraint sv).

Definition sort_satisfies sv : SortConstraintFormula.t -> Prop :=
  SortConstraintFormula.For_all (sort_satisfies_clause sv).

Definition valid_sort_constraints (ϕ sctrs : SortConstraintFormula.t) :=
  forall sval, sort_satisfies sval ϕ -> sort_satisfies sval sctrs.


(* Module SortArg. *)

(*   Inductive t_ := *)
(*   | TypeArg (_ : Level.t) *)
(*   | ImpredSortArg (_ : SortFamily.t) *)
(*   | PredSortArg ( _ : SortFamily.t) (_ : Level.t). *)

(*   Definition t := t_. *)

(*   Definition level (s : t) := *)
(*     match s with *)
(*     | TypeArg l => l *)
(*     | ImpredSortArg _ => Level.lSet *)
(*     | PredSortArg _ l => l *)
(*     end. *)

(*   Module SortFamilyLevel := PairOrderedType SortFamily Level. *)

(*   Definition compare (s1 s2 : t) : comparison := *)
(*     match s1, s2 with *)
(*     | TypeArg l1, TypeArg l2 => Level.compare l1 l2 *)
(*     | TypeArg _, _ => Lt *)
(*     | _, TypeArg _ => Gt *)
(*     | ImpredSortArg sr1, ImpredSortArg sr2 => SortFamily.compare sr1 sr2 *)
(*     | ImpredSortArg _, _ => Lt *)
(*     | _, ImpredSortArg _ => Gt *)
(*     | PredSortArg sr1 l1, PredSortArg sr2 l2 => *)
(*       SortFamilyLevel.compare (sr1, l1) (sr2, l2) *)
(*     end. *)

(*   Definition eqb (s1 s2 : t) : bool := *)
(*     match compare s1 s2 with Eq => true | _ => false end. *)

(*   Definition equal_upto (f : Level.t -> Level.t -> bool) (s1 s2 : t) := *)
(*     match s1, s2 with *)
(*     | TypeArg l1, TypeArg l2 => f l1 l2 *)
(*     | TypeArg _, _ | _, TypeArg _ => false *)
(*     | ImpredSortArg sr1, ImpredSortArg sr2 => *)
(*       match SortFamily.compare sr1 sr2 with Eq => true | _ => false end *)
(*     | ImpredSortArg _, _ | _, ImpredSortArg _ => false *)
(*     | PredSortArg sr1 l1, PredSortArg sr2 l2 => *)
(*       match SortFamily.compare sr1 sr2 with *)
(*         | Eq => f l1 l2 *)
(*         | _ => false *)
(*       end *)
(*     end. *)

(*   Definition type0 := SortArg.TypeArg Level.lSet. *)
(* End SortArg. *)
