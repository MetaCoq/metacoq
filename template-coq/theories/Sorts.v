(* TODO: Revise the preamble to see what's needed *)
From Coq Require Import ssreflect MSetList MSetFacts MSetProperties MSetDecide.
From Coq Require Import Structures.OrdersEx.
From MetaCoq.Template Require Import utils BasicAst config Universes.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Record sort_valuation :=
  { valuation_global : nat -> nat ;
    valuation_var : nat -> nat }.

Class EvaluableSort (A : Type) :=
  sort_val : sort_valuation -> A -> nat.

Module SortRef.

  Inductive t_ :=
  | GlobalSortRef (_ : kername) (* name of a globally defined sort *)
  | VarSortRef (_ : nat) (* deBruijin index in the local sort context *)
  .

  Definition t := t_.

  Instance: EvaluableSort t :=
    fun (sval : sort_valuation) (sr : t) =>
      match sr with
      | GlobalSortRef i => valuation_global sval i
      | VarSortRef i => valuation_var sval i
      end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltGlobalGlobal i j : Nat.lt i j -> lt_ (GlobalSortRef i) (GlobalSortRef j)
  | ltGlobalVar i j : lt_ (GlobalSortRef i) (VarSortRef j)
  | ltVarVar i j : Nat.lt i j -> lt_ (VarSortRef i) (VarSortRef j).

  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [|] X; inversion X; eapply Nat.lt_irrefl; tea.
    - intros [|] [|] [|] X1 X2; inversion X1; inversion X2; constructor.
      all: etransitivity; tea.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; subst; reflexivity. Qed.

  Definition compare (sd1 sd2 : t) : comparison :=
    match sd1, sd2 with
    | GlobalSortRef i, GlobalSortRef j => Nat.compare i j
    | GlobalSortRef _, _ => Lt
    | _, GlobalSortRef _ => Gt
    | VarSortRef i, VarSortRef j => Nat.compare i j
    end.

  Definition eq_dec (sd1 sd2 : t) : {sd1 = sd2} + {sd1 <> sd2}.
  Proof.
    decide equality; apply Peano_dec.eq_nat_dec.
  Defined.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
  Qed.

End SortRef.

Module Sort.

  Inductive t_ :=
  | TypeSort (_ : Level.t) (* harcoded because it has a special status *)
  | PredicativeSort (_ : SortRef.t) (_ : Level.t)
  | ImpredicativeSort (_ : SortRef.t).

  Definition t := t_.

  Instance: EvaluableSort t :=
    fun (sval : sort_valuation) (s : t) =>
      match s with
      | TypeSort _ => 0
      | PredicativeSort sr _ => sort_val sval sr
      | ImpredicativeSort sr => sort_val sval sr
      end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.


  Module SortRefLevel := PairOrderedType SortRef Level.

  Inductive lt_ : t -> t -> Prop :=
  | ltTypeType l1 l2 : Level.lt l1 l2 -> lt_ (TypeSort l1) (TypeSort l2)
  | ltTypeImpred l1 sd2 : lt_ (TypeSort l1) (ImpredicativeSort sd2)
  | ltTypePred l1 sd2 l2 : lt_ (TypeSort l1) (PredicativeSort sd2 l2)
  | ltImpredImpred sd1 sd2 : SortRef.lt sd1 sd2 -> lt_ (ImpredicativeSort sd1) (ImpredicativeSort sd2)
  | ltImpredPred sd1 sd2 l2 : lt_ (ImpredicativeSort sd1) (PredicativeSort sd2 l2)
  | ltPredPred sd1 l1 sd2 l2 : SortRefLevel.lt (sd1, l1) (sd2, l2) ->lt_ (PredicativeSort sd1 l1) (PredicativeSort sd2 l2)
  .

  Definition lt := lt_.


  Local Existing Instance SortRef.lt_strorder.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] X; inversion X.
      + eapply Level.lt_strorder; tea.
      + eapply SortRefLevel.lt_strorder; tea.
      + eapply SortRef.lt_strorder; tea.
    - intros [] [] [] X1 X2; inversion X1; inversion X2.
      all: constructor; subst=> // ; etransitivity; tea.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; unfold eq in *; subst; reflexivity. Qed.


  Definition compare (s1 s2 : t) : comparison :=
    match s1, s2 with
    | TypeSort l1, TypeSort l2 => Level.compare l1 l2
    | TypeSort _, _ => Lt
    | _, TypeSort _ => Gt
    | ImpredicativeSort sd1, ImpredicativeSort sd2 => SortRef.compare sd1 sd2
    | ImpredicativeSort _, _ => Lt
    | _, ImpredicativeSort _ => Gt
    | PredicativeSort sd1 l1, PredicativeSort sd2 l2 =>
      SortRefLevel.compare (sd1, l1) (sd2, l2)
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply Level.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1:now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply SortRefLevel.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1: by cbv=> -[-> ->].
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply SortRef.compare_spec.
      4: reflexivity.
      all: split; [now inversion 1|].
      1:now intros ->.
      all: intro; now constructor.
  Qed.

  Definition eq_dec (s1 s2 : t) : {s1 = s2} + {s1 <> s2}.
  Proof.
    decide equality; first [apply Level.eq_dec|apply SortRef.eq_dec].
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End Sort.

Module SortSet := MSetList.MakeWithLeibniz Sort.
Module SortSetFact := WFactsOn Sort SortSet.
Module SortSetProp := WPropertiesOn Sort SortSet.


Module SortConstraint.

  (* An atomic constraint on sorts (literal) *)
  Inductive t_ :=
  | Eliminable (_ _ : Sort.t)
  .

  Definition t := t_.

  Definition satisfiable (sval : sort_valuation) (sc : t) : bool :=
    match sc with
    | Eliminable s1 s2 => sort_val sval s1 <=? sort_val sval s2
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Module SortPair := PairOrderedType Sort Sort.

  Inductive lt_ : t -> t -> Prop :=
  | ltElimElim s1 s'1 s2 s'2 : SortPair.lt (s1, s'1) (s2, s'2) -> lt_ (Eliminable s1 s'1) (Eliminable s2 s'2).

  Definition lt := lt_.


  Local Existing Instance SortPair.lt_strorder.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] X; inversion X; eapply SortPair.lt_strorder; tea.
    - intros [] [] [] X1 X2; inversion X1; inversion X2.
      all: try by (constructor; subst=> // ; etransitivity; tea).
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
    decide equality; apply Sort.eq_dec.
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
    let add_clause sf lsc :=
      let clause :=
        fold_left (fun clause sc => SortConstraintSet.add sc clause) lsc SortConstraintSet.empty
      in
      add clause sf
    in
    fold_left add_clause llsc empty.

  (* Consider adding from_dnf *)

End SortConstraintFormula.

Module SortConstraintFormulaFact := WFactsOn SortConstraintSet SortConstraintFormula.
Module SortConstraintFormulaProp := WPropertiesOn SortConstraintSet SortConstraintFormula.
Module SortConstraintFormulaDecide := WDecide SortConstraintFormula.
Ltac sort_constraint_sets := SortConstraintFormulaDecide.fsetdec.


Definition clause_satisfiable (sval : sort_valuation) : SortConstraintSet.t -> bool :=
  SortConstraintSet.exists_ (SortConstraint.satisfiable sval).

Definition formula_satisfiable (sval : sort_valuation) :
  SortConstraintFormula.t -> bool :=
  SortConstraintFormula.for_all (clause_satisfiable sval).



Module SortContext.
  Definition t := SortSet.t × SortConstraintFormula.t.

  Definition empty : t := (SortSet.empty, SortConstraintFormula.True).

  Definition is_empty (sctx : t) :=
    SortSet.is_empty sctx.1 && SortConstraintFormula.is_True sctx.2.
End SortContext.

Definition sorts_decl := SortContext.t.

