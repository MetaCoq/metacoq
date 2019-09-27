From Coq Require Import Ascii String ZArith List Bool.
From Coq Require Import MSetWeakList MSetFacts MSetProperties RelationClasses.
From MetaCoq.Template Require Import utils BasicAst config.
Import ListNotations.

Module Level.
  Inductive t : Set :=
  | lProp
  | lSet
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices *).

  Definition set : t := lSet.
  Definition prop : t := lProp.

  Definition is_small (x : t) :=
    match x with
    | lProp | lSet => true
    | _ => false
    end.

  Definition is_prop (x : t) :=
    match x with
    | lProp => true
    | _ => false
    end.

  Definition is_set (x : t) :=
    match x with
    | lSet => true
    | _ => false
    end.

  Definition is_var (l : t) :=
    match l with
    | Var _ => true
    | _ => false
    end.

  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lProp, lProp => Eq
    | lProp, _ => Lt
    | _, lProp => Gt
    | lSet, lSet => Eq
    | lSet, _ => Lt
    | _, lSet => Gt
    | Level s1, Level s2 => string_compare s1 s2
    | Level _, _ => Lt
    | _, Level _ => Gt
    | Var n, Var m => Nat.compare n m
    end.
  (** Comparison function *)

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.

  Definition equal (l1 l2 : Level.t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.
End Level.

Module LevelDecidableType.
   Definition t : Type := Level.t.
   Definition eq : t -> t -> Prop := eq.
   Definition eq_refl : forall x : t, eq x x := @eq_refl _.
   Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
   Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
   Definition eq_equiv : RelationClasses.Equivalence eq := _.
   Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := Level.eq_dec.
End LevelDecidableType.
Module LevelSet <: (MSetInterface.WSetsOn LevelDecidableType) := MSets.MSetWeakList.Make LevelDecidableType.
Module LevelSetFact := WFactsOn LevelDecidableType LevelSet.
Module LevelSetProp := WPropertiesOn LevelDecidableType LevelSet.

Definition LevelSet_pair x y
  := LevelSet.add y (LevelSet.singleton x).

Lemma LevelSet_pair_In x y z :
  LevelSet.In x (LevelSet_pair y z) -> x = y \/ x = z.
Proof.
  intro H. apply LevelSetFact.add_iff in H.
  destruct H; [intuition|].
  apply LevelSetFact.singleton_1 in H; intuition.
Qed.

Definition LevelSet_mem_union (s s' : LevelSet.t) x :
  LevelSet.mem x (LevelSet.union s s') <-> LevelSet.mem x s \/ LevelSet.mem x s'.
Proof.
  rewrite LevelSetFact.union_b.
  apply orb_true_iff.
Qed.

Definition universe_level := Level.t.


Module Universe.
  Module Expr.
    (* level+1 if true. Except if Prop -> boolean ignored *)
    Definition t : Set := Level.t * bool.

    (* Warning: (lProp, true) represents also Prop *)
    Definition is_small (e : t) : bool :=
      match e with
      | (Level.lProp, _)
      | (Level.lSet, false) => true
      | _ => false
      end.

    Definition is_level (e : t) : bool :=
      match e with
      | (Level.lProp, _)
      | (_, false) => true
      | _ => false
      end.

    Definition is_prop (e : t) : bool :=
      match e with
      | (Level.lProp, _) => true
      | _ => false
      end.

    Definition equal (e1 e2 : t) : bool
      := match e1, e2 with
         | (Level.lProp, _), (Level.lProp, _) => true
         | (l1, b1), (l2, b2) => Level.equal l1 l2 && Bool.eqb b1 b2
         end.

    Definition get_level (e : t) : Level.t := fst e.

    Definition prop : t := (Level.prop, false).
    Definition set : t := (Level.set, false).
    Definition type1 : t := (Level.set, true).
  End Expr.

  Definition t : Set := non_empty_list Expr.t.

  Definition equal (u1 u2 : t) : bool :=
    NEL.forallb2 Expr.equal u1 u2.

  Definition make (l : Level.t) : t
    := NEL.sing (l, false).
  (** Create a universe representing the given level. *)

  Definition make' (e : Expr.t) : t
    := NEL.sing e.

  Definition make'' (e : Expr.t) (u : list Expr.t) : t
    := NEL.cons' e u.

  (* FIXME: take duplicates in account *)
  Definition is_level (u : t) : bool :=
    match u with
    | NEL.sing e => Expr.is_level e
    | _ => false
    end.
  (** Test if the universe is a level or an algebraic universe. *)

  Definition is_levels (u : t) : bool :=
    NEL.forallb Expr.is_level u.
  (** Test if the universe is a lub of levels or contains +n's. *)

  Definition level (u : t) : option Level.t :=
    match u with
    | NEL.sing (Level.lProp, _) => Some Level.lProp
    | NEL.sing (l, false) => Some l
    | _ => None
    end.
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  (* Definition levels (u : t) : list Level.t := *)
  (*   LevelSet.elements (NEL.fold_left (fun s '(l, _) => LevelSet.add l s) *)
  (*                                u LevelSet.empty). *)
  (* (** Get the levels inside the universe, forgetting about increments *) *)

  Definition is_small (u : t) : bool :=
    NEL.forallb Expr.is_small u.

  Definition is_prop (u : t) : bool :=
    NEL.forallb Expr.is_prop u.

  Definition type0m : t := make Level.prop.
  Definition type0 : t := make Level.set.
  Definition type1  :t := make' Expr.type1.

  Definition super (l : Level.t) : t :=
    if Level.is_small l then type1
    else make' (l, true).
  (** The universe strictly above FOR TYPING (not cumulativity) *)

  Definition try_suc (u : t) : t :=
    NEL.map (fun '(l, b) =>  (l, true)) u.

  (* FIXME: don't duplicate *)
  Definition sup (u1 u2 : t) : t := NEL.app u1 u2.
  (** The l.u.b. of 2 universes (naive because of duplicates) *)

  (* Definition existsb (P : Expr.t -> bool) (u : t) : bool := NEL.existsb P u. *)
  Definition for_all (P : Expr.t -> bool) (u : t) : bool := NEL.forallb P u.

  (** Type of product *)
  Definition sort_of_product (domsort rangsort : t) :=
    (* Prop impredicativity *)
    if Universe.is_prop rangsort then rangsort
    else Universe.sup domsort rangsort.

End Universe.

Definition universe := Universe.t.
Definition universe_coercion : universe -> list Universe.Expr.t := NEL.to_list.
Coercion universe_coercion : universe >-> list.


(** Sort families *)

Inductive sort_family : Set := InProp | InSet | InType.

Definition leb_sort_family x y :=
  match x, y with
  | InProp, _ => true
  | InSet, InProp => false
  | InType, (InProp | InSet) => false
  | _, _ => true
  end.

(** Family of a universe [u]. *)

Definition universe_family (u : universe) :=
  if Universe.is_prop u then InProp
  else if Universe.is_small u then InSet
  else InType.


Module ConstraintType.
  Inductive t : Set := Lt | Le | Eq.
End ConstraintType.

Definition constraint_type := ConstraintType.t.
Definition univ_constraint : Set := universe_level * ConstraintType.t * universe_level.

Module UnivConstraintDec.
  Definition t : Set := univ_constraint.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
    decide equality. decide equality. apply LevelDecidableType.eq_dec.
  Defined.
End UnivConstraintDec.
Module ConstraintSet <: MSetInterface.WSetsOn UnivConstraintDec := MSets.MSetWeakList.Make UnivConstraintDec.
Module ConstraintSetFact := MSetFacts.WFactsOn UnivConstraintDec ConstraintSet.
Module ConstraintSetProp := MSetProperties.WPropertiesOn UnivConstraintDec
                                                         ConstraintSet.

Definition make_univ_constraint : universe_level -> constraint_type -> universe_level -> univ_constraint
  := fun x y z => (x, y, z).

(** Needs to be in Type because template polymorphism of MSets does not allow setting
    the lowest universe *)
Definition constraints : Type := ConstraintSet.t.  (* list univ_constraint *)

Definition empty_constraint : constraints := ConstraintSet.empty.

(* Definition constraint_function A : Type := A -> A -> constraints -> constraints. *)
(* val enforce_eq : universe constraint_function *)
(* val enforce_leq : universe constraint_function *)
(* val enforce_eq_level : universe_level constraint_function *)
(* val enforce_leq_level : universe_level constraint_function *)


(** {6 Universe instances} *)

Module Instance.

  Definition t : Set := list Level.t.
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  Definition empty : t := [].
  Definition is_empty (i : t) : bool :=
    match i with
    | [] => true
    | _ => false
    end.

  Definition equal (i j : t) :=
    forallb2 Level.equal i j.

  Definition equal_upto (f : Level.t -> Level.t -> bool) (i j : t) :=
    forallb2 f i j.
End Instance.

Definition universe_instance := Instance.t.

(* val enforce_eq_instances : universe_instance constraint_function *)


Module UContext.
  Definition t := universe_instance × constraints.

  Definition make : Instance.t -> ConstraintSet.t -> t := pair.

  Definition empty : t := (Instance.empty, ConstraintSet.empty).
  (* val is_empty : t -> bool *)

  Definition instance : t -> Instance.t := fst.
  Definition constraints : t -> constraints := snd.

  Definition dest : t -> Instance.t * ConstraintSet.t := fun x => x.
End UContext.

Module AUContext.
  Definition t := list ident × constraints.

  Definition make (ids : list ident) (ctrs : constraints) : t := (ids, ctrs).
  Definition repr '((u, cst) : t) : UContext.t :=
    (mapi (fun i _ => Level.Var i) u, cst).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (repr uctx)).
End AUContext.

Module ContextSet.
  Definition t := LevelSet.t × constraints.

  Definition empty : t := (LevelSet.empty, ConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && ConstraintSet.is_empty (snd uctx).
End ContextSet.


(* Variance info is needed to do full universe polymorphism *)
Module Variance.
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.

(** Universe info for cumulative inductive types: A context of
   universe levels with universe constraints, representing local
   universe variables and constraints, together with an array of
   Variance.t.

    This data structure maintains the invariant that the variance
   array has the same length as the universe instance. *)
Module ACumulativityInfo.
  Definition t := AUContext.t × list Variance.t.

  Definition make ctx var : t := (ctx, var).
  (* Definition empty : t := (AUContext.empty, nil). *)
  (* val is_empty : t -> bool *)

  Definition univ_context : t -> AUContext.t := fst.
  Definition variance : t -> list Variance.t := snd.

  (** This function takes a universe context representing constraints
     of an inductive and produces a CumulativityInfo.t with the
     trivial subtyping relation. *)
  (* val from_universe_context : UContext.t -> t *)

  (* val leq_constraints : t -> Instance.t constraint_function *)
  (* val eq_constraints : t -> Instance.t constraint_function *)
End ACumulativityInfo.

Inductive universes_decl : Type :=
| Monomorphic_ctx (ctx : ContextSet.t)
| Polymorphic_ctx (cst : AUContext.t)
| Cumulative_ctx (ctx : ACumulativityInfo.t).


Definition monomorphic_udecl u :=
  match u with
  | Monomorphic_ctx ctx => ctx
  | _ => ContextSet.empty
  end.

Definition monomorphic_levels φ := (monomorphic_udecl φ).1.
Definition monomorphic_constraints φ := (monomorphic_udecl φ).2.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => fst ctx
  | Polymorphic_ctx ctx
  | Cumulative_ctx (ctx, _) => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => snd ctx
  | Polymorphic_ctx ctx
  | Cumulative_ctx (ctx, _) => snd (AUContext.repr ctx)
  end.


(** * Valuations *)

Import Level ConstraintType.


(** A valuation is a universe level (nat) given for each
    universe variable (Level.t).
    It is >= for polymorphic universes and > 0 for monomorphic universes. *)

Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Definition val0 (v : valuation) (l : Level.t) : Z :=
  match l with
  | lProp => -1
  | lSet => 0
  | Level s => Z.pos (v.(valuation_mono) s)
  | Var x => Z.of_nat (v.(valuation_poly) x)
  end.

Definition val1 v (e : Universe.Expr.t) : Z :=
  let n := val0 v (fst e) in
  if snd e && negb (is_prop (fst e)) then n + 1 else n.

Definition val (v : valuation) (u : universe) : Z :=
  match u with
  | NEL.sing e => val1 v e
  | NEL.cons e u => NEL.fold_left (fun n e => Z.max (val1 v e) n) u (val1 v e)
  end.

Definition llt `{checker_flags} (x y : Z) : Prop :=
  if prop_sub_type
  then (x < y)%Z
  else (0 <= x /\ x < y)%Z.

Notation "x < y" := (llt x y) : univ_scope.

Delimit Scope univ_scope with u.

Definition lle `{checker_flags} (x y : Z) : Prop :=
  (x < y)%u \/ x = y.

Notation "x <= y" := (lle x y) : univ_scope.

Section Univ.

Context `{cf : checker_flags}.

Inductive satisfies0 (v : valuation) : univ_constraint -> Prop :=
| satisfies0_Lt l l' : (val0 v l < val0 v l')%u -> satisfies0 v (l, Lt, l')
| satisfies0_Le l l' : (val0 v l <= val0 v l')%u -> satisfies0 v (l, Le, l')
| satisfies0_Eq l l' : val0 v l = val0 v l' -> satisfies0 v (l, Eq, l').

Definition satisfies v : constraints -> Prop :=
  ConstraintSet.For_all (satisfies0 v).

Definition consistent ctrs := exists v, satisfies v ctrs.

Definition eq_universe0 (φ : constraints) u u' :=
  forall v, satisfies v φ -> val v u = val v u'.

Definition leq_universe_n n (φ : constraints) u u' :=
  forall v, satisfies v φ -> (Z.of_nat n + val v u <= val v u')%Z.

Definition leq_universe0 := leq_universe_n 0.
Definition lt_universe := leq_universe_n 1.

Definition eq_universe φ u u'
  := if check_univs then eq_universe0 φ u u' else True.

Definition leq_universe φ u u'
  := if check_univs then leq_universe0 φ u u' else True.

(* ctrs are "enforced" by φ *)

Definition valid_constraints0 φ ctrs
  := forall v, satisfies v φ -> satisfies v ctrs.

Definition valid_constraints φ ctrs
  := if check_univs then valid_constraints0 φ ctrs else True.

Lemma valid_subset φ φ' ctrs
  : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
    ->  valid_constraints φ' ctrs.
Proof.
  unfold valid_constraints.
  destruct check_univs; [|trivial].
  intros Hφ H v Hv. apply H.
  intros ctr Hc. apply Hv. now apply Hφ.
Qed.


(** **** Lemmas about eq and leq **** *)

(** We show that equality and inequality of universes form an equivalence and
    a partial order (one w.r.t. the other).
    We use classes from [CRelationClasses] for consistency with the rest of the
    development which uses relations in [Type] rather than [Prop].
    These definitions hence use [Prop <= Type]. *)

Global Instance eq_universe0_refl φ : Reflexive (eq_universe0 φ).
Proof.
  intros vH s; reflexivity.
Qed.

Global Instance eq_universe_refl φ : Reflexive (eq_universe φ).
Proof.
  intro s.
  unfold eq_universe; destruct check_univs;
    [apply eq_universe0_refl|constructor].
Qed.

Global Instance leq_universe0_refl φ : Reflexive (leq_universe0 φ).
Proof.
  intros s vH; reflexivity.
Qed.

Global Instance leq_universe_refl φ : Reflexive (leq_universe φ).
Proof.
  intro s.
  unfold leq_universe; destruct check_univs;
    [apply leq_universe0_refl|constructor].
Qed.

Global Instance eq_universe0_sym φ : Symmetric (eq_universe0 φ).
Proof.
  intros s s' e vH. symmetry ; eauto.
Qed.

Global Instance eq_universe_sym φ : Symmetric (eq_universe φ).
Proof.
  unfold eq_universe. destruct check_univs ; eauto.
  eapply eq_universe0_sym.
Qed.

Global Instance eq_universe0_trans φ : Transitive (eq_universe0 φ).
Proof.
  intros s1 s2 s3 h1 h2 v h.
  etransitivity ; try eapply h1 ; eauto.
Qed.

Global Instance eq_universe_trans φ : Transitive (eq_universe φ).
Proof.
  intros s1 s2 s3.
  unfold eq_universe. destruct check_univs ; auto.
  intros h1 h2.
  eapply eq_universe0_trans ; eauto.
Qed.

Global Instance leq_universe0_trans φ : Transitive (leq_universe0 φ).
Proof.
  intros s1 s2 s3 h1 h2 v h. etransitivity.
  - eapply h1. assumption.
  - eapply h2. assumption.
Qed.

Global Instance leq_universe_trans φ : Transitive (leq_universe φ).
Proof.
  intros s1 s2 s3.
  unfold leq_universe. destruct check_univs ; auto.
  intros h1 h2.
  eapply leq_universe0_trans ; eauto.
Qed.


Lemma val_cons v e s
  : val v (NEL.cons e s) = Z.max (val1 v e) (val v s).
Proof.
  cbn. generalize (val1 v e); clear e.
  induction s.
  intro; cbn. apply Z.max_comm.
  intro; cbn in *. rewrite !IHs. Lia.lia.
Defined.

Lemma val_sup v s1 s2 :
  val v (Universe.sup s1 s2) = Z.max (val v s1) (val v s2).
Proof.
  induction s1.
  unfold Universe.sup, NEL.app. now rewrite val_cons.
  change (Universe.sup (NEL.cons a s1) s2) with (NEL.cons a (Universe.sup s1 s2)).
  rewrite !val_cons. rewrite IHs1. Lia.lia.
Qed.

Lemma leq_universe0_sup_l φ s1 s2 : leq_universe0 φ s1 (Universe.sup s1 s2).
Proof.
  intros v H. rewrite val_sup. Lia.lia.
Qed.

Lemma leq_universe0_sup_r φ s1 s2 : leq_universe0 φ s2 (Universe.sup s1 s2).
Proof.
  intros v H. rewrite val_sup. Lia.lia.
Qed.

Lemma leq_universe_product φ s1 s2
  : leq_universe φ s2 (Universe.sort_of_product s1 s2).
Proof.
  unfold leq_universe; destruct check_univs; [cbn|constructor].
  unfold Universe.sort_of_product; case_eq (Universe.is_prop s2); intro eq.
  apply leq_universe0_refl.
  apply leq_universe0_sup_r.
Qed.

(* Rk: [leq_universe φ s1 (sort_of_product s1 s2)] does not hold due
   impredicativity. *)

Global Instance eq_universe_leq_universe φ : subrelation (eq_universe φ) (leq_universe φ).
Proof.
  unfold eq_universe, leq_universe; destruct check_univs; [|intuition].
  intros u u' HH v Hv. rewrite (HH v Hv). apply BinInt.Z.le_refl.
Qed.

Global Instance eq_universe0_equivalence φ : Equivalence (eq_universe0 φ) :=
   {| Equivalence_Reflexive := _ ;
      Equivalence_Symmetric := _;
      Equivalence_Transitive := _ |}.

Global Instance eq_universe_equivalence φ : Equivalence (eq_universe φ) :=
   {| Equivalence_Reflexive := eq_universe_refl _ ;
      Equivalence_Symmetric := eq_universe_sym _;
      Equivalence_Transitive := eq_universe_trans _ |}.

Global Instance leq_universe_preorder φ : PreOrder (leq_universe φ) :=
   {| PreOrder_Reflexive := leq_universe_refl _ ;
      PreOrder_Transitive := leq_universe_trans _ |}.


Global Instance leq_universe0_antisym φ
  : Antisymmetric _ (eq_universe0 φ) (leq_universe0 φ).
Proof.
  intros t u tu ut. unfold leq_universe0, eq_universe0 in *.
  red in tu, ut.
  intros v sat.
  specialize (tu _ sat).
  specialize (ut _ sat).
  simpl in tu, ut. Lia.lia.
Qed.

Global Instance leq_universe_antisym φ
  : Antisymmetric _ (eq_universe φ) (leq_universe φ).
Proof.
  intros t u tu ut. unfold leq_universe, eq_universe in *.
  destruct check_univs; [|trivial]. eapply leq_universe0_antisym; auto.
Qed.

Global Instance leq_universe_partial_order φ
  : PartialOrder (eq_universe φ) (leq_universe φ).
Proof.
  intros x y; split. intros eqxy; split. now eapply eq_universe_leq_universe. red.
  now eapply eq_universe_leq_universe, symmetry.
  intros [l r]. now eapply leq_universe_antisym.
Defined.

(* This universe is a hack used in plugings to generate fresh universes *)
Definition fresh_universe : universe. exact Universe.type0. Qed.

End Univ.

Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

(* Check (_ : forall (cf : checker_flags) Σ, Reflexive (eq_universe Σ)). *)