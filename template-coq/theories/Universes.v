Require Import Ascii String ZArith List utils.
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

  (* Definition level_dec (l1 l2 : Level.t) : {l1 = l2}+{l1 <> l2}. *)
  (*   decide equality. apply string_dec. apply Peano_dec.eq_nat_dec. *)
  (* Defined. *)
  (* Definition equal (l1 l2 : Level.t) : bool *)
  (*   := if level_dec l1 l2 then true else false. *)
  Definition equal (l1 l2 : Level.t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.
  (** Equality function *)

  (* val hash : t -> int *)
  (* val make : Names.DirPath.t -> int -> t *)
  (* (** Create a new universe level from a unique identifier and an associated *)
  (*     module path. *) *)
  (* val pr : t -> Pp.std_ppcmds *)
  (* (** Pretty-printing *) *)
  (* val to_string : t -> string *)
  (* (** Debug printing *) *)
  (* val var : int -> t *)
  (* val var_index : t -> int option *)
End Level.

Require FSets.FSetWeakList.
Require FSets.FMapWeakList.
Module LevelDecidableType.
   Definition t : Type := Level.t.
   Definition eq : t -> t -> Prop := eq.
   Definition eq_refl : forall x : t, eq x x := @eq_refl _.
   Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
   Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
   Definition eq_equiv : RelationClasses.Equivalence eq.
   Proof. constructor. red. apply eq_refl. red. apply eq_sym. red. apply eq_trans. Defined.
   Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
     unfold eq. decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
   Defined.
End LevelDecidableType.
Module LevelSet <: (MSetInterface.WSetsOn LevelDecidableType) := MSets.MSetWeakList.Make LevelDecidableType.
Module LevelMap := FSets.FMapWeakList.Make LevelDecidableType.

Definition universe_level := Level.t.


Module Universe.
  Module Expr.
    Definition t : Set := Level.t * bool. (* level+1 if true *)

    Definition is_small (e : t) : bool :=
      match e with
      | (l, false) => Level.is_small l
      | _ => false
      end.

    Inductive super_result :=
    | SuperSame (_ : bool)
    (* The level expressions are in cumulativity relation. boolean
           indicates if left is smaller than right?  *)
    | SuperDiff (_ : comparison).
    (* The level expressions are unrelated, the comparison result
           is canonical *)

    (** [super u v] compares two level expressions,
       returning [SuperSame] if they refer to the same level at potentially different
       increments or [SuperDiff] if they are different. The booleans indicate if the
       left expression is "smaller" than the right one in both cases. *)
    Definition super (x y : t) : super_result :=
      match Level.compare (fst x) (fst y) with
      | Eq => SuperSame (bool_lt' (snd x) (snd y))
      | cmp =>
	  match x, y with
	  | (l, false), (l', false) =>
	    match l, l' with
	    | Level.lProp, Level.lProp => SuperSame false
	    | Level.lProp, _ => SuperSame true
	    | _, Level.lProp => SuperSame false
	    | _, _ => SuperDiff cmp
            end
	  | _, _ => SuperDiff cmp
          end
      end.


    Definition is_level (e : t) : bool :=
      match e with
      | (_, false) => true
      | _ => false
      end.

    Definition equal (e1 e2 : t) : bool
      := Level.equal (fst e1) (fst e2) && Bool.eqb (snd e1) (snd e2).

    Definition get_level (e : t) : Level.t := fst e.

    Definition prop : t := (Level.prop, false).
    Definition set : t := (Level.set, false).
    Definition type1 : t := (Level.set, true).
  End Expr.

  (** INVARIANTS: not empty, sorted ??, no duplicate *)
  Definition t : Set := non_empty_list Expr.t.

  Definition universe_coercion : t -> list Expr.t := @projT1 _ _.
  Coercion universe_coercion : t >-> list.


  (* val compare : t -> t -> int *)
  (* (** Comparison function *) *)

  Definition equal (u1 u2 : t) : bool :=
    forallb2 Expr.equal u1 u2.
  (* Equality function on formal universes *)
  (* val hash : t -> int *)
  (* (** Hash function *) *)

  Definition make (l : Level.t) : t
    := make_non_empty_list (l, false) [].
  (** Create a universe representing the given level. *)

  Definition make' (e : Expr.t) : t
    := make_non_empty_list e [].

  Definition make'' (e : Expr.t) (u : list Expr.t) : t
    := make_non_empty_list e u.
  (* val pr : t -> Pp.std_ppcmds *)
  (* (** Pretty-printing *) *)
  (* val pr_with : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds *)

  Definition is_level (u : t) : bool :=
    match (u : list _) with
    | [(_, false)] => true
    | _ => false
    end.
  (** Test if the universe is a level or an algebraic universe. *)

  Definition is_levels (u : t) : bool :=
    forallb Expr.is_level u.
  (** Test if the universe is a lub of levels or contains +n's. *)

  Definition level (u : t) : option Level.t :=
    match (u : list _) with
    | [(l, false)] => Some l
    | _ => None
    end.
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  Definition levels (u : t) : list Level.t :=
    LevelSet.elements (fold_left (fun s '(l, _) => LevelSet.add l s)
                                 u LevelSet.empty).
  (** Get the levels inside the universe, forgetting about increments *)

  Definition is_small (u : t) : bool :=
    match (u : list _) with
    | [e] => Expr.is_small e
    | _ => false
    end.

  Definition is_prop s :=
    match Universe.level s with
    | Some l => Level.is_prop l
    | None => false
    end.

  Definition type0m : t := make Level.prop.
  Definition type0 : t := make Level.set.
  Definition type1  :t := make' Expr.type1.

  Definition super (u : Level.t) : t :=
    if Level.is_small u then type1
    else make' (u, true).
  (** The universe strictly above *)

  Fixpoint insert {A} `{ComparableType A} (x : A) (l : list A) :=
    match l with
    | [] => [x]
    | y :: l' =>  match compare x y with
                 | Eq => l
                 | Lt => x :: l
                 | Gt => y :: (insert x l')
                 end
    end.

  Fixpoint merge_univs (fuel : nat) (l1 l2 : list Expr.t) : list Expr.t :=
    match fuel with
    | O => l1
    | S fuel => match l1, l2 with
               | [], _ => l2
               | _, [] => l1
               | h1 :: t1, h2 :: t2 =>
                 match Expr.super h1 h2 with
	         | Expr.SuperSame true (* h1 < h2 *) => merge_univs fuel t1 l2
	         | Expr.SuperSame false => merge_univs fuel l1 t2
	         | Expr.SuperDiff Lt (* h1 < h2 is name order *)
                   => h1 :: (merge_univs fuel t1 l2)
                 | _ => h2 :: (merge_univs fuel l1 t2)
                 end
               end
    end.

  Program Definition sup (u1 u2 : t) : t :=
    (merge_univs (length u1 + length u2 + 1) u1 u2; _).
  Next Obligation.
  Admitted. (* TODO *)
  (** The l.u.b. of 2 universes *)

  Definition existsb : (Expr.t -> bool) -> t -> bool := @existsb _.
  Definition for_all : (Expr.t -> bool) -> t -> bool := @forallb _.

  (* Type of product *)

  Definition sort_of_product (domsort rangsort:t) :=
  match (domsort, rangsort) with
  (* Product rule (s,Prop,Prop) *)
    | (_,([(Level.lProp,false)]; _))  => rangsort
    (* (* Product rule (Type_i,Type_i,Type_i) *) *)
    | (u1,u2) => Universe.sup u1 u2
  end.

           
End Universe.

Definition universe := Universe.t.
Definition universe_coercion : universe -> list Universe.Expr.t := @projT1 _ _.
Coercion universe_coercion : universe >-> list.

Module ConstraintType.
  Inductive t : Set := Lt | Le | Eq.
End ConstraintType.

Definition constraint_type := ConstraintType.t.
Definition univ_constraint : Set := universe_level * ConstraintType.t * universe_level.

Require MSets.MSetWeakList.
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

Definition make_univ_constraint : universe_level -> constraint_type -> universe_level -> univ_constraint
  := fun x y z => (x, y, z).

(** Needs to be in Type because template polymorphism of MSets does not allow setting
    the lowest universe *)
Definition constraints : Type := ConstraintSet.t.  (* list univ_constraint *)

(* val empty_constraint : constraints *)
(* val union_constraint : constraints -> constraints -> constraints *)
(* val eq_constraint : constraints -> constraints -> bool *)

(** A value with universe constraints. *)
Definition constrained A : Type := A * constraints.

(** Constrained *)
Definition constraints_of {A} : constrained A -> constraints := snd.

(** Enforcing constraints. *)

Definition constraint_function A : Type := A -> A -> constraints -> constraints.

(* val enforce_eq : universe constraint_function *)
(* val enforce_leq : universe constraint_function *)
(* val enforce_eq_level : universe_level constraint_function *)
(* val enforce_leq_level : universe_level constraint_function *)

(* (** {6 Substitution} *) *)

(* type universe_subst_fn = universe_level -> universe *)
(* type universe_level_subst_fn = universe_level -> universe_level *)

(* (** A full substitution, might involve algebraic universes *) *)
(* type universe_subst = universe universe_map *)
(* type universe_level_subst = universe_level universe_map *)

(* val level_subst_of : universe_subst_fn -> universe_level_subst_fn *)


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

  (* val of_array : Level.t array -> t *)
  (* val to_array : t -> Level.t array *)
  (* val append : t -> t -> t *)
  (* (** To concatenate two instances, used for discharge *) *)

  Definition equal (i j : t) :=
    forallb2 Level.equal i j.

  Definition equal_upto (f : Level.t -> Level.t -> bool) (i j : t) :=
    forallb2 f i j.

  (* val equal : t -> t -> bool *)
  (* (** Equality *) *)
  (* val length : t -> int *)
  (* (** Instance length *) *)
  (* val hcons : t -> t *)
  (* (** Hash-consing. *) *)
  (* val hash : t -> int *)
  (* (** Hash value *) *)
  (* val share : t -> t * int *)
  (* (** Simultaneous hash-consing and hash-value computation *) *)
  (* val subst_fn : universe_level_subst_fn -> t -> t *)
  (* (** Substitution by a level-to-level function. *) *)
  (* val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds *)
  (* (** Pretty-printing, no comments *) *)
  (* val levels : t -> LSet.t *)
  (* (** The set of levels in the instance *) *)
End Instance.

Definition universe_instance := Instance.t.

(* val enforce_eq_instances : universe_instance constraint_function *)

Definition puniverses A : Type := A * universe_instance.
Definition out_punivs {A} : puniverses A -> A := fst.
Definition in_punivs {A} (x : A) : puniverses A := (x, Instance.empty).

(* val eq_puniverses : ('a -> 'a -> bool) -> 'a puniverses -> 'a puniverses -> bool *)


Module UContext.
  Definition t := constrained Instance.t.

  (* Definition make : constrained Instance.t -> t := fun x => x. *)
  Definition make : Instance.t -> ConstraintSet.t -> t := pair.

  Definition empty : t := (Instance.empty, ConstraintSet.empty).
  (* val is_empty : t -> bool *)

  Definition instance : t -> Instance.t := fst.
  Definition constraints : t -> constraints := snd.

  Definition dest : t -> Instance.t * ConstraintSet.t := fun x => x.

  (* (** Keeps the order of the instances *) *)
  (* val union : t -> t -> t *)
  (* (* the number of universes in the context *) *)
  (* val size : t -> int *)
End UContext.

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
  (* val pr : t -> Pp.t *)
End Variance.

(** Universe info for cumulative inductive types: A context of
   universe levels with universe constraints, representing local
   universe variables and constraints, together with an array of
   Variance.t.

    This data structure maintains the invariant that the variance
   array has the same length as the universe instance. *)
Module CumulativityInfo.
  Definition t := prod UContext.t (list Variance.t).

  Definition empty : t := (UContext.empty, nil).
  (* val is_empty : t -> bool *)

  Definition univ_context : t -> UContext.t := fst.
  Definition variance : t -> list Variance.t := snd.

  (** This function takes a universe context representing constraints
     of an inductive and produces a CumulativityInfo.t with the
     trivial subtyping relation. *)
  (* val from_universe_context : UContext.t -> t *)

  (* val leq_constraints : t -> Instance.t constraint_function *)
  (* val eq_constraints : t -> Instance.t constraint_function *)
End CumulativityInfo.

Inductive universe_context : Type :=
| Monomorphic_ctx (ctx : UContext.t)
| Polymorphic_ctx (cst : UContext.t)
| Cumulative_ctx (ctx : CumulativityInfo.t).


(** * Valuations *)

Import Level ConstraintType.

Record valuation := 
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Fixpoint val0 (v : valuation) (l : Level.t) : Z :=
  match l with
  | lProp => -1
  | lSet => 0
  | Level s => Zpos (v.(valuation_mono) s)
  | Var x => Z.of_nat (v.(valuation_poly) x)
  end.

Definition val1 v (e : Universe.Expr.t) : Z :=
  let n := val0 v (fst e) in
  if snd e then n + 1 else n.

Program Definition val (v : valuation) (u : universe) : Z :=
  match u : list _ with
  | [] => _
  | e :: u => List.fold_left (fun n e => Z.max (val1 v e) n) u (val1 v e)
  end.
Next Obligation.
  apply False_rect.
  apply u.2; assumption.
Defined.

Inductive satisfies0 (v : valuation) : univ_constraint -> Prop :=
| satisfies0_Lt l l' : (val0 v l < val0 v l')%Z -> satisfies0 v (l, Lt, l')
| satisfies0_Le l l' : (val0 v l <= val0 v l')%Z -> satisfies0 v (l, Le, l')
| satisfies0_Eq l l' : val0 v l = val0 v l' -> satisfies0 v (l, Eq, l').

Definition satisfies v : constraints -> Prop := 
  ConstraintSet.For_all (satisfies0 v).

Definition consistent ctrs := exists v, satisfies v ctrs.

Definition eq_universe (φ : constraints) u u' :=
  forall v : valuation, satisfies v φ -> val v u = val v u'.

Definition leq_universe (φ : constraints) u u' :=
  forall v : valuation, satisfies v φ -> (val v u <= val v u')%Z.

Definition lt_universe (φ : constraints) u u' :=
  forall v : valuation, satisfies v φ -> (val v u < val v u')%Z.


Require Import config.

Definition eq_universe' `{checker_flags} φ u u'
  := if check_univs then eq_universe φ u u' else True.

Definition leq_universe' `{checker_flags} φ u u'
  := if check_univs then leq_universe φ u u' else True.


Program Definition try_suc (u : universe) : universe :=   (* FIXME suc s *)
  (map (fun '(l, b) =>  (l, true)) u; _).
Next Obligation.
  intro. apply u.2. destruct u as [[] ?].
  reflexivity. discriminate.
Qed.

Conjecture leq_universe_product_l : forall `{checker_flags} φ s1 s2,
    leq_universe' φ s1 (Universe.sort_of_product s1 s2).
Conjecture leq_universe_product_r : forall `{checker_flags} φ s1 s2,
    leq_universe' φ s2 (Universe.sort_of_product s1 s2).
