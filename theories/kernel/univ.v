Require Import String List.
Import ListNotations.

(* Sorted lists without duplicates *)
Class ComparableType A := { compare : A -> A -> comparison }.
Arguments compare {A} {_} _ _.

Fixpoint insert {A} `{ComparableType A} (x : A) (l : list A) :=
  match l with
  | [] => [x]
  | y :: l' =>  match compare x y with
               | Eq => l
               | Lt => x :: l
               | Gt => y :: (insert x l')
               end
  end.

Definition list_union {A} `{ComparableType A} (l l' : list A) : list A
  := fold_left (fun l' x => insert x l') l l'.

(* FIXME *)
Definition compare_string s1 s2 := Nat.compare (String.length s1) (String.length s2).

Definition compare_bool b1 b2 :=
  match b1, b2 with
  | false, true => Lt
  | true, false => Gt
  | _, _ => Eq
  end.

Definition bool_lt b1 b2 := match compare_bool b1 b2 with Lt => true | _ => false end.





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
    | Level s1, Level s2 => compare_string s1 s2
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
   Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
     unfold eq. repeat decide equality.
   Defined.
End LevelDecidableType.
Module LevelSet := FSets.FSetWeakList.Make LevelDecidableType.
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
      | Eq => SuperSame (bool_lt (snd x) (snd y))
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
  Definition t : Set := list Expr.t.

  (* val compare : t -> t -> int *)
  (* (** Comparison function *) *)

  Definition equal (u1 u2 : t) : bool :=
    false. (* FIXME *)
  (* Equality function on formal universes *)
  (* val hash : t -> int *)
  (* (** Hash function *) *)

  Definition make (l : Level.t) : t := [(l, false)].
  (** Create a universe representing the given level. *)

  (* val pr : t -> Pp.std_ppcmds *)
  (* (** Pretty-printing *) *)
  (* val pr_with : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds *)

  Definition is_level (u : t) : bool :=
    match u with
    | [(_, false)] => true
    | _ => false
    end.
  (** Test if the universe is a level or an algebraic universe. *)

  Definition is_levels (u : t) : bool :=
    forallb Expr.is_level u.
  (** Test if the universe is a lub of levels or contains +n's. *)

  Definition level (u : t) : option Level.t :=
    match u with
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
    match u with
    | [e] => Expr.is_small e
    | _ => false
    end.

  Definition type0m := [Expr.prop].
  Definition type0 := [Expr.set].
  Definition type1 := [Expr.type1].

  Definition super (u : Level.t) : t :=
    if Level.is_small u then type1
    else [(u, true)].
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

  Fixpoint merge_univs (fuel : nat) (l1 l2 : t) : t :=
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

  Definition sup (u1 u2 : t) : t :=
    merge_univs (length u1 + length u2 + 1) u1 u2.
  (** The l.u.b. of 2 universes *)

  Definition existsb : (Expr.t -> bool) -> t -> bool := @existsb _.
  Definition for_all : (Expr.t -> bool) -> t -> bool := @forallb _.
End Universe.

Definition universe := Universe.t.

Inductive constraint_type : Set := Lt | Le | Eq.
Definition univ_constraint : Set := universe_level * constraint_type * universe_level.

Definition make_univ_constraint : universe_level -> constraint_type -> universe_level -> univ_constraint
  := fun x y z => (x, y, z).


Require MSets.MSetWeakList.
Module ConstraintTypeDec.
  Definition t := univ_constraint.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq. repeat decide equality.
  Defined.
End ConstraintTypeDec.
Module Constraint := MSets.MSetWeakList.Make ConstraintTypeDec.

Definition constraints := Constraint.t.  (* list univ_constraint *)

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

  Definition t := list Level.t.
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
  Definition make : Instance.t -> Constraint.t -> t := pair.

  Definition empty : t := (Instance.empty, Constraint.empty).
  (* val is_empty : t -> bool *)

  Definition instance : t -> Instance.t := fst.
  Definition constraints : t -> constraints := snd.

  Definition dest : t -> Instance.t * Constraint.t := fun x => x.

  (* (** Keeps the order of the instances *) *)
  (* val union : t -> t -> t *)
  (* (* the number of universes in the context *) *)
  (* val size : t -> int *)
End UContext.

Definition universe_context := UContext.t.

(* (** Universe info for inductive types: A context of universe levels *)
(*     with universe constraints, representing local universe variables *)
(*     and constraints, together with a context of universe levels with *)
(*     universe constraints, representing conditions for subtyping used *)
(*     for inductive types. *)

(*     This data structure maintains the invariant that the context for *)
(*     subtyping constraints is exactly twice as big as the context for *)
(*     universe constraints. *) *)
(* module CumulativityInfo : *)
(* sig *)
(*   type t *)

(*   val make : universe_context * universe_context -> t *)

(*   val empty : t *)
(*   val is_empty : t -> bool *)

(*   val univ_context : t -> universe_context *)
(*   val subtyp_context : t -> universe_context *)

(*   (** This function takes a universe context representing constraints *)
(*       of an inductive and a Instance.t of fresh universe names for the *)
(*       subtyping (with the same length as the context in the given *)
(*       universe context) and produces a UInfoInd.t that with the *)
(*       trivial subtyping relation. *) *)
(*   val from_universe_context : universe_context -> universe_instance -> t *)

(*   val subtyping_susbst : t -> universe_level_subst *)

(* end *)

(* type cumulativity_info = CumulativityInfo.t *)
