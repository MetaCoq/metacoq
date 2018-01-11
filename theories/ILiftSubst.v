Require Import List Program.
Require Import Template.Template Template.IAst.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Require Import Template.Induction.

Set Asymmetric Patterns.

Fixpoint lift n k t : iterm :=
  match t with
  | iRel i => if Nat.leb k i then iRel (n + i) else iRel i
  | iLambda na T V M => iLambda na (lift n k T) (lift n (S k) V) (lift n (S k) M)
  | iApp u na A B v =>
    iApp (lift n k u) na (lift n k A) (lift n (S k) B) (lift n k v)
  | iProd na A B => iProd na (lift n k A) (lift n (S k) B)
  | iEq s A u v => iEq s (lift n k A) (lift n k u) (lift n k v)
  | iRefl A u => iRefl (lift n k A) (lift n k u)
  | x => x
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst t k u :=
  match u with
  | iRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Gt => iRel n
    | Lt => iRel (pred n)
    end
  | iLambda na T V M =>
    iLambda na (subst t k T) (subst t (S k) V) (subst t (S k) M)
  | iApp u na A B v =>
    iApp (subst t k u) na (subst t k A) (subst t (S k) B) (subst t k v)
  | iProd na A B => iProd na (subst t k A) (subst t (S k) B)
  | iEq s A u v => iEq s (subst t k A) (subst t k u) (subst t k v)
  | iRefl A u => iRefl (subst t k A) (subst t k u)
  | x => x
  end.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity) : i_scope.