Require Import List Program.
Require Import Template.Template Template.XAst.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Require Import Template.Induction.

Set Asymmetric Patterns.

Fixpoint lift n k t : xterm :=
  match t with
  | xRel i => if Nat.leb k i then xRel (n + i) else xRel i
  | xLambda na T V M => xLambda na (lift n k T) (lift n (S k) V) (lift n (S k) M)
  | xApp u A B v =>
    xApp (lift n k u) (lift n k A) (lift n (S k) B) (lift n k v)
  | xProd na A B => xProd na (lift n k A) (lift n (S k) B)
  | xEq A u v => xEq (lift n k A) (lift n k u) (lift n k v)
  | xRefl A u => xRefl (lift n k A) (lift n k u)
  | x => x
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst t k u :=
  match u with
  | xRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Gt => xRel n
    | Lt => xRel (pred n)
    end
  | xLambda na T V M =>
    xLambda na (subst t k T) (subst t (S k) V) (subst t (S k) M)
  | xApp u A B v =>
    xApp (subst t k u) (subst t k A) (subst t (S k) B) (subst t k v)
  | xProd na A B => xProd na (subst t k A) (subst t (S k) B)
  | xEq A u v => xEq (subst t k A) (subst t k u) (subst t k v)
  | xRefl A u => xRefl (subst t k A) (subst t k u)
  | x => x
  end.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity).