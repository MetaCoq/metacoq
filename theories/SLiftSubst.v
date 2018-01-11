Require Import List Program.
Require Import Template.Template Template.SAst.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Require Import Template.Induction.

Set Asymmetric Patterns.

Fixpoint lift n k t : sterm :=
  match t with
  | sRel i => if Nat.leb k i then sRel (n + i) else sRel i
  | sLambda na T V M => sLambda na (lift n k T) (lift n (S k) V) (lift n (S k) M)
  | sApp u na A B v =>
    sApp (lift n k u) na (lift n k A) (lift n (S k) B) (lift n k v)
  | sProd na A B => sProd na (lift n k A) (lift n (S k) B)
  | sEq s A u v => sEq s (lift n k A) (lift n k u) (lift n k v)
  | sRefl A u => sRefl (lift n k A) (lift n k u)
  | sJ A u P w v p =>
    sJ (lift n k A)
       (lift n k u)
       (lift n (S (S k)) P)
       (lift n k w)
       (lift n k v)
       (lift n k p)
  | sUip A u v p q =>
    sUip (lift n k A) (lift n k u) (lift n k v) (lift n k p) (lift n k q)
  | sFunext A B f g e =>
    sFunext (lift n k A) (lift n (S k) B) (lift n k f) (lift n k g) (lift n k e)
  | sSig na A B => sSig na (lift n k A) (lift n (S k) B)
  | sPair A B u v =>
    sPair (lift n k A) (lift n (S k) B) (lift n k u) (lift n k v)
  | sSigLet A B p P t =>
    sSigLet (lift n k A)
            (lift n (S k) B)
            (lift n k p)
            (lift n (S k) P)
            (lift n (S (S k)) t)
  | x => x
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst t k u :=
  match u with
  | sRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Gt => sRel n
    | Lt => sRel (pred n)
    end
  | sLambda na T V M =>
    sLambda na (subst t k T) (subst t (S k) V) (subst t (S k) M)
  | sApp u na A B v =>
    sApp (subst t k u) na (subst t k A) (subst t (S k) B) (subst t k v)
  | sProd na A B => sProd na (subst t k A) (subst t (S k) B)
  | sEq s A u v => sEq s (subst t k A) (subst t k u) (subst t k v)
  | sRefl A u => sRefl (subst t k A) (subst t k u)
  | x => x
  end.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity) : s_scope.