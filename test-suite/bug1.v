(** Reported by Randy Pollack **)

Require Import MetaCoq.Template.Loader.
Require Import List.
Fixpoint fibrec (n:nat) (fs:list nat) {struct n} : nat :=
  match n with
    | 0 => hd 0 fs
    | (S n) => fibrec n (cons ((hd 0 fs) + (hd 0 (tl fs))) fs)
  end.
Definition fib n := fibrec n (cons 0 (cons 1 nil)).
MetaCoq Quote Definition qfib := fib.  (** works **)
MetaCoq Quote Recursively Definition qfib_syntax := fib.
