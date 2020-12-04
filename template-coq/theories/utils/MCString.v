From Coq Require Import String Decimal DecimalString ZArith.
From MetaCoq.Template Require Import MCCompare.

Local Open Scope string_scope.

(** When defining [Show] instance for your own datatypes, you sometimes need to
    start a new line for better printing. [nl] is a shorthand for it. *)
Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f "," l ++ "]".

Definition print_list {A} (f : A -> string) (sep : string) (l : list A) : string :=
  string_of_list_aux f sep l.

Definition parens (top : bool) (s : string) :=
  if top then s else "(" ++ s ++ ")".

Definition string_of_nat n : string :=
  DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Hint Resolve String.string_dec : eq_dec.

Definition string_of_positive p := 
  string_of_nat (Pos.to_nat p).

Definition string_of_Z (z : Z) : string := 
  match z with
  | Z0 => "0"
  | Zpos p => string_of_positive p
  | Zneg p => "-" ++ string_of_positive p
  end.

Definition eq_string s s' :=
  match string_compare s s' with
  | Eq => true
  | _ => false
  end.

Lemma eq_string_refl x : is_true (eq_string x x).
Proof.
  unfold eq_string.
  now rewrite (proj2 (string_compare_eq x x) eq_refl).
Qed.
