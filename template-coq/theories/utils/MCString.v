From Coq Require Import String.
From Coq.Numbers Require Import (* DecimalString *) Int63.
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
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | 10 => "10"
  | 11 => "11"
  | 12 => "12"
  | 13 => "13"
  | 14 => "14"
  | 15 => "15"
  | 16 => "16"
  | 17 => "17"
  | 18 => "18"
  | 19 => "19"
  | 20 => "20"
  | 21 => "21"
  | 22 => "22"
  | 23 => "23"
  | 24 => "24"
  | 25 => "25"
  | 26 => "26"
  | 27 => "27"
  | 28 => "28"
  | 29 => "29"
  | 30 => "30"
  | 31 => "31"
  | 32 => "32"
  | 33 => "33"
  | 34 => "34"
  | 35 => "35"
  | 36 => "36"
  | 37 => "37"
  | 38 => "38"
  | 39 => "39"
  | 40 => "40"
  | 41 => "41"
  | 42 => "42"
  | 43 => "43"
  | 44 => "44"
  | 45 => "45"
  | 46 => "46"
  | 47 => "47"
  | 48 => "48"
  | 49 => "49"
  | _ => "todo string_of_nat"
  end.


(* Definition string_of_nat n : string := DecimalString.NilZero.string_of_uint (Nat.to_uint n). *)
(* Definition string_of_int (i:Int63.int) : string := BinNat.N.to_uint (BinInt.Z.to_N (Int63.to_Z i))). *)
Definition string_of_int (i:Int63.int) : string := 
  (if Int63.ltb i 8
  then
    if Int63.ltb i 4
    then
      if Int63.ltb i 2
      then if Int63.ltb i 1 then "0" else "1"
      else if Int63.ltb i 3 then "2" else "3"
    else
      if Int63.ltb i 6
      then if Int63.ltb i 5 then "4" else "5"
      else if Int63.ltb i 7 then "6" else "7"
  else if Int63.eqb i 42 then "42" else "todo string_of_int")%int63.

Hint Resolve String.string_dec : eq_dec.


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
