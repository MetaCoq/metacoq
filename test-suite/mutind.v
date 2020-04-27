Require Import MetaCoq.Template.Loader.

Section with_T.
  Variable T : Type.

  Inductive tree :=
  | leaf
  | node : tree -> tree_list -> tree -> tree
  with tree_list :=
  | tdata : T -> tree_list
  | tcons : tree -> tree_list -> tree_list.

  Fixpoint count_tree (t : tree) : nat :=
    match t with
      | leaf => 0
      | node a b c => count_tree a + count_list b + count_tree c
    end
  with count_list (l : tree_list) : nat :=
    match l with
      | tdata _ => 1
      | tcons t l => count_tree t + count_list l
    end.
End with_T.

Local Open Scope string_scope.
Local Open Scope positive_scope.
MetaCoq Quote Recursively Definition count_tree_syntax := count_tree.
