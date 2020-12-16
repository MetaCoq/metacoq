(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst.


Definition def_size (size : term -> nat) (x : def term)
  := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (list_size size p.(pparams) + size p.(preturn) + 
    size c + list_size (size ∘ bbody) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | x => 1
  end.
