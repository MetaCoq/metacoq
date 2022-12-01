
Require Import Recdef.
Require Import Coq.micromega.Lia.
Set Implicit Arguments.

(** A function defined using measure or well-founded relation **)
Function Plus1 (n: nat) {measure id n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. unfold id. abstract lia.
Defined.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import MetaCoq.Template.Loader.
Require Import MetaCoq.Template.All.

From MetaCoq.Template Require Import Pretty.
(* Use template-coq to make a [program] from function defined above *)
Time MetaCoq Quote Recursively Definition p_Plus1 := Plus1.

(* Eval cbv in (print_program false 1 p_Plus1).
Eval lazy in (print_term (empty_ext (fst p_Plus1)) nil true (snd p_Plus1)). *)

(** The program p_Plus1 is too big to read, so we define some
*** diagnostic software **)
Section occ_term_Sec.
Variable str:kername.
  (** does [tConst str] occur in a term? **)
Fixpoint pocc_term (n:nat) (t:term): bool :=
  match n with
    | 0 => false
    | S n =>
      match t with
        | tCast t _ ty => pocc_term n t || pocc_term n ty
        | tProd _ ty t => pocc_term n t || pocc_term n ty
        | tLambda _ ty t => pocc_term n t || pocc_term n ty
        | tLetIn _ dfn ty t => pocc_term n dfn || pocc_term n t || pocc_term n ty
        | tApp fn args => pocc_term n fn || fold_left orb (map (pocc_term n) args) false
        | tConst nm _ => if eqb str nm then true else false
        | tCase _ ty mch brs =>
          existsb (pocc_term n) (pparams ty) || pocc_term n (preturn ty) ||
          pocc_term n mch ||
          fold_left orb (map (fun x => pocc_term n (bbody x)) brs) false
        | tFix ds _ =>
          fold_left
            orb (map (fun x => pocc_term n (dtype x) || pocc_term n (dbody x)) ds) false
        | _ => false
      end
  end.
  (** does [tConst str] occur anywhere in a program? **)

Definition bound_global_decl (d : kername * global_decl) : bool :=
  if eq_kername str (fst d) then true else false.

Definition bound_program (p : program) := List.existsb bound_global_decl (fst p).(declarations).

Definition pocc_global_decl (d : kername * global_decl) : bool :=
match snd d with
| ConstantDecl {| cst_type := ty;  cst_body := Some t |} => pocc_term 2000 ty || pocc_term 2000 t
| ConstantDecl {| cst_type := ty;  cst_body := None |} => pocc_term 2000 ty
| InductiveDecl _ => false
end.

Definition pocc_program p := pocc_term 2000 (snd p) || List.existsb pocc_global_decl (fst p).(declarations).

End occ_term_Sec.

Require Import List. Import ListNotations. Open Scope bs_scope.
(* MetaCoq Test Unquote (tConst (MPfile ["Nat"; "PeanoNat"; "Arith"; "Coq"], "pred") []) . *)

Eval vm_compute in (eq_refl : pocc_program (MPfile ["Nat"; "PeanoNat"; "Arith"; "Coq"], "pred") p_Plus1 = false).
Eval vm_compute in (eq_refl : bound_program (MPfile ["Nat"; "PeanoNat"; "Arith"; "Coq"], "pred") p_Plus1 = false).

Eval vm_compute in (eq_refl : pocc_program (MPfile ["Nat"; "Init"; "Coq"], "pred") p_Plus1 = true).
Eval vm_compute in (eq_refl : bound_program (MPfile ["Nat"; "Init"; "Coq"], "pred") p_Plus1 = true).
