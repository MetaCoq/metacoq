
Require Import Recdef.
Require Import Coq.omega.Omega.
Set Implicit Arguments.

(** A function defined using measure or well-founded relation **)
Function Plus1 (n: nat) {measure id n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. unfold id. abstract omega.
Defined.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import MetaCoq.Template.Loader.
Require Import MetaCoq.Template.Ast.

Unset Template Cast Propositions.

(* Use template-coq to make a [program] from function defined above *)
Time MetaCoq Quote Recursively Definition p_Plus1 := Plus1.

(** The program p_Plus1 is too big to read, so we define some
*** diagnostic software **)
Section occ_term_Sec.
Variable str:string.
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
        | tConst nm _ => if string_dec str nm then true else false
        | tCase _ ty mch brs =>
          pocc_term n ty || pocc_term n mch ||
                    fold_left orb (map (fun x => pocc_term n (snd x)) brs) false
        | tFix ds _ =>
          fold_left
            orb (map (fun x => pocc_term n (dtype x) || pocc_term n (dbody x)) ds) false
        | _ => false
      end
  end.
  (** does [tConst str] occur anywhere in a program? **)

Definition bound_global_decl (d : global_decl) : bool :=
  match d with
  | ConstantDecl kn _
  | InductiveDecl kn _ => if string_dec str kn then true else false
  end.

Definition bound_program (p : program) := List.existsb bound_global_decl (fst p).

Definition pocc_global_decl (d : global_decl) : bool :=
match d with
| ConstantDecl kn {| cst_type := ty;  cst_body := Some t |} => pocc_term 2000 ty || pocc_term 2000 t
| ConstantDecl kn {| cst_type := ty;  cst_body := None |} => pocc_term 2000 ty
| InductiveDecl kn _ => false
end.

Definition pocc_program p := pocc_term 2000 (snd p) || List.existsb pocc_global_decl (fst p).

End occ_term_Sec.

Eval vm_compute in (eq_refl : pocc_program "Coq.Arith.PeanoNat.Nat.pred" p_Plus1 = false).
Eval vm_compute in (eq_refl : bound_program "Coq.Arith.PeanoNat.Nat.pred" p_Plus1 = false).

Eval vm_compute in (eq_refl : pocc_program "Coq.Init.Nat.pred" p_Plus1 = true).
Eval vm_compute in (eq_refl : bound_program "Coq.Init.Nat.pred" p_Plus1 = true).
