
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
Require Import Template.Template.
Require Import Template.Ast.

Unset Template Cast Propositions.
Unset Template Cast Types.

(* Use template-coq to make a [program] from function defined above *)
Time Quote Recursively Definition p_Plus1 := Plus1.

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
            orb (map (fun x => pocc_term n (dtype _ x) || pocc_term n (dbody _ x)) ds) false
        | _ => false
      end
  end.
  (** does [tConst str] occur anywhere in a program? **)
Fixpoint pocc_program (p:program): bool :=
  match p with
    | PConstr _ _ ty t q => pocc_term 2000 ty || pocc_term 2000 t || pocc_program q
    | PType _ _ _ _ q =>  pocc_program q
    | PAxiom _ _ t q => pocc_term 2000 t || pocc_program q
    | PIn t =>  pocc_term 2000 t
  end.
  (** is [str] in a program's environment? **)
Fixpoint bound_program (p:program): bool :=
  match p with
    | PConstr nm _ _ _ q
    | PType nm _ _ _ q
    | PAxiom nm _ _ q =>
      (if string_dec str nm then true else false) || bound_program q
    | PIn _ =>  false
  end.
End occ_term_Sec.

Eval vm_compute in pocc_program "Coq.Arith.PeanoNat.Nat.pred" p_Plus1.
Eval vm_compute in bound_program "Coq.Arith.PeanoNat.Nat.pred" p_Plus1.

Eval vm_compute in pocc_program "Coq.Init.Nat.pred" p_Plus1.
Eval vm_compute in bound_program "Coq.Init.Nat.pred" p_Plus1.
