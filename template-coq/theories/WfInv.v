(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template Require Import config utils Ast.
Require Import ssreflect.

(** * Inversion lemmas for the well-formedness judgement *)

Fixpoint wf_Inv (t : term) :=
  match t with
  | tRel _ | tVar _ | tSort _ => True
  | tEvar n l => Forall wf l
  | tCast t k t' => wf t /\ wf t'
  | tProd na t b => wf t /\ wf b
  | tLambda na t b => wf t /\ wf b
  | tLetIn na t b b' => wf t /\ wf b /\ wf b'
  | tApp t u => ~ isApp t = true /\ u <> nil /\ wf t /\ Forall wf u
  | tConst _ _ | tInd _ _ | tConstruct _ _ _ => True
  | tCase ci p c brs => wf p /\ wf c /\ Forall (Program.Basics.compose wf snd) brs
  | tProj p t => wf t
  | tFix mfix k => Forall (fun def => wf def.(dtype) /\ wf def.(dbody) /\ isLambda def.(dbody) = true) mfix
  | tCoFix mfix k => Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix
  end.

Lemma wf_inv t (w : Ast.wf t) : wf_Inv t.
Proof.
  induction w; simpl; auto.
Defined.
