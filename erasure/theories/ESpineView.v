(* Distributed under the terms of the MIT license. *)
Require Import List ssreflect ssrbool.
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EReflect.
From MetaCoq.PCUIC Require Import PCUICSize.
From Equations Require Import Equations.
Set Equations Transparent.

Module TermSpineView.

Inductive t : term -> Set :=
| tBox       : t EAst.tBox
| tRel (n : nat) : t (EAst.tRel n)
| tVar (n : ident) : t (EAst.tVar n)
| tEvar (n : nat) (e : list term) : t (EAst.tEvar n e)
| tLambda n b : t (EAst.tLambda n b)
| tLetIn n b b' : t (EAst.tLetIn n b b')
| tApp (f : term) (l : list term) (napp : ~~ isApp f) (nnil : l <> nil) : t (mkApps f l)
| tConst kn : t (tConst kn)
| tConstruct i n : t (tConstruct i n)
| tCase ci p brs : t (tCase ci p brs)
| tProj p c : t (tProj p c)
| tFix mfix idx : t (tFix mfix idx)
| tCoFix mfix idx : t (tCoFix mfix idx).
Derive Signature for t.

Definition view : forall x : term, t x :=
  MkAppsInd.rec (P:=fun x => t x)
    tBox tRel tVar 
    (fun n l _ => tEvar n l) 
    (fun n t _ => tLambda n t)
    (fun n b _ t _ => tLetIn n b t)
    (fun f l napp nnil _ _ => tApp f l napp nnil)
    tConst
    tConstruct
    (fun p t pt l pl => tCase p t l)
    (fun p t pt => tProj p t)
    (fun mfix n _ => tFix mfix n)
    (fun mfix n _ => tCoFix mfix n).

Lemma view_mkApps {f v} (vi : t (mkApps f v)) : ~~ isApp f -> v <> [] -> 
  exists hf vn, vi = tApp f v hf vn.
Proof.
  intros ha hv.
  depelim vi.
  all: try (revert H; eapply DepElim.simplification_sigma1; intros H'; solve_discr).
  intros He.
  epose proof (DepElim.pr2_uip (A:=EAst.term) He). subst vi0.
  do 2 eexists; reflexivity.
Qed.
  
End TermSpineView.