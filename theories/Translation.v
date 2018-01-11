From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst Typing ITyping XTyping.

(* We'll see later if we really need weakening, uniqueness and inversion of
   typing.
 *)

Section Translation.

(* Transport in the target *)
(* We want transport to be a symbolic construction, do we need to be able to
   match on it? If so, we'll need to change the target syntax as well... *)
Context (transport : sort -> term -> term -> term -> term -> term).
Context (tEq : sort -> term -> term -> term -> term).
Context (type_transport :
  forall Σ Γ s T1 T2 p t ,
    Σ ;;; Γ |-- p : tEq (succ_sort s) (tSort s) T1 T2 ->
    Σ ;;; Γ |-- t : T1 ->
    Σ ;;; Γ |-- transport s T1 T2 p t : T2
).

(*! Relation for translated expressions *)
Inductive trel (E : list (nat * nat)) : term -> term -> Prop :=
| trel_assumption x y :
    In (x,y) E ->
    trel E (tRel x) (tRel y)

| trel_Rel x :
    trel E (tRel x) (tRel x)

| trel_transportl t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E (transport s T1 T2 p t1) t2

| trel_transportr t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E t1 (transport s T1 T2 p t2)

(* It seems I was mistaken. The target does need annotations. *)
.

End Translation.