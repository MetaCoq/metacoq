(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template Require Import config utils Universes BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICReflect
                          PCUICLiftSubst PCUICUnivSubst PCUICTyping.

Fixpoint eqb_term_upto_univ (equ : universe -> universe -> bool) (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ equ) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    equ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ equ u u' &&
    eqb_term_upto_univ equ v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tLambda na A t, tLambda na' A' t' =>
    eqb_term_upto_univ equ A A' &&
    eqb_term_upto_univ equ t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_term_upto_univ equ A A' &&
    eqb_term_upto_univ equ B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_term_upto_univ equ B B' &&
    eqb_term_upto_univ equ b b' &&
    eqb_term_upto_univ equ u u'

  | tCase (ind, par) p c brs, tCase (ind', par') p' c' brs' =>
    eqb_term_upto_univ equ p p' &&
    eqb_term_upto_univ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      eqb_term_upto_univ equ (snd x) (snd y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ equ c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | _, _ => false
  end.

(* Definition eqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

(* Definition leqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

Conjecture reflect_eq_term_upto_univ :
  forall equ R,
    (forall u u', reflect (R u u') (equ u u')) ->
    forall t t', reflect (eq_term_upto_univ R t t') (eqb_term_upto_univ equ t t').