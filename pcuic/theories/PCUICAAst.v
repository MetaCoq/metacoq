(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Export monad_utils univ uGraph.
From Template Require Import BasicAst.
From PCUIC Require Import PCUICAst PCUICChecker PCUICRetyping.
Import monad_utils.MonadNotation.

(** * Annotated AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is basically a copy of PCUICAst's but this time it features
   type annotations for abstraction and application.

*)

Inductive aterm : Set :=
| aRel       : nat -> aterm
| aVar       : ident -> aterm (* For free variables (e.g. in a goal) *)
| aMeta      : nat -> aterm   (* NOTE: this will go away *)
| aEvar      : nat -> list aterm -> aterm
| aSort      : universe -> aterm
| aProd      : name -> aterm (* the type *) -> aterm -> aterm
| aLambda    : name -> aterm (* the domain *) -> (* the codomain *) aterm -> aterm -> aterm
| aLetIn     : name -> aterm (* the term *) -> aterm (* the type *) -> aterm -> aterm
| aApp       : (* the domain *) aterm -> (* the codomain *) aterm -> aterm -> aterm -> aterm
| aConst     : kername -> universe_instance -> aterm
| aInd       : inductive -> universe_instance -> aterm
| aConstruct : inductive -> nat -> universe_instance -> aterm
| aCase      : (inductive * nat) (* # of parameters *) -> aterm (* type info *)
               -> aterm (* discriminee *) -> list (nat * aterm) (* branches *) -> aterm
| aProj      : projection -> aterm -> aterm
| aFix       : mfixpoint aterm -> nat -> aterm
| aCoFix     : mfixpoint aterm -> nat -> aterm.

Fixpoint erase (t : aterm) : term :=
  match t with
  | aRel n => tRel n
  | aVar id => tVar id
  | aMeta n => tMeta n
  | aEvar n l => tEvar n (List.map erase l)
  | aSort u => tSort u
  | aProd na A B => tProd na (erase A) (erase B)
  | aLambda na A B t => tLambda na (erase A) (erase t)
  | aLetIn na t A t' => tLetIn na (erase t) (erase A) (erase t')
  | aApp A B t u => tApp (erase t) (erase u)
  | aConst id l => tConst id l
  | aInd ind l => tInd ind l
  | aConstruct ind n l => tConstruct ind n l
  | aCase indn i b brs => tCase indn (erase i) (erase b) (List.map (utils.on_snd erase) brs)
  | aProj p t => tProj p (erase t)
  | aFix f n => tFix (List.map (fun def => mkdef _ def.(dname) (erase def.(dtype)) (erase def.(dbody)) def.(rarg)) f) n
  | aCoFix f n => tCoFix (List.map (fun def => mkdef _ def.(dname) (erase def.(dtype)) (erase def.(dbody)) def.(rarg)) f) n
  end.

Fixpoint annotate F Σ Γ (t : term) {struct F} : typing_result aterm :=
  match F with 0 => raise (NotEnoughFuel 0) | S F =>
  let F' := F : utils.Fuel in
  match t with
  | tRel n => ret (aRel n)
  | tVar id => ret (aVar id)
  | tMeta n => ret (aMeta n)
  | tEvar n l =>
    l' <- monad_map (annotate F Σ Γ) l ;;
    ret (aEvar n l')
  | tSort u => ret (aSort u)
  | tProd na A B =>
    A' <- annotate F Σ Γ A ;;
    B' <- annotate F Σ (Γ ,, vass na A) B ;;
    ret (aProd na A' B')
  | tLambda na A t =>
    A' <- annotate F Σ Γ A ;;
    B <- type_of Σ (Γ ,, vass na A) t ;;
    B' <- annotate F Σ (Γ ,, vass na A) B ;;
    t' <- annotate F Σ (Γ ,, vass na A) t ;;
    ret (aLambda na A' B' t')
  | tLetIn na t A b =>
    t' <- annotate F Σ Γ t ;;
    A' <- annotate F Σ Γ A ;;
    b' <- annotate F Σ (Γ ,, vass na A) b ;;
    ret (aLetIn na t' A' b')
  | tApp t u =>
    t' <- annotate F Σ Γ t ;;
    u' <- annotate F Σ Γ u ;;
    P <- type_of Σ Γ t ;;
    p <- reduce_to_prod (fst Σ) Γ P ;;
    let '(A, B) := p in
    A' <- annotate F Σ Γ A ;;
    B' <- annotate F Σ (Γ ,, vass nAnon A) B ;;
    ret (aApp A' B' t' u')
  | tConst id l => ret (aConst id l)
  | tInd ind l => ret (aInd ind l)
  | tConstruct ind n l => ret (aConstruct ind n l)
  | tCase indn i b brs =>
    i' <- annotate F Σ Γ i ;;
    b' <- annotate F Σ Γ b ;;
    brs' <- monad_map (fun '(n,t) => t' <- annotate F Σ Γ t ;; ret (n,t')) brs ;;
    ret (aCase indn i' b' brs')
  | tProj p t =>
    t' <- annotate F Σ Γ t ;;
    ret (aProj p t')
  | tFix f n =>
    f' <- monad_map (fun def =>
      dtype <- annotate F Σ Γ def.(dtype) ;;
      dbody <- annotate F Σ Γ def.(dbody) ;;
      ret (mkdef _ def.(dname) dtype dbody def.(rarg))
    ) f ;;
    ret (aFix f' n)
  | tCoFix f n =>
    f' <- monad_map (fun def =>
      dtype <- annotate F Σ Γ def.(dtype) ;;
      dbody <- annotate F Σ Γ def.(dbody) ;;
      ret (mkdef _ def.(dname) dtype dbody def.(rarg))
    ) f ;;
    ret (aCoFix f' n)
  end
  end.