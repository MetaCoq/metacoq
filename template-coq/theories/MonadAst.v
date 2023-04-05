(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils monad_utils.
From MetaCoq.Template Require Import Ast.

Import MCMonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_monad.
  Context {T} {M : Monad T}.

  Section map_predicate.
    Context {term term' : Type}.
    Context (uf : Instance.t -> T Instance.t).
    Context (paramf preturnf : term -> T term').

    Definition monad_map_predicate (p : predicate term) :=
      pparams <- monad_map paramf p.(pparams);;
      puinst <- uf p.(puinst);;
      preturn <- preturnf p.(preturn);;
      ret {| pparams := pparams;
            puinst := puinst;
            pcontext := p.(pcontext);
            preturn := preturn |}.
  End map_predicate.

  Section map_predicate_k.
    Context {term : Type}.
    Context (uf : Instance.t -> T Instance.t).
    Context (f : nat -> term -> T term).

    Definition monad_map_predicate_k k (p : predicate term) :=
      pparams <- monad_map (f k) p.(pparams);;
      puinst <- uf p.(puinst);;
      preturn <- f (#|p.(pcontext)| + k) p.(preturn);;
      ret {| pparams := pparams;
            puinst := puinst;
            pcontext := p.(pcontext);
            preturn := preturn |}.

  End map_predicate_k.

  Section map_branch.
    Context {term term' : Type}.
    Context (bbodyf : term -> T term').

    Definition monad_map_branch (b : branch term) :=
      bbody <- bbodyf b.(bbody);;
      ret {| bcontext := b.(bcontext);
            bbody := bbody |}.
  End map_branch.

  Definition monad_map_branches {term B} (f : term -> T B) l := monad_map (monad_map_branch f) l.

  Notation map_branches_k f k brs :=
    (monad_map (fun b => monad_map_branch (f (#|b.(bcontext)| + k)) b) brs).
End with_monad.
