From MetaCoq.Template Require Import utils config All.
From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.
Import MCMonadNotation.

Module TTP := TemplateToPCUIC.
Module PTT := PCUICToTemplate.

Definition univ := Level.Level "s".

Definition gctx : global_env_ext := 
  ({| universes := (LS.union (LevelSet.singleton Level.lzero) (LevelSet.singleton univ), ConstraintSet.empty); declarations := [] |}, Monomorphic_ctx).

Polymorphic Definition eval_castcic (tm : Ast.term)
  : TemplateMonad typed_term
  := let tm' := TTP.trans (TTP.trans_global_env (fst gctx)) tm in
    let tm'' := PTT.trans tm' in
    tmUnquote tm''.

MetaCoq Run (eval_castcic <% 1 + 2 %> >>= tmPrint).