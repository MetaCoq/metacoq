From MetaCoq.Template Require Import TemplateMonad.Core.

(** This allow to use notations of MonadNotation *)
From MetaCoq.Template Require Import monad_utils.

Instance TemplateMonad_Monad : Monad TemplateMonad :=
{| ret := @tmReturn ; bind := @tmBind |}.
