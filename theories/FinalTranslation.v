(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon Typing
                             ITyping Checker Template.
Import MonadNotation.

(* From Simon Boulier *)
Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandled
| TypingError (t : type_error).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Open Scope t_scope.

(* We need to assert somewhere that we ask a Σ containing Σ-types, eq-types,
   UIP and funext.
   The rest will be obtained through quoting.
 *)

Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (Γ : context) (t : sterm) {struct fuel}
  : tsl_result term :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | sRel n => ret (tRel n)
    | sSort s => ret (tSort s)
    | sProd n A B =>
      A' <- tsl_rec fuel Σ Γ A ;;
      B' <- tsl_rec fuel Σ (Γ ,, vass n A') B ;;
      ret (tProd n A' B')
    | sLambda n A B t =>
      A' <- tsl_rec fuel Σ Γ A ;;
      t' <- tsl_rec fuel Σ (Γ ,, vass n A') t ;;
      ret (tLambda n A' t')
    | sApp u n A B v =>
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (tApp u' [v'])
    | sEq A u v =>
      A' <- tsl_rec fuel Σ Γ A ;;
      match infer Σ Γ A' with
      | Checked (tSort s) =>
        (* TODO, do something with Σ *)
        raise TranslationNotHandled
      | Checked T => raise (TypingError (NotASort T))
      | TypeError t => raise (TypingError t)
      end
    | sRefl A u =>
      A' <- tsl_rec fuel Σ Γ A ;;
      match infer Σ Γ A' with
      | Checked (tSort s) =>
        (* TODO, do something with Σ *)
        raise TranslationNotHandled
      | Checked T => raise (TypingError (NotASort T))
      | TypeError t => raise (TypingError t)
      end
    | _ => raise TranslationNotHandled
    end
  end.