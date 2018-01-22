Require Import Template.Template Template.Ast Translations.sigma Template.monad_utils.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import  Translations.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel  n => ret (tRel n)
  | tSort s => ret (tSort s)
  | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;;
                  A' <- tsl_rec fuel Σ E Γ A ;;
                  ret (tCast t' c A')
  | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;;
                  B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                  ret (timesBool (tProd n A' B'))
  | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;;
                    match infer Σ (Γ ,, vass n A) t with
                    | Checked B =>
                      B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                      ret (pairTrue (tProd n A' B') (tLambda n A' t'))
                    | TypeError t => raise (TypingError t)
                    end
  | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;;
                     A' <- tsl_rec fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;;
                     ret (tLetIn n t' A' u')
  | tApp (tInd i univs) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                      ret (tApp (tInd i univs) u')
  | tApp (tConstruct i n univs) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                              ret (tApp (tConstruct i n univs) u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;;
               u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
               ret (tApp (proj1 t') u')
  | tConst s univs => match lookup_tsl_table E (ConstRef s) with
               | Some t => ret t
               | None => raise (TranslationNotFound s)
               end
  | tInd _ _ as t
  | tConstruct _ _ _ as t => ret t
  | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;;
                ret (tProj p t)
  | _ => raise TranslationNotHandeled (* var evar meta case fix cofix *)
  end end.

Instance tsl_fun : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ind := todo |}.


Definition T := Type -> Type.
Definition u : T := fun x => x.

Run TemplateProgram (SE <- tTranslate _ ([],[]) "T" ;;
                     tTranslate _ SE "u" >>= tmPrint).