Require Import Template.Template Template.Ast Translations.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import  Translations.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


Reserved Notation "'tsl_ty'".


(* if b it is the first translation, else the second *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (b : bool) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj b (tRel n))
  | tSort s => if b then ret (tSort s)
              else ret (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s)))
  | tCast t c A => if b then
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    A1 <- tsl_rec fuel Σ E Γ true A ;;
                    ret (tCast t1 c A1)
                  else
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    t2 <- tsl_rec fuel Σ E Γ false t ;;
                    A2 <- tsl_rec fuel Σ E Γ false A ;;
                    ret (tCast t2 c (tApp A2 [t1]))
  | tProd n A B => if b then
                    A' <- tsl_ty fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    ret (tProd n A' B1)
                  else
                    A' <- tsl_ty fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    B2 <- tsl_rec fuel Σ E (Γ ,, vass n A) false B ;;
                    ret (tLambda (nNamed "f") (tProd n A' B1)
                                 (tProd n (lift 1 0 A')
                                        (tApp (lift 1 1 B2)
                                              [tApp (tRel 1) [tRel 0]])))
  | tLambda n A t => A' <- tsl_ty fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) b t ;;
                    ret (tLambda n A' t')
  | tLetIn n t A u => t' <- tsl_term fuel Σ E Γ t ;;
                     A' <- tsl_ty fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) b u ;;
                     ret (tLetIn n t' A' u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ b t ;;
               u' <- monad_map (tsl_term fuel Σ E Γ) u ;;
               ret (tApp t' u')
  | tConst _ as t
  | tInd _ as t
  | tConstruct _ _ as t => t' <- tsl_term fuel Σ E Γ t ;;
                          ret (proj b t')
  | _ => raise TranslationNotHandeled
  end
  end
with tsl_term  (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)
  | tCast t c A => t' <- tsl_term fuel Σ E Γ t ;;
                  A' <- tsl_ty fuel Σ E Γ A ;;
                  ret (tCast t' c A')
  | tConst s => match lookup_tsl_ctx E (ConstRef s) with
               | Some t => ret t
               | None => raise (TranslationNotFound s)
               end
  | tInd i =>
    match lookup_tsl_ctx E (IndRef i) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (IndRef i)))
    end
  | tConstruct i n =>
    match lookup_tsl_ctx E (ConstructRef i n) with
    | Some decl => raise TranslationNotHandeled
    | None => raise (TranslationNotFound (string_of_gref (ConstructRef i n)))
    end
  | t => match infer Σ Γ t with
        | Checked typ => t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        typ1 <- tsl_rec fuel Σ E Γ true typ ;;
                        typ2 <- tsl_rec fuel Σ E Γ false typ ;;
                        ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty'" := (fun fuel Σ E Γ t =>
                        t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        ret (pack t1 t2)).


(* Fixpoint tsl_rec (Σ : global_context) (E : tsl_context) (Γ : context) (b : bool) (t : term) {struct t} *)
(*   : tsl_result term := *)
(*   match t with *)
(*   | tRel n => ret (proj b (tRel n)) *)
(*   | tSort s => if b then ret (tSort s) *)
(*               else ret (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))) *)
(*   | tCast t c A => if b then *)
(*                     t1 <- tsl_rec Σ E Γ true t ;; *)
(*                     A1 <- tsl_rec Σ E Γ true A ;; *)
(*                     ret (tCast t1 c A1) *)
(*                   else *)
(*                     t1 <- tsl_rec Σ E Γ true t ;; *)
(*                     t2 <- tsl_rec Σ E Γ false t ;; *)
(*                     A2 <- tsl_rec Σ E Γ false A ;; *)
(*                     ret (tCast t2 c (tApp A2 [t1])) *)
(*   | tProd n A B => if b then *)
(*                     A' <- tsl_typ Σ E Γ A ;; *)
(*                     B1 <- tsl_rec Σ E (Γ ,, vass n A') true B ;; *)
(*                     ret (tProd n A' B1) *)
(*                   else *)
(*                     A' <- tsl_typ Σ E Γ A ;; *)
(*                     B1 <- tsl_rec Σ E (Γ ,, vass n A') true B ;; *)
(*                     B2 <- tsl_rec Σ E (Γ ,, vass n A') false B ;; *)
(*                     ret (tLambda (nNamed "f") (tProd n A' B1) *)
(*                                  (tProd n (lift 1 0 A') *)
(*                                         (tApp (lift 1 1 B2) *)
(*                                               [tApp (tRel 1) [tRel 0]]))) *)
(*   | tLambda n A t => A' <- tsl_typ Σ E Γ A ;; *)
(*                     t' <- tsl_rec Σ E (Γ ,, vass n A') b t ;; *)
(*                     ret (tLambda n A' t') *)
(*   | tLetIn n t A u => t' <- tsl_term Σ E Γ t ;; *)
(*                      A' <- tsl_typ Σ E Γ A ;; *)
(*                      u' <- tsl_rec Σ E (Γ ,, vdef n t' A') b u ;; *)
(*                      ret (tLetIn n t' A' u') *)
(*   | tApp t u => t' <- tsl_rec Σ E Γ b t ;; *)
(*                u' <- monad_map (tsl_term Σ E Γ) u ;; *)
(*                ret (tApp t' u') *)
(*   | tConst _ as t *)
(*   | tInd _ as t *)
(*   | tConstruct _ _ as t => t' <- tsl_term Σ E Γ t ;; *)
(*                           ret (proj b t') *)
(*   | _ => raise TranslationNotHandeled *)
(*   end *)
(* with tsl_term (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct t} *)
(*   : tsl_result term := *)
(*   match t with *)
(*   | tRel n => ret (tRel n) *)
(*   | tCast t c A => t' <- tsl_term Σ E Γ t ;; *)
(*                   A' <- tsl_typ Σ E Γ A ;; *)
(*                   ret (tCast t' c A') *)
(*   | tConst s *)
(*   | tInd (mkInd s _) => match lookup_tsl_ctx E s with *)
(*                        | Some t => ret (tConst t) *)
(*                        | None => raise (TranslationNotFound s) *)
(*                        end *)
(*   | tConstruct (mkInd s _) n => match lookup_env Σ s with *)
(*                                | Some decl => raise TranslationNotHandeled *)
(*                                | None => raise (TranslationNotFound s) *)
(*                                end *)
(*   | t => t1 <- tsl_rec Σ E Γ true t ;; *)
(*         t2 <- tsl_rec Σ E Γ false t ;; *)
(*         typ1 <- match infer Σ Γ t1 with *)
(*                | Checked typ => ret typ *)
(*                | _ => raise TypingError *)
(*                end ;; *)
(*         typ2 <- match infer Σ Γ t2 with *)
(*                | Checked typ => ret typ *)
(*                | _ => raise TypingError *)
(*                end ;; *)
(*         ret (pair typ1 typ2 t1 t2) *)
(*   end *)
(* where "'tsl_typ'" := (fun Σ E Γ t => *)
(*                         t1 <- tsl_rec Σ E Γ true t ;; *)
(*                         t2 <- tsl_rec Σ E Γ false t ;; *)
(*                         ret (pack t1 t2)). *)



Instance tsl_param_instance_term : Translation
  := {| tsl_tm := fun Σ E => tsl_term fuel Σ E [] |}.

Instance tsl_param_instance_type : TranslationType
  := {| tsl_typ := fun Σ E => tsl_ty fuel Σ E [] |}.