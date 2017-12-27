(* -*- coq-prog-args : ("-type-in-type") -*-  *)
Require Import Template.Template Template.Ast Template.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import  Template.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


(* Definition syntax_ind (T : Type) *)
(*   := forall P : Type -> Type, P unit *)
(*           -> (forall A (B : A -> Type), P A -> (forall x, P (B x)) -> P (forall x, B x)) *)
(*           -> (forall A B, P A -> (forall x, P (B x)) -> P (sigma A B)) *)
(*           -> P Type *)
(*           -> P T. *)
(* Open Scope sigma_scope. *)
(* Definition TYPE := {A : Type & syntax_ind A}. *)
(* Definition Typeᵗ : TYPE. *)
(*   simple refine (_ ; _). exact TYPE. *)
(*   intros P Punit Pforall Psigma PType. *)
(*   eapply Psigma. assumption. *)
(*   intro T. eapply Pforall. eauto. *)
(*   intro P'. eapply Pforall. admit. *)
(*   intro P'unit. eapply Pforall. *)
(*   eapply Pforall. assumption. *)
(*   intro A. eapply Pforall. eapply Pforall. *)
(*   eauto.  *)
(*   cbn.  *)



(* Polymorphic Definition P : Type -> Type *)
(*   := fun _ => bool. *)
(* . Admitted. *)

(* Notation "'PP'" := (fun _ => (bool : Type)). *)
(* Definition P_type : P (sigma Type P) *)
(*   := true. *)
(* (* . Admitted. *) *)
(* Definition P_prod : forall A B, P A -> (forall x : A, P (B x)) -> P (forall x, B x) *)
(*   := fun _ _ _ _ => true. *)
(* (* . Admitted. *) *)

(* (* Quote Definition tP := Eval compute in P. *) *)
(* Quote Definition tP_type := Eval compute in P_type. *)
(* Quote Definition tP_typeT := Eval compute in (P Type). *)
(* Quote Definition tP_prod := Eval compute in P_prod. *)

Quote Definition tTYPE :=
  (* Eval compute in *)
  (@mk_sig _ (fun _ => bool) Type true).
Quote Definition j := (fun _ : bool => (bool)).
(* Make Definition jj := (tLambda nAnon (tInd (mkInd "Coq.Init.Datatypes.bool" 0)) *)
(*   (tCast (tInd (mkInd "Coq.Init.Datatypes.bool" 0)) Cast *)
(*      (tSort (sType BinNums.xH)))). *)
Make Definition kk := ltac:(let t:= eval compute in j in exact t).
(* Make Definition d''_from_syntax := ltac:(let t:= eval compute in tTYPE in exact t). *)
(* Make Definition ii := (tLambda (nNamed "x") (tSort (sType BinNums.xH)) *)
(*                                (tInd (mkInd "Coq.Init.Datatypes.bool" 0))). *)
(*   ltac:(let t:= eval compute in tTYPE in exact t). *)

Quote Definition tType := Type.

(* Quote Definition (sigma Type P) *)

(* Definition t : sigma Type P. *)
(*   let t := eval compute in (proj1 tTYPE) in *)
(*   let k x := refine x in *)
(*   denote_term t k. *)


(* Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel} *)
(*   : tsl_result term := *)
(*   match fuel with *)
(*   | O => raise NotEnoughFuel *)
(*   | S fuel => *)
(*   match t with *)
(*   | tRel  n => ret (tRel n) *)
(*   | tSort s => ret tTYPE *)
(*   | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                   A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   ret (tCast t' c A') *)
(*   | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;; *)
(*                   let A'1 := proj1 A' in *)
(*                   ret (pair tType (tLambda n tType tBool) *)
(*                             (tProd n A'1 (proj1 B')) *)
(*                             (tApp tP_prod [A'1; tLambda n A'1 (proj1 B'); proj2 A'; tLambda n A'1 (proj2 B')])) *)
(*   | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                     t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;; *)
(*                     ret (tLambda n (proj1 A') t') *)
(*   | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                      A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                      u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;; *)
(*                      ret (tLetIn n t' (proj1 A') u') *)
(*   (* | tApp (tInd i) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;; *) *)
(*   (*                     ret (tApp (tInd i) u') *) *)
(*   (* | tApp (tConstruct i n) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;; *) *)
(*   (*                             ret (tApp (tConstruct i n) u') *) *)
(*   | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                u' <- monad_map (tsl_rec fuel Σ E Γ) u ;; *)
(*                ret (tApp t' u') *)
(*   | tConst s *)
(*   | tInd (mkInd s _) => match lookup_tsl_ctx E s with *)
(*                        | Some t => ret (tConst t) *)
(*                        | None => raise (TranslationNotFound s) *)
(*                        end *)
(*   (* | tConstruct _ _ as t => ret t *) *)
(*   (* | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;; *) *)
(*   (*               ret (tProj p t) *) *)
(*   | _ => raise TranslationNotHandeled *)
(*   end end. *)

(* Definition tsl := fun Σ E => tsl_rec 1000 Σ E []. *)
(* Definition tsl_type := fun Σ E t => t' <- tsl_rec 1000 Σ E [] t ;; ret (proj1 t). *)
