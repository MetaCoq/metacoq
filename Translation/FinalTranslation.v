(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils monad_utils LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping Quotes.

Import MonadNotation.

Module T := Typing.

(* From Simon Boulier *)
Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandled
| TypingError (t : type_error)
| UnexpectedTranslation (msg : string) (p : sterm) (p' ty : term)
.

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

(* For now, we'll let TemplateCoq deal with universes on its own. *)
Fixpoint sort_to_universe (s : sort) : Universe.t :=
  match s with
  | 0 => (* Universe.type0 *) []
  | S n => []
  end.

Definition myret (Σ : global_context) (Γ : context) (t : term) : tsl_result term :=
  match hnf_stack (fst Σ) Γ t with
    Checked (t', _) => Success t'
  | _ => Error TranslationNotHandled end.

Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (Γ : context) (t : sterm) {struct fuel}
  : tsl_result term :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | sRel n => ret (tRel n)
    | sSort s => ret (tSort (sort_to_universe s))
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
      myret Σ Γ (tApp u' [v'])
    | sEq A u v =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (mkEq A' u' v')
    | sRefl A u =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      ret (mkRefl A' u')
    | sJ A u P w v p =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      P' <- tsl_rec fuel Σ (Γ ,, vass nAnon A' ,, vass nAnon (mkEq (LiftSubst.lift0 1 A') (LiftSubst.lift0 1 u') (tRel 0))) P ;;
      w' <- tsl_rec fuel Σ Γ w ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      myret Σ Γ (mkJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
      T1' <- tsl_rec fuel Σ Γ T1 ;;
      T2' <- tsl_rec fuel Σ Γ T2 ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      myret Σ Γ (mkTransport T1' T2' p' t')
    | sHeq A a B b =>
      A' <- tsl_rec fuel Σ Γ A ;;
      B' <- tsl_rec fuel Σ Γ B ;;
      a' <- tsl_rec fuel Σ Γ a ;;
      b' <- tsl_rec fuel Σ Γ b ;;
      ret (mkHeq A' a' B' b')
    | sHeqToEq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; u' ; _ ; v' ]) =>
        myret Σ Γ (mkHeqToHeq A' u' v' p')
      | Checked T => raise (UnexpectedTranslation "HeqToEq" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sHeqRefl A a =>
      A' <- tsl_rec fuel Σ Γ A ;;
      a' <- tsl_rec fuel Σ Γ a ;;
      myret Σ Γ (mkHeqRefl A' a')
    | sHeqSym p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        myret Σ Γ (mkHeqSym A' a' B' b' p')
      | Checked T => raise (UnexpectedTranslation "HeqSym" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sHeqTrans p q =>
      p' <- tsl_rec fuel Σ Γ p ;;
      q' <- tsl_rec fuel Σ Γ q ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        match @infer (Build_Fuel fuel) Σ Γ q' with
        | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; _ ; C' ; c' ]) =>
          myret Σ Γ (mkHeqTrans A' a' B' b' C' c' p' q')
        | Checked T => raise (UnexpectedTranslation "HeqTrans 1" q q' T)
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (UnexpectedTranslation "HeqTrans 2" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sHeqTransport p t =>
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Coq.Init.Logic.eq" 0) _) [ _ ; A' ; B' ]) =>
        myret Σ Γ (mkHeqTransport A' B' p' t')
      | Checked T => raise (UnexpectedTranslation "HeqTransport" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sCongProd B1 B2 pA pB =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      match @infer (Build_Fuel fuel) Σ Γ pA' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ (Γ ,, vass nAnon (mkPack A1' A2')) pB ;;
        B1' <- tsl_rec fuel Σ (Γ ,, vass nAnon A1') B1 ;;
        B2' <- tsl_rec fuel Σ (Γ ,, vass nAnon A2') B2 ;;
        myret Σ Γ (mkCongProd A1' A2' B1' B2' pA' pB')
      | Checked T => raise (UnexpectedTranslation "CongProd" pA pA' T)
      | TypeError t => raise (TypingError t)
      end
    | sCongLambda B1 B2 t1 t2 pA pB pt =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      match @infer (Build_Fuel fuel) Σ Γ pA' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ (Γ ,, vass nAnon (mkPack A1' A2')) pB ;;
        pt' <- tsl_rec fuel Σ (Γ ,, vass nAnon (mkPack A1' A2')) pt ;;
        B1' <- tsl_rec fuel Σ (Γ ,, vass nAnon A1') B1 ;;
        B2' <- tsl_rec fuel Σ (Γ ,, vass nAnon A2') B2 ;;
        t1' <- tsl_rec fuel Σ (Γ ,, vass nAnon A1') t1 ;;
        t2' <- tsl_rec fuel Σ (Γ ,, vass nAnon A2') t2 ;;
        myret Σ Γ (mkCongLambda A1' A2' B1' B2' t1' t2' pA' pB' pt')
      | Checked T => raise (UnexpectedTranslation "CongLambda" pA pA' T)
      | TypeError t => raise (TypingError t)
      end
    | sCongApp B1 B2 pt pA pB pu =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      match @infer (Build_Fuel fuel) Σ Γ pA' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ (Γ ,, vass nAnon (mkPack A1' A2')) pB ;;
        pt' <- tsl_rec fuel Σ Γ pt ;;
        pu' <- tsl_rec fuel Σ Γ pu ;;
        B1' <- tsl_rec fuel Σ (Γ ,, vass nAnon A1') B1 ;;
        B2' <- tsl_rec fuel Σ (Γ ,, vass nAnon A2') B2 ;;
        match @infer (Build_Fuel fuel) Σ Γ pt' with
        | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; t1' ; _ ; t2' ]) =>
          match @infer (Build_Fuel fuel) Σ Γ pu' with
          | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; u1' ; _ ; u2' ]) =>
            myret Σ Γ (mkCongApp A1' A2' B1' B2' t1' t2' u1' u2' pA' pB' pt' pu')
          | Checked T => raise (UnexpectedTranslation "CongApp 1" pu pu' T)
          | TypeError t => raise (TypingError t)
          end
        | Checked T => raise (UnexpectedTranslation "CongApp 2" pt pt' T)
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (UnexpectedTranslation "CongApp 3" pA pA' T)
      | TypeError t => raise (TypingError t)
      end
    | sCongEq pA pu pv =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      pu' <- tsl_rec fuel Σ Γ pu ;;
      pv' <- tsl_rec fuel Σ Γ pv ;;
      match @infer (Build_Fuel fuel) Σ Γ pu' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A1' ; u1' ; A2' ; u2' ]) =>
        match @infer (Build_Fuel fuel) Σ Γ pv' with
        | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; v1' ; _ ; v2' ]) =>
          myret Σ Γ (mkCongEq A1' A2' u1' v1' u2' v2' pA' pu' pv')
        | Checked T => raise (UnexpectedTranslation "CongEq 1" pv pv' T)
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (UnexpectedTranslation "CongEq 2" pu pu' T)
      | TypeError t => raise (TypingError t)
      end
    | sCongRefl pA pu =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      pu' <- tsl_rec fuel Σ Γ pu ;;
      match @infer (Build_Fuel fuel) Σ Γ pu' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A1' ; u1' ; A2' ; u2' ]) =>
        myret Σ Γ (mkCongRefl A1' A2' u1' u2' pA' pu')
      | Checked T => raise (UnexpectedTranslation "CongRefl" pu pu' T)
      | TypeError t => raise (TypingError t)
      end
    | sEqToHeq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Coq.Init.Logic.eq" 0) _) [ A' ; u' ; v' ]) =>
        myret Σ Γ (mkEqToHeq A' u' v' p')
      | Checked T => raise (UnexpectedTranslation "EqToHeq" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sHeqTypeEq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; u' ; B' ; v' ]) =>
        myret Σ Γ (mkHeqTypeEq A' u' B' v' p')
      | Checked T => raise (UnexpectedTranslation "HeqTypeEq" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sPack A1 A2 =>
      A1' <- tsl_rec fuel Σ Γ A1 ;;
      A2' <- tsl_rec fuel Σ Γ A2 ;;
      ret (mkPack A1' A2')
    | sProjT1 p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.Pack" 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjT1 A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjT1" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sProjT2 p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.Pack" 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjT2 A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjT2" p p' T)
      | TypeError t => raise (TypingError t)
      end
    | sProjTe p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.Pack" 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjTe A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjTe" p p' T)
      | TypeError t => raise (TypingError t)
      end
    end
  end.

(* Delimit Scope i_scope with i. *)

Fixpoint tsl_ctx (fuel : nat) (Σ : global_context) (Γ : scontext)
  : tsl_result context :=
  match Γ with
  | [] => ret []
  | a :: Γ =>
    Γ' <- tsl_ctx fuel Σ Γ ;;
    A' <- tsl_rec fuel Σ Γ' (sdecl_type a) ;;
    ret (Γ' ,, vass (sdecl_name a) A')
  end.

(* We define a term that mentions everything that the global context should
   have. *)
Definition glob_term :=
  let _ := @eq in
  let _ := @transport in
  let _ := @K in
  let _ := @funext in
  let _ := @heq in
  let _ := @heq_to_eq in
  let _ := @heq_refl in
  let _ := @heq_sym in
  let _ := @heq_trans in
  let _ := @heq_transport in
  let _ := @Pack in
  let _ := @ProjT1 in
  let _ := @ProjT2 in
  let _ := @ProjTe in
  let _ := @cong_prod in
  let _ := @cong_app in
  let _ := @cong_lambda in
  let _ := @cong_eq in
  let _ := @cong_refl in
  let _ := @eq_to_heq in
  let _ := @heq_type_eq in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context := (fst glob_prog, init_graph).

(* Checking for the sake of checking *)
Compute (infer Σ [] tEq).
Compute (infer Σ [] tJ).
Compute (infer Σ [] tTransport).
Compute (infer Σ [] tK).
Compute (infer Σ [] tFunext).
Compute (infer Σ [] tHeq).
Compute (infer Σ [] tHeqToEq).
Compute (infer Σ [] tHeqRefl).
Compute (infer Σ [] tHeqSym).
Compute (infer Σ [] tHeqTrans).
Compute (infer Σ [] tHeqTransport).
Compute (infer Σ [] tPack).
Compute (infer Σ [] tProjT1).
Compute (infer Σ [] tProjT2).
Compute (infer Σ [] tProjTe).
Compute (infer Σ [] tCongProd).
Compute (infer Σ [] tCongLambda).
Compute (infer Σ [] tCongApp).
Compute (infer Σ [] tCongEq).
Compute (infer Σ [] tCongRefl).
Compute (infer Σ [] tEqToHeq).
Compute (infer Σ [] tHeqTypeEq).

(* Theorem soundness : *)
(*   forall {Γ t A}, *)
(*     Σ ;;; Γ |-i t : A -> *)
(*     forall {fuel Γ' t' A'}, *)
(*       tsl_ctx fuel Σ Γ = Success Γ' -> *)
(*       tsl_rec fuel Σ Γ' t = Success t' -> *)
(*       tsl_rec fuel Σ Γ' A = Success A' -> *)
(*       Σ ;;; Γ' |-- t' : A'. *)
(* Proof. *)
(*   intros Γ t A h. *)
(*   dependent induction h ; intros fuel Γ' t' A' hΓ ht hA. *)
(*   all: destruct fuel ; try discriminate. *)

(*   - cbn in ht. inversion_clear ht. *)
(*     admit. *)

(*   - cbn in ht, hA. inversion_clear ht. inversion_clear hA. *)
(*     apply T.type_Sort. *)

(*   - cbn in hA. inversion_clear hA. *)
(*     simpl in ht. inversion ht. *)
(*     admit. *)

(*   - admit. *)

(*   - admit. *)

(*   - cbn in hA. inversion_clear hA. *)
(*     cbn in ht. *)
(*     destruct (tsl_rec fuel Σ Γ' A) ; destruct (tsl_rec fuel Σ Γ' u) ; try (now inversion ht). *)
(*     destruct (tsl_rec fuel Σ Γ' v) ; inversion_clear ht. *)
(*     eapply T.type_App. *)
(*     + econstructor. econstructor. split. *)
(*       * econstructor. *)
(*       * cbn. f_equal. *)
(*     + econstructor. *)
(* Abort. *)