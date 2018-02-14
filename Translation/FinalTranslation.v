(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping Quotes.

Import MonadNotation.

Module T := Typing.

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
      ret (mkJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
      T1' <- tsl_rec fuel Σ Γ T1 ;;
      T2' <- tsl_rec fuel Σ Γ T1 ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      ret (mkTransport T1' T2' p' t')
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
        ret (mkHeqToHeq A' u' v' p')
      (* That's not really the correct error but well. *)
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqRefl A a =>
      A' <- tsl_rec fuel Σ Γ A ;;
      a' <- tsl_rec fuel Σ Γ a ;;
      ret (mkHeqRefl A' a')
    | sHeqSym p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        ret (mkHeqSym A' a' B' b' p')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqTrans p q =>
      p' <- tsl_rec fuel Σ Γ p ;;
      q' <- tsl_rec fuel Σ Γ q ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        match @infer (Build_Fuel fuel) Σ Γ q' with
        | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; _ ; C' ; c' ]) =>
          ret (mkHeqTrans A' a' B' b' C' c' p' q')
        | Checked T => raise (TypingError (NotAnInductive T))
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqTransport p t =>
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Coq.Init.Logic.eq" 0) _) [ _ ; A' ; B' ]) =>
        ret (mkHeqTransport A' B' p' t')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sCongProd B1 B2 pA pB =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      match @infer (Build_Fuel fuel) Σ Γ pA' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ (Γ ,, vass nAnon (mkPack A1' A2')) pB ;;
        B1' <- tsl_rec fuel Σ (Γ ,, vass nAnon A1') B1 ;;
        B2' <- tsl_rec fuel Σ (Γ ,, vass nAnon A2') B2 ;;
        ret (mkCongProd A1' A2' B1' B2' pA' pB')
      | Checked T => raise (TypingError (NotAnInductive T))
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
        ret (mkCongLambda A1' A2' B1' B2' t1' t2' pA' pB' pt')
      | Checked T => raise (TypingError (NotAnInductive T))
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
          match @infer (Build_Fuel fuel) Σ Γ pt' with
          | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ _ ; u1' ; _ ; u2' ]) =>
            ret (mkCongApp A1' A2' B1' B2' t1' t2' u1' u2' pA' pB' pt' pu')
          | Checked T => raise (TypingError (NotAnInductive T))
          | TypeError t => raise (TypingError t)
          end
        | Checked T => raise (TypingError (NotAnInductive T))
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (TypingError (NotAnInductive T))
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
          ret (mkCongEq A1' A2' u1' v1' u2' v2' pA' pu' pv')
        | Checked T => raise (TypingError (NotAnInductive T))
        | TypeError t => raise (TypingError t)
        end
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sCongRefl pA pu =>
      pA' <- tsl_rec fuel Σ Γ pA ;;
      pu' <- tsl_rec fuel Σ Γ pu ;;
      match @infer (Build_Fuel fuel) Σ Γ pu' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A1' ; u1' ; A2' ; u2' ]) =>
        ret (mkCongRefl A1' A2' u1' u2' pA' pu')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sEqToHeq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Coq.Init.Logic.eq" 0) _) [ A' ; u' ; v' ]) =>
        ret (mkEqToHeq A' u' v' p')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqTypeEq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.heq" 0) _) [ A' ; u' ; B' ; v' ]) =>
        ret (mkHeqTypeEq A' u' B' v' p')
      | Checked T => raise (TypingError (NotAnInductive T))
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
        ret (mkProjT1 A1' A2' p')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sProjT2 p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.Pack" 0) _) [ A1' ; A2' ]) =>
        ret (mkProjT2 A1' A2' p')
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sProjTe p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match @infer (Build_Fuel fuel) Σ Γ p' with
      | Checked (tApp (tInd (mkInd "Translation.Quotes.Pack" 0) _) [ A1' ; A2' ]) =>
        ret (mkProjTe A1' A2' p')
      | Checked T => raise (TypingError (NotAnInductive T))
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

Fixpoint extract_mind_decl_from_program (id : ident) (p : program)
  : option minductive_decl
  := match p with
     | PConstr _ _ _ _ p => extract_mind_decl_from_program id p
     | PType id' n inds p => if string_dec id id' then
                              Some (Build_minductive_decl n inds)
                            else extract_mind_decl_from_program id p
     | PAxiom _ _ _ p => extract_mind_decl_from_program id p
     | PIn _ => None
     end.

Fixpoint extract_cst_decl_from_program (id : ident) (p : program)
  : option constant_decl
  := match p with
     | PConstr id' uist t1 t2 p => if string_dec id id' then
                                    Some (Build_constant_decl id uist t1 (Some t2))
                                  else extract_cst_decl_from_program id p
     | PType id' n inds p => extract_cst_decl_from_program id p
     | PAxiom _ _ _ p => extract_cst_decl_from_program id p
     | PIn _ => None
     end.

Fixpoint extract_axiom_decl_from_program (id : ident) (p : program)
  : option constant_decl
  := match p with
     | PConstr _ _ _ _ p => extract_axiom_decl_from_program id p
     | PType _ _ _ p => extract_axiom_decl_from_program id p
     | PAxiom id' ui t p => if string_dec id id' then
                             Some (Build_constant_decl id ui t None)
                           else extract_axiom_decl_from_program id p
     | PIn _ => None
     end.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Open Scope string_scope.

Definition get_idecl id prog :=
  option_get (Build_minductive_decl 0 [])
             (extract_mind_decl_from_program id prog).
Definition get_cdecl id prog :=
  option_get (Build_constant_decl "XX" [] (tRel 0) None)
             (extract_cst_decl_from_program id prog).
Definition get_adecl id prog :=
  option_get (Build_constant_decl "XX" [] (tRel 0) None)
             (extract_axiom_decl_from_program id prog).

Quote Recursively Definition eq_prog := @eq.
Definition eq_decl :=
  Eval compute in (get_idecl "Coq.Init.Logic.eq" eq_prog).

Quote Recursively Definition J_prog := J.
Definition J_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.J" J_prog).

Quote Recursively Definition Transport_prog := @transport.
Definition Transport_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.transport" Transport_prog).

Quote Recursively Definition UIP_prog := @UIP.
Definition UIP_decl :=
  Eval compute in (get_adecl "Translation.Quotes.UIP" UIP_prog).

Quote Recursively Definition funext_prog := @funext.
Definition funext_decl :=
  Eval compute in (get_adecl "Translation.Quotes.funext" funext_prog).

Quote Recursively Definition heq_prog := @heq.
Definition heq_decl :=
  Eval compute in (get_idecl "Translation.Quotes.heq" heq_prog).

Quote Recursively Definition heq_to_eq_prog := @heq_to_eq.
Definition heq_to_eq_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_to_eq" heq_to_eq_prog).

Quote Recursively Definition heq_refl_prog := @heq_refl.
Definition heq_refl_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_refl" heq_refl_prog).

Quote Recursively Definition heq_sym_prog := @heq_sym.
Definition heq_sym_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_sym" heq_sym_prog).

Quote Recursively Definition heq_trans_prog := @heq_trans.
Definition heq_trans_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_trans" heq_trans_prog).

Quote Recursively Definition heq_transport_prog := @heq_transport.
Definition heq_transport_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_transport" heq_transport_prog).

Quote Recursively Definition Pack_prog := @Pack.
Definition Pack_decl :=
  Eval compute in (get_idecl "Translation.Quotes.Pack" Pack_prog).

Quote Recursively Definition ProjT1_prog := @ProjT1.
Definition ProjT1_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.ProjT1" ProjT1_prog).

Quote Recursively Definition ProjT2_prog := @ProjT2.
Definition ProjT2_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.ProjT2" ProjT2_prog).

Quote Recursively Definition ProjTe_prog := @ProjTe.
Definition ProjTe_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.ProjTe" ProjTe_prog).

Quote Recursively Definition cong_prod_prog := @cong_prod.
Definition cong_prod_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.cong_prod" cong_prod_prog).

Quote Recursively Definition cong_lambda_prog := @cong_lambda.
Definition cong_lambda_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.cong_lambda" cong_lambda_prog).

Quote Recursively Definition cong_app_prog := @cong_app.
Definition cong_app_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.cong_app" cong_app_prog).

Quote Recursively Definition cong_eq_prog := @cong_eq.
Definition cong_eq_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.cong_eq" cong_eq_prog).

Quote Recursively Definition cong_refl_prog := @cong_refl.
Definition cong_refl_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.cong_refl" cong_refl_prog).

Quote Recursively Definition eq_to_heq_prog := @eq_to_heq.
Definition eq_to_heq_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.eq_to_heq" eq_to_heq_prog).

Quote Recursively Definition heq_type_eq_prog := @heq_type_eq.
Definition heq_type_eq_decl :=
  Eval compute in (get_cdecl "Translation.Quotes.heq_type_eq" heq_type_eq_prog).

Definition Σ : global_context :=
  [ InductiveDecl "Coq.Init.Logic.eq" eq_decl ;
    ConstantDecl "Translation.Quotes.J" J_decl ;
    ConstantDecl "Translation.Quotes.transport" Transport_decl ;
    ConstantDecl "Translation.Quotes.UIP" UIP_decl ;
    ConstantDecl "Translation.Quotes.funext" funext_decl ;
    InductiveDecl "Translation.Quotes.heq" heq_decl ;
    ConstantDecl "Translation.Quotes.heq_to_eq" heq_to_eq_decl ;
    ConstantDecl "Translation.Quotes.heq_refl" heq_refl_decl ;
    ConstantDecl "Translation.Quotes.heq_sym" heq_sym_decl ;
    ConstantDecl "Translation.Quotes.heq_trans" heq_trans_decl ;
    ConstantDecl "Translation.Quotes.heq_transport" heq_transport_decl ;
    InductiveDecl "Translation.Quotes.Pack" Pack_decl ;
    ConstantDecl "Translation.Quotes.ProjT1" ProjT1_decl ;
    ConstantDecl "Translation.Quotes.ProjT2" ProjT2_decl ;
    ConstantDecl "Translation.Quotes.ProjTe" ProjTe_decl ;
    ConstantDecl "Translation.Quotes.cong_prod" cong_prod_decl ;
    ConstantDecl "Translation.Quotes.cong_lambda" cong_lambda_decl ;
    ConstantDecl "Translation.Quotes.cong_app" cong_app_decl ;
    ConstantDecl "Translation.Quotes.cong_eq" cong_eq_decl ;
    ConstantDecl "Translation.Quotes.cong_refl" cong_refl_decl ;
    ConstantDecl "Translation.Quotes.eq_to_heq" eq_to_heq_decl ;
    ConstantDecl "Translation.Quotes.heq_type_eq" heq_type_eq_decl
  ].

(* Checking for the sake of checking *)
Compute (infer Σ [] tEq).
Compute (infer Σ [] tJ).
Compute (infer Σ [] tTransport).
Compute (infer Σ [] tUip).
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

Make Definition eq' := ltac:(let t := eval compute in tEq in exact t).
Make Definition eq_refl' := ltac:(let t := eval compute in tRefl in exact t).
Make Definition heq_refl' :=
  ltac:(
    let t := eval compute in (mkHeqRefl (tSort (succ_sort sSet)) (tSort sSet))
      in exact t
  ).
Make Definition heq_refl_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 10) Σ []
                           (sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).
Make Definition heq_sym_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 16) Σ []
                           (sHeqSym ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).
Make Definition heq_trans_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 16) Σ []
                           (sHeqTrans ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet)))
                                      ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).

Eval lazy in (tsl_rec (2 ^ 18) Σ []
                         (sHeqSym ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))))).

Quote Definition heq_g := ltac:(let t := eval compute in (fun A (x : A) B (y : B) => @heq A x B y) in exact t).


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