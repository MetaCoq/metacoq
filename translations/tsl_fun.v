Require Import Template.Template Template.Ast Translations.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import  Translations.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel}
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
  | tApp (tInd i) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                      ret (tApp (tInd i) u')
  | tApp (tConstruct i n) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                              ret (tApp (tConstruct i n) u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;;
               u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
               ret (tApp (proj1 t') u')
  | tConst s => match lookup_tsl_ctx E (ConstRef s) with
               | Some t => ret t
               | None => raise (TranslationNotFound s)
               end
  | tInd _ as t
  | tConstruct _ _ as t => ret t
  | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;;
                ret (tProj p t)
  | _ => raise TranslationNotHandeled (* var evar meta case fix cofix *)
  end end.

Instance tsl_fun_instance_term : Translation
  := {| tsl_tm := fun Σ E => tsl_rec fuel Σ E [] |}.

Instance tsl_fun_instance_type : TranslationType
  := {| tsl_typ := fun Σ E => tsl_rec fuel Σ E [] |}.


(* Definition tsl := fun Σ E => tsl_rec fuel Σ E []. *)
(* Definition tsl_type := tsl. *)


(* Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) (cst : option ident) {struct fuel} *)
(*   : tsl_result term := *)
(*   match fuel with *)
(*   | O => raise NotEnoughFuel *)
(*   | S fuel => *)
(*   match t with *)
(*   | tRel  n => ret (tRel n) *)
(*   | tSort s => ret (tSort s) *)
(*   | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                   A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   ret (tCast t' c A') *)
(*   | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;; *)
(*                   ret (timesBool (tProd n A' B')) *)
(*   | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                     t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;; *)
(*                     match infer Σ (Γ ,, vass n A) t with *)
(*                     | Checked B => *)
(*                       B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;  *)
(*                       ret (pairTrue (tProd n A' B') (tLambda n A' t')) *)
(*                     | TypeError _ => raise TypingError *)
(*                     end *)
(*   | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                      A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                      u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;; *)
(*                      ret (tLetIn n t' A' u') *)
(*   | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                u' <- monad_map (tsl_rec fuel Σ E Γ) u ;; *)
(*                ret (tApp (proj1 t') u') *)
(*   | tConst s as t *)
(*   | tInd (mkInd s _) as t => if ... then ret t *)
(*                             else match lookup_tsl_ctx E s with *)
(*                                  | Some t => ret (tConst t) *)
(*                                  | None => raise (TranslationNotFound s) *)
(*                                  end *)
(*   | tConstruct _ _ as t => ret t *)
                              
(*   | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                 ret (tProj p t) *)
(*   | _ => raise TranslationNotHandeled *)
(*   end end. *)

(* Definition tsl := fun Σ E => tsl_rec 1000 Σ E []. *)
(* Definition tsl_type := fun Σ E => tsl_rec 1000 Σ E []. *)

(* Definition tsl_inductive_decl (Σ : global_context) (E : tsl_context) *)
(*            (id : ident) (m : minductive_decl) *)
(*   : tsl_result (global_context * tsl_context). *)
(*   simple refine (let id' := id ++ "ᵗ" in *)
(*                  let t := fun ΣE I => *)
(*                             let typ := I.(ind_type) in *)
(*                             typ' <- tsl_type Σ E typ ;; (* include ΣE ? *) *)
(*                             let I' := _ in *)
(*                             let ctors' := _ in *)
(*                             let projs' := _ in *)
(*                             ret (projs' ++ ctors' ++ I' :: (fst ΣE), *)
(*                                  (id, id') :: (snd ΣE))%list *)
(*                  in *)
(*                    monad_fold_left t m.(ind_bodies) ([], []) *)
(*                 ). *)

(* Quote Recursively Definition yy := Vector.t . *)


(* Quote Definition tBool := bool. *)
(* Quote Definition tTimes := prod'. *)
(* Definition timesBool (t : term) : term *)
(*   := tApp tTimes [ t ; tBool ]. *)
(* Quote Definition t:= true. *)
(* Quote Definition tPair := pair'. *)
(* Definition pair(A t : term) : term *)
(*   := tApp tPair [ A ; tBool ; t ; tTrue]. *)
(* (* Test Quote ((pair' _ _ 4).(snd')). *) *)
(* (* Make Definition x := (tProj (mkInd "Top.prod'" 0, 2, 1) *) *)
(* (*    (tApp (tConstruct (mkInd "Top.prod'" 0) 0) *) *)
(* (*       [tInd (mkInd "Coq.Init.Datatypes.bool" 0); *) *)
(* (*       tInd (mkInd "Coq.Init.Datatypes.nat" 0); *) *)
(* (*       tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0; *) *)
(* (*       tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*         [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*            [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*               [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*                  [tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0]]]]])). *) *)
(* (* Test Quote (snd' (pair' _ _ 4)). *) *)
(* Definition fstProj (t : term) : term *)
(*   := tProj (mkInd "Template.trad.prod'" 0, 2, 0) t. *)


(* Fixpoint tsl_rec fuel (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct t} *)
(*   : term := *)
(*   match t with *)
(*   (* | tRel       : nat -> term *) *)
(*   | tRel n => tRel n *)
(*   (* | tVar       : ident -> term (** For free variables (e.g. in a goal) *) *) *)
(*   | tVar v => tVar v *)
(*   (* | tMeta      : nat -> term   (** NOTE: this can go away *) *) *)
(*   | tMeta n => tMeta n *)
(*   (* | tEvar      : nat -> list term -> term *) *)
(*   | tEvar n l => tEvar n (List.map (tsl_rec fuel Σ E Γ) l) *)
(*   (* | tSort      : sort -> term *) *)
(*   | tSort s => tSort s *)
(*   (* | tCast      : term -> cast_kind -> term -> term *) *)
(*   | tCast t c A => tCast (tsl_rec fuel Σ E Γ t) c (tsl_rec fuel Σ E Γ A) *)
(*   (* | tProd      : name -> term (** the type **) -> term -> term *) *)
(*   | tProd n A B => let A' := tsl_rec fuel Σ E Γ A in timesBool (tProd n A' (tsl_rec fuel Σ E (Γ ,, vass n A') B)) *)
(*   (* | tLambda    : name -> term (** the type **) -> term -> term *) *)
(*   | tLambda n A t => let A' := tsl_rec fuel Σ E Γ A in *)
(*                     let t' := tLambda n A' (tsl_rec fuel Σ E (Γ ,, vass n A') t) in *)
(*                     match infer Σ Γ t' with *)
(*                     | Checked A' => pairA' t' *)
(*                     | _ => (* FIXME *) tBool *)
(*                     end *)
(*     (* t' *) *)
(*   (* | tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term *) *)
(*   | tLetIn n t A u => let t' := tsl_rec fuel Σ E Γ t in *)
(*                      let A' := tsl_rec fuel Σ E Γ A in *)
(*                      tLetIn n t' A' (tsl_rec fuel Σ E (Γ ,, vdef n t' A') u) *)
(*   (* | tApp       : term -> list term -> term *) *)
(*   | tApp (tInd i) u => tApp (tInd i) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   | tApp (tConstruct i n) u => tApp (tConstruct i n) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   | tApp t u => tApp (fstProj (tsl_rec fuel Σ E Γ t)) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   (* | tConst     : string -> term *) *)
(*   | tConst s => match lookup_tsl_ctx E s with *)
(*                | Some t => tConst t *)
(*                | None => (* FIXME *) tBool *)
(*                end *)
(*   (* | tInd       : inductive -> term *) *)
(*   | tInd i => tInd (tsl_inductive i) *)
(*   (* | tConstruct : inductive -> nat -> term *) *)
(*   | tConstruct i n => tConstruct (tsl_inductive i) n *)
(*   (* | tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **) -> term -> *) *)
(*   (*                list (nat * term) -> term *) *)
(*   | tCase (i , n) t u l => tCase (tsl_inductive i , n) (tsl_rec fuel Σ E Γ t) (tsl_rec fuel Σ E Γ u) (List.map (fun nt => (fst nt , tsl_rec fuel Σ E Γ (snd nt))) l) *)
(*   (* | tProj      : projection -> term -> term *) *)
(*   | tProj p t => tProj (tsl_projection p) (tsl_rec fuel Σ E Γ t) *)
(*   (* | tFix       : mfixpoint term -> nat -> term *)  (* mfixpoint = list (def term) *) *)
(*   | tFix l n => tFix (List.map (map_def (tsl_rec fuel Σ E Γ)) l) n *)
(*   (* | tCoFix     : mfixpoint term -> nat -> term. *) *)
(*   | tCoFix l n => tCoFix (List.map (map_def (tsl_rec fuel Σ E Γ)) l) n *)
(*   end. *)
