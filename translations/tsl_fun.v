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

Definition recompose_prod (nas : list name) (ts : list term) (u : term)
  : term
  := let nats := List.combine nas ts in
     List.fold_right (fun t u => tProd (fst t) (snd t) u) u nats.

Definition combine' := fun {A B} l => @List.combine A B (fst l) (snd l).

Definition up := lift 1 0.

Fixpoint replace pat u t {struct t} :=
  if eq_term t pat then u else
    match t with
    | tCast t c A => tCast (replace pat u t) c (replace pat u A)
    | tProd n A B => tProd n (replace pat u A) (replace (up pat) (up u) B)
    | tLambda n A t => tLambda n (replace pat u A) (replace (up pat) (up u) t)
    | tLetIn n t A B => tLetIn n (replace pat u t) (replace pat u A) (replace (up pat) (up u) B)
    | tApp t us => tApp (replace pat u t) (List.map (replace pat u) us)
    | tProj p t => tProj p (replace pat u t)
    | _ => t (* todo *)
    end.


Definition tsl_mind_decl (E : tsl_table)
           (kn : kername) (mind : minductive_decl) : minductive_decl.
  refine (let tsl := fun Γ t => match tsl_rec fuel [] [] Γ t with
                             | Success x => x
                             | Error _ => todo
                             end in _).
  refine {| ind_npars := mind.(ind_npars); ind_bodies := _ |}.
  - refine (map_i _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* todo *)
    + (* arity *)
      refine (let L := decompose_prod ind.(ind_type) in _).
      simple refine (let L' := List.fold_left _ (combine' (fst L)) [] in _).
      exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
      refine (List.fold_left _ L' (snd L)).
      exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).
    + (* constructors *)
      refine (map_i _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (tsl_ident name, _, nargs).
      refine (replace (proj1 (tRel 0)) (tRel 0) _). (* todo mutual *)
      refine (let L := decompose_prod typ in _).
      simple refine (let L' := List.fold_left _ (combine' (fst L)) [] in _).
      exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
      refine (List.fold_left _ L' (tsl L' (snd L))).
      exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).

      (* refine (match snd L with *)
      (*         | tApp t us => tApp t (List.map (tsl L') us) *)
      (*         | t => t *)
      (*         end). *)

Defined.


Require Import Vector.

Run TemplateProgram (d <- tmQuoteInductive "eq" ;;
                     d' <- tmEval lazy (tsl_mind_decl [] "nat" d) ;;
                     tmPrint d' ;;
                     e' <- tmEval lazy (mind_decl_to_entry d') ;;
                     tmMkInductive e').


(* Definition tsl_inductive (ΣE : tsl_context) (id : ident) *)
(*            (mind : minductive_decl) *)
(*   : tsl_result (tsl_table * list minductive_decl). *)
(* Proof. *)



(*   refine (if List.forallb () minductive_decl *)
(*   refine (Success (_, [])). *)
(*   refine (List.concat (map_i _ mind.(ind_bodies))). *)
(*   intros i ind. exact [(IndRef (mkInd id i), tInd (mkInd id i) [])]. *)
(* Defined. *)

Instance tsl_fun : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ind := todo |}.


Definition T := forall A, A -> A.
Definition u : T := fun A x => x.

Open Scope sigma_scope.

Run TemplateProgram (SE <- tTranslate _ ([],[]) "T" ;;
                     tTranslate _ SE "u" >>= tmPrint).



Run TemplateProgram (tImplement _ ([],[]) "notFunext"
    ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = g x) -> f = g) -> False)
    >>= tmPrint).
Next Obligation.
  refine (fun H => _; true).
  apply π1 in H; specialize (H unit).
  apply π1 in H; specialize (H unit).
  apply π1 in H; specialize (H (fun x => x; true)).
  apply π1 in H; specialize (H (fun x => x; false)).
  apply π1 in H; specialize (H (fun x => eq_refl; true)).
  discriminate.
Defined.
