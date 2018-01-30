Require Import Template.All.
Require Import List.
Import ListNotations MonadNotation String.
Open Scope string_scope.

Axiom todo : forall {A}, A.


Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.


Definition tsl_context := (global_context * tsl_table)%type.

Definition emptyTC : tsl_context := ([], []).

Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandeled
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



Class Translation := { tsl_id : ident -> ident ;
                       tsl_tm : tsl_context -> term -> tsl_result term ;
                       tsl_ty : tsl_context -> term -> tsl_result term ;
                       tsl_ind : tsl_context -> kername -> kername -> minductive_decl
                            -> tsl_result (tsl_table * list minductive_decl)
                     }.


Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition tsl_name tsl_ident n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.



Definition tTranslate {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  kn' <- tmEval all (mp ++ "." ++ id') ;;
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _)
  | Some (IndRef (mkInd kn n)) =>
      d <- tmQuoteInductive id ;;
      d' <- tmEval lazy (tsl_ind ΣE kn kn' d) ;;
      match d' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ id)
      | Success (E, decls) =>
        monad_fold_left (fun _ e => tmMkInductive' e) decls tt ;;
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (InductiveDecl kn d :: fst ΣE, E ++ snd ΣE)%list
      end

  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ => fail_nf (id ++ "is an axiom, not a definition")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_body := t |} =>
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      match t' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ id)
      | Success t' =>
        tmMkDefinition id' t' ;;
        let decl := {| cst_universes := UContext.empty;
                       cst_type := A; cst_body := Some t |} in
        let Σ' := ConstantDecl kn decl :: (fst ΣE) in
        let E' := (ConstRef kn, tConst kn' []) :: (snd ΣE) in
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  end.



Definition tImplement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA <- tmQuote A ;;
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  match tA' with
  | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      A' <- tmUnquoteTyped Type tA' ;;
      tmLemma id' A' ;;
      tmAxiom id A ;;
      gr <- tmAbout id ;;
      match gr with
      | Some (ConstRef kn) =>
        let decl := {| cst_universes := UContext.empty;
                       cst_type := tA; cst_body := None |} in
        let Σ' := ConstantDecl kn decl :: (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      | _ => fail_nf (id ++ " was not found or is not a constant, this is a bug")
      end
  end.


(* Definition tImplementExisting (tsl_id : ident -> ident) *)
(*            (tsl_tm tsl_ty : global_context -> tsl_table -> term *)
(*                             -> tsl_result term) *)
(*            (Σ : tsl_context) (id : ident) *)
(*   : TemplateMonad (option tsl_context) := *)
(*   e <- tmQuoteConstant id true ;; *)
(*   match e with *)
(*   | ParameterEntry _ => tmPrint "Not a definition" ;; *)
(*                        tmReturn None *)
(*   | DefinitionEntry {| definition_entry_type := A; *)
(*                        definition_entry_body := t |} => *)
(*     match tsl_ty (fst Σ) (snd Σ) A with *)
(*     | Error _ => tmPrint "tsl error in type" ;; *)
(*                   tmReturn None *)
(*     | Success tA' => *)
(*       id' <- tmEval all (tsl_id id) ;; *)
(*       A' <- tmUnquoteTyped Type tA' ;; *)
(*       tmLemma id' A' ;; *)
(*       let decl := {| cst_universes := []; *)
(*                      cst_type := A; cst_body := Some t |} in *)
(*       let Σ' := ConstantDecl id decl :: (fst Σ) in *)
(*       let E' := (ConstRef id, tConst id' []) :: (snd Σ) in *)
(*       msg <- tmEval all (id ++ " has been translated as " ++ id') ;; *)
(*       tmPrint msg ;; *)
(*       tmReturn (Some (Σ', E')) *)
(*     end *)
(*   end. *)
