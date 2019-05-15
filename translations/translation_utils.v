From Template Require Import All TemplateMonad.Extractable Monad monad_utils.
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

Definition emptyTC : tsl_context := (([], ConstraintSet.empty), []).

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

Global Instance tsl_monad : Monad tsl_result :=
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

Definition lookup_tsl_table' E gr :=
  match lookup_tsl_table E gr with
  | Some t => ret t
  | None => raise (TranslationNotFound (string_of_gref gr))
  end.




Class Translation :=
  { tsl_id : ident -> ident ;
    tsl_tm : tsl_context -> term -> tsl_result term ;
    tsl_ty : option (tsl_context -> term -> tsl_result term) ;

    (* string = ModPath in which the inductive will be declared *)
    tsl_ind : tsl_context -> string -> kername -> mutual_inductive_body
              -> tsl_result (tsl_table * list mutual_inductive_body) }.


Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition tsl_name tsl_ident n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.


Definition tmDebug {A} : A -> TM unit :=
  fun _ => tmReturn tt.

Global Instance Monad_TM : Monad TM :=
{ ret := @tmReturn
; bind := @tmBind }.

Definition Translate {tsl : Translation} (ΣE : tsl_context) (id : ident)
: TM tsl_context :=
  tmMsg ("Translate " ++ id);;
  gr <- tmAbout id ;;
  tmDebug gr;;
  match gr return TM _ with
  | None => tmFail (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _)
  | Some (IndRef (mkInd kn n)) =>
    mp <- tmCurrentModPath ;;
    d <- tmQuoteInductive id ;;
    match tsl_ind ΣE mp kn d with
    | Error e =>
(*      print_nf e ;; *)
      tmFail ("Translation error during the translation of the inductive " ++ id)
    | Success (E, decls) =>
      monad_iter tmInductive (List.map mind_body_to_entry decls) ;;
      let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
      let E' := (E ++ (snd ΣE))%list in
      tmMsg (kn ++ " has been translated.") ;;
      tmReturn (Σ', E')
    end
  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ =>
      tmFail (id ++ " is an axiom, not a definition. Use Implement Existing.")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_universes := univs;
                         definition_entry_body := t |} =>
      tmDebug t ;;
      match tsl_tm ΣE t with
      | Error e =>
        tmFail ("Translation error during the translation of the body of " ++ id)
      | Success t' =>
        let id' := tsl_id id in
        tmDefinition id' None t' ;;
        let decl := {| cst_universes := univs;
                       cst_type := A; cst_body := Some t |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        (*Σ' <- tmEval lazy Σ' ;;
        E' <- tmEval lazy E' ;; *)
        tmMsg (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  end.


Definition Implement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (tA : Ast.term)
: TM (tsl_context) :=
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty =>
    match tsl_ty ΣE tA with
    | Error e =>
      tmFail "Translation error during the translation of the type."
    | Success tA' =>
      let id' := tsl_id id in
      tmLemma id' tA' ;;
      id_kn <- tmAxiom id tA ;;
      gr <- tmAbout id_kn ;;
      match gr return TM _ with
      | Some (ConstRef kn) =>
        let decl := {| cst_universes := Monomorphic_ctx UContext.empty;
                       cst_type := tA; cst_body := None |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        tmMsg (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      | _ => tmFail (id ++ " was not found or is not a constant. This is a bug.")
      end
    end
  end.

Definition body_constant_entry (e : constant_entry) : option term :=
  match e with
  | ParameterEntry _ => None
  | DefinitionEntry {| definition_entry_body := t |} => Some t
  end.


Definition ImplementExisting {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TM tsl_context :=
  gr <- tmAbout id ;;
  let id' := tsl_id id in
  mp <- tmCurrentModPath ;;
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty =>
  match gr with
  | None => tmFail (id ++ " not found")
  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry  {| parameter_entry_type := A  |}
    | DefinitionEntry {| definition_entry_type := A |} =>
      let tA' := tsl_ty ΣE A in
      match tA' with
      | Error e =>
        tmFail ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
        tmLemma id' tA' ;;
        let decl := {| cst_universes := Monomorphic_ctx UContext.empty;
                       cst_type := A; cst_body := body_constant_entry e |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        tmMsg (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  | Some (IndRef (mkInd kn n)) =>
    d <- tmQuoteInductive kn ;;
    match List.nth_error (ind_bodies d) n with
      | None => tmFail ("The declaration of "
                          ++ id ++ " has not enough bodies. This is a bug.")
      | Some {| ind_type := A |} =>
      let tA' := tsl_ty ΣE A in
      match tA' with
      | Error e =>
        tmFail ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
        let id' := tsl_id id in
        tmLemma id' tA' ;;
        let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
        let E' := (IndRef (mkInd kn n), tConst id' []) :: (snd ΣE) in
        tmMsg (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end

  | Some (ConstructRef (mkInd kn n) k) =>
    d <- tmQuoteInductive kn ;;
    tmDebug "plop1" ;;
    match List.nth_error (ind_bodies d) n with
    | None => tmFail ("The declaration of "
                        ++ id ++ " has not enough bodies. This is a bug.")
    | Some {| ind_ctors := ctors |} =>
      match List.nth_error ctors k with
      | None => tmFail ("The body of "
                          ++ id ++ " has not enough constructors. This is a bug.")
      | Some (_, ty, _) =>  (* keep id? *)
        tmMsg "plop3" ;;
        let A := subst0 (inds kn [] (* FIXME uctx *) (ind_bodies d)) ty in
        tmMsg "plop4" ;;
        let tA' := tsl_ty ΣE A in
        tmMsg "plop5" ;;
        match tA' with
        | Error e =>
(*          tmPrint e ;; *)
          tmFail ("Translation error during the translation of the type of " ++ id)
        | Success tA' =>
          tmMsg "plop6" ;;
          let id' := tsl_id id in
          tmLemma id' tA' ;;
          let E' := (ConstructRef (mkInd kn n) k, tConst id' []) :: (snd ΣE) in
          tmMsg (id ++ " has been translated as " ++ id') ;;
          ret (fst ΣE, E')
        end
      end
    end
  end
  end.



Require Import Ascii.

Fixpoint string_of_ascii_list l :=
  match l with
  | nil => EmptyString
  | a :: s => String a (string_of_ascii_list s)
  end.

Definition string_of_ascii_list_rev l := string_of_ascii_list (rev l).

(* Compute (string_of_ascii_list_rev ["."; "g"; "h"]%char). *)


(* empty list on empty string ?? *)
(* acc is in reverse order *)
Fixpoint split_string_aux (sep : ascii) (s : string) (acc : list ascii)
  : list string :=
  match s with
  | EmptyString => [string_of_ascii_list_rev acc]
  | String a s => if Ascii.ascii_dec a sep then (string_of_ascii_list_rev acc)
                                                 :: (split_string_aux sep s [])
                 else split_string_aux sep s (a :: acc)
  end.

Definition split_string (sep : Ascii.ascii) (s : string) : list string :=
  split_string_aux sep s [].

(* Compute (split_string "."%char "eopjqd.qS.E"). *)
(* Compute (split_string "."%char ""). *)

Definition ident_of_kn (kn : kername) : ident
  := last (split_string "."%char kn) kn.

Definition tsl_kn (tsl_ident : ident -> ident) (kn : kername) mp
  := mp ++ "." ++ (tsl_ident (ident_of_kn kn)).

Definition TranslateRec {tsl : Translation} (ΣE : tsl_context) (p : program)
: TM tsl_context :=
  tmMsg "~~~~~~~~~~~~~~~~~~" ;;
  monad_fold_left (fun ΣE decl =>
    tmMsg ("Translating " ++ global_decl_ident decl) ;;
    match decl with
    | ConstantDecl kn decl =>
      match lookup_tsl_table (snd ΣE) (ConstRef kn) with
      | Some _ => tmMsg (kn ++ " was already translated") ;; ret ΣE
      | None =>
        match decl with
        | {| cst_body := None |} =>
          tmFail (kn ++ " is an axiom. Use Implement Existing.")

        | {| cst_type := A; cst_body := Some t; cst_universes := univs |} =>
          tmDebug "go";;
          let t' := tsl_tm ΣE t in
          tmDebug "done";;
          match t' with
          | Error e =>
            (*  e ;; *)
            tmFail ("Translation error during the translation of the body of "
                       ++ kn)
          | Success t' =>
            let id := ident_of_kn kn in
            let id' := tsl_ident id in
            tmDebug "here";;
            tmDebug id' ;;
            tmDebug t' ;;
            tmDefinition id' None t' ;;
            tmDebug "there";;
            let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
            let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
            tmMsg  (id ++ " has been translated as " ++ id') ;;
            ret (Σ', E')
          end
        end
      end
    | InductiveDecl kn d =>
      match lookup_tsl_table (snd ΣE) (IndRef (mkInd kn 0)) with
      | Some _ => tmMsg (kn ++ " was already translated") ;; ret ΣE
      | None =>
        tmDebug "go'";;
        mp <- tmCurrentModPath ;;
        let d' := tsl_ind ΣE mp kn d in
        tmDebug "done'";;
         match d' with
         | Error e =>
           tmFail ("Translation error during the translation of the inductive "
                      ++ kn)
         | Success (E, decls) =>
           monad_iter tmInductive' decls ;;
           let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
           let E' := (E ++ (snd ΣE))%list in
           tmMsg  (kn ++ " has been translated.") ;;
           ret (Σ', E')
         end
      end
    end)
  (fst p) ΣE.