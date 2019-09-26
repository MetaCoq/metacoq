From MetaCoq.Template Require Import All TemplateMonad.Core Monad monad_utils.
From MetaCoq.Checker Require Import All.
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


Definition tsl_context := (global_env_ext * tsl_table)%type.

Definition emptyTC : tsl_context := (empty_ext [], []).

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


Definition tmDebug {A} : A -> TemplateMonad unit
  := tmPrint.
  (* := fun _ => ret tt. *)


Definition add_global_decl d (Σ : global_env_ext) : global_env_ext
  := (d :: Σ.1, Σ.2).


Definition Translate {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  tmDebug ("Translate" ++ id);;
  gr <- tmAbout id ;;
  tmDebug gr;;
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _)
  | Some (IndRef (mkInd kn n)) =>
    mp <- tmCurrentModPath tt ;;
    d <- tmQuoteInductive id ;;
    d' <- tmEval lazy (tsl_ind ΣE mp kn d) ;;
    match d' with
    | Error e =>
      print_nf e ;;
      fail_nf ("Translation error during the translation of the inductive " ++ id)
    | Success (E, decls) =>
      monad_iter tmMkInductive' decls ;;
      let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
      let E' := (E ++ (snd ΣE))%list in
      Σ' <- tmEval lazy Σ' ;;
      E' <- tmEval lazy E' ;;
      tmMsg (kn ++ " has been translated.") ;;
      ret (Σ', E')
    end
    
  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ =>
      fail_nf (id ++ " is an axiom, not a definition. Use Implement Existing.")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_universes := univs;
                         definition_entry_body := t |} =>
      tmDebug t ;;
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      tmDebug t' ;;
      match t' with
      | Error e =>
        print_nf e ;;
        fail_nf ("Translation error during the translation of the body of " ++ id)
      | Success t' =>
        id' <- tmEval all (tsl_id id) ;;
            tmDebug "here" ;;
            tmDebug id' ;;
            tmDebug t' ;;
        tmMkDefinition id' t' ;;
            tmDebug "doneu" ;;
        let decl := {| cst_universes := univs;
                       cst_type := A; cst_body := Some t |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        Σ' <- tmEval lazy Σ' ;;
        E' <- tmEval lazy E' ;;
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  end.


Definition Implement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA  <- tmQuote A ;;
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty => 
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  print_nf tA' ;;
  match tA' with
  | Error e =>
    print_nf e ;;
    tmFail "Translation error during the translation of the type."
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      tmBind (tmUnquoteTyped Type tA') (fun A' =>
      tmLemma id' A' ;;
      tmAxiom id A ;;
      gr <- tmAbout id ;;
      match gr with
      | Some (ConstRef kn) =>
        let decl := {| cst_universes := Monomorphic_ctx ContextSet.empty;
                       cst_type := tA; cst_body := None |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      | _ => fail_nf (id ++ " was not found or is not a constant. This is a bug.")
      end)
  end
  end.

Definition body_constant_entry (e : constant_entry) : option term :=
  match e with
  | ParameterEntry _ => None
  | DefinitionEntry {| definition_entry_body := t |} => Some t
  end.


Definition ImplementExisting {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty => 
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry  {| parameter_entry_type := A  |}
    | DefinitionEntry {| definition_entry_type := A |} =>
      tmDebug "plop1" ;;
      ΣE <- tmEval lazy ΣE ;;
      tmDebug ΣE ;;
      tA' <- tmEval lazy (tsl_ty ΣE A) ;;  (* long *)
      tmDebug "plop" ;;
      match tA' with
      | Error e =>
        print_nf e ;;
        fail_nf ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
        tmDebug "plop2" ;;
        tmBind (tmUnquoteTyped Type tA') (fun A' =>
        tmDebug "plop3" ;;
        tmLemma id' A' ;;
        let decl := {| cst_universes := Monomorphic_ctx ContextSet.empty;
                       cst_type := A; cst_body := body_constant_entry e |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E'))
      end
    end
  | Some (IndRef (mkInd kn n)) =>
    d <- tmQuoteInductive kn ;;
    match List.nth_error (ind_bodies d) n with
      | None => fail_nf ("The declaration of "
                          ++ id ++ " has not enough bodies. This is a bug.")
      | Some {| ind_type := A |} => 
      tA' <- tmEval lazy (tsl_ty ΣE A) ;;
      match tA' with
      | Error e =>
        print_nf e ;;
        fail_nf ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
        id' <- tmEval all (tsl_id id) ;;
        tmBind (tmUnquoteTyped Type tA') (fun A' =>
        tmLemma id' A' ;;
        let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
        let E' := (IndRef (mkInd kn n), tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E'))
      end
    end

  | Some (ConstructRef (mkInd kn n) k) =>
    d <- tmQuoteInductive kn ;;
    tmDebug "plop1" ;;
    match List.nth_error (ind_bodies d) n with
    | None => fail_nf ("The declaration of "
                        ++ id ++ " has not enough bodies. This is a bug.")
    | Some {| ind_ctors := ctors |} => 
      tmDebug "plop2" ;;
      match List.nth_error ctors k with
      | None => fail_nf ("The body of "
                          ++ id ++ " has not enough constructors. This is a bug.")
      | Some (_, ty, _) =>  (* keep id? *)
        tmDebug "plop3" ;;
        let A := subst0 (inds kn [] (* FIXME uctx *) (ind_bodies d)) ty in
        tmDebug "plop4" ;;
        tA' <- tmEval lazy (tsl_ty ΣE A) ;;
        tmDebug "plop5" ;;
        match tA' with
        | Error e =>
          print_nf e ;;
          fail_nf ("Translation error during the translation of the type of " ++ id)
        | Success tA' =>
          tmDebug "plop6" ;;
          id' <- tmEval all (tsl_id id) ;;
          tmBind (tmUnquoteTyped Type tA') (fun A' =>
          tmDebug "plop7" ;;
          tmLemma id' A' ;;
          let E' := (ConstructRef (mkInd kn n) k, tConst id' []) :: (snd ΣE) in
          print_nf (id ++ " has been translated as " ++ id') ;;
          ret (fst ΣE, E'))
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



Definition TranslateRec {tsl : Translation} (ΣE : tsl_context) {A} (t : A) := 
  p <- tmQuoteRec t ;;
  tmPrint "~~~~~~~~~~~~~~~~~~" ;;
  monad_fold_left (fun ΣE decl =>
    print_nf ("Translating " ++ global_decl_ident decl) ;;
    match decl with
    | ConstantDecl kn decl =>
      match lookup_tsl_table (snd ΣE) (ConstRef kn) with
      | Some _ => print_nf (kn ++ " was already translated") ;; ret ΣE
      | None => 
        match decl with
        | {| cst_body := None |} =>
          fail_nf (kn ++ " is an axiom. Use Implement Existing.")
                    
        | {| cst_type := A; cst_body := Some t; cst_universes := univs |} =>
          tmDebug "go";;
          t' <- tmEval lazy (tsl_tm ΣE t) ;;
          tmDebug "done";;
          match t' with
          | Error e =>
            print_nf e ;;
            fail_nf ("Translation error during the translation of the body of "
                       ++ kn)
          | Success t' =>
            let id := ident_of_kn kn in
            let id' := tsl_ident id in
            tmDebug "here";;
            tmDebug id' ;;
            tmDebug t' ;;
            tmMkDefinition id' t' ;;
            tmDebug "there";;
            let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
            let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            print_nf  (id ++ " has been translated as " ++ id') ;;
            ret (Σ', E')
          end
        end
      end

    | InductiveDecl kn d => 
      match lookup_tsl_table (snd ΣE) (IndRef (mkInd kn 0)) with
      | Some _ => print_nf (kn ++ " was already translated") ;; ret ΣE
      | None => 
        tmDebug "go'";;
        mp <- tmCurrentModPath tt ;;
        d' <- tmEval lazy (tsl_ind ΣE mp kn d) ;;
        tmDebug "done'";;
         match d' with
         | Error e => 
           print_nf e ;;
           fail_nf ("Translation error during the translation of the inductive "
                      ++ kn)
         | Success (E, decls) =>
           monad_iter tmMkInductive' decls ;;
           let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
           let E' := (E ++ (snd ΣE))%list in
           Σ' <- tmEval lazy Σ' ;;
           E' <- tmEval lazy E' ;;
           print_nf  (kn ++ " has been translated.") ;;
           ret (Σ', E')
         end
      end
    end)
  (fst p) ΣE.
