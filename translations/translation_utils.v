Require Import Template.Ast Template.Typing Template.Checker Template.monad_utils Template.Template.
Require Import Translations.sigma.
Require Import List.
Import ListNotations MonadNotation String.
Open Scope string_scope.

Axiom todo : forall {A}, A.

(* Inductive global_reference := *)
(* (* VarRef of Names.variable *) *)
(*   | ConstRef : string (* kername *) -> global_reference *)
(*   | IndRef : inductive -> global_reference *)
(*   | ConstructRef : inductive -> nat -> global_reference. *)

Hint Resolve String.string_dec Peano_dec.eq_nat_dec : eq_dec.

Definition string_of_gref gr :=
  match gr with
  | ConstRef s => s
  | IndRef (mkInd s n) => "todo" ++ s
  | ConstructRef (mkInd s n) k => "todo" ++ s
  end.

Definition gref_eq_dec
  : forall gr gr' : global_reference, {gr = gr'} + {~ gr = gr'}.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
Defined.

Definition tsl_table := list (global_reference * term).

Definition empty_global_ctx : global_context := [].
Definition empty_tsl_table : tsl_table := [].

Definition add_global_ctx : global_decl -> global_context -> global_context
  := cons.
Definition add_tsl_table : global_reference -> term -> tsl_table -> tsl_table
  := fun kn t => cons (kn, t).


Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.


Definition tsl_context := (global_context * tsl_table)%type.


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
                       tsl_ind : tsl_context -> ident -> mutual_inductive_entry
                            -> tsl_result (tsl_table * list mutual_inductive_entry)
                     }.



Quote Definition tSigma := sigma.
Quote Definition tPair := @mk_sig.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
Definition proj1 (t : term) : term
  := tProj (mkInd "Translations.sigma.sigma" 0, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (mkInd "Translations.sigma.sigma" 0, 2, 1) t.
Definition proj (b : bool) (t : term) : term
  := tProj (mkInd "Translations.sigma.sigma" 0, 2, if b then 0 else 1) t.

Quote Definition tBool := bool.
Quote Definition tTrue := true.
Definition timesBool (t : term) :=
  tApp tSigma [t; tLambda nAnon t tBool].
Definition pairTrue typ t := pair typ (tLambda nAnon typ tBool) t tTrue.

Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition print_nf {A} (msg : A) : TemplateMonad unit
  := (tmEval all msg) >>= tmPrint.

Definition tTranslate (tsl : Translation) (ΣE : tsl_context) (id : ident)
  : TemplateMonad (option tsl_context) :=
  gr <- tmAbout id ;;
  match gr with
  | IndRef ind
  | ConstructRef ind _ => tmPrint "todo tTranslate" ;; ret None
  | ConstRef kn =>
    e <- tmQuoteConstant kn true ;;
    print_nf ("toto1" ++ id) ;;
    match e with
    | ParameterEntry _ => print_nf (id ++ "is an axiom, not a definition") ;;
                         ret None
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_body := t |} =>
      print_nf ("toto2 " ++ id) ;;
      (* tmPrint t ;; *)
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      match t' with
      | Error e => tmPrint "tsl error in term: " ;; tmPrint e ;; ret None
      | Success t' =>
        print_nf ("toto3 " ++ id) ;;
        A' <- tmEval lazy (tsl_ty ΣE A) ;;
        match A' with
        | Error e => tmPrint "tsl error in type: " ;; tmPrint e ;; ret None
        | Success A' =>
          print_nf ("toto4 " ++ id) ;;
          id' <- tmEval all (tsl_id id) ;;
          tmMkDefinition id' t' ;;
          print_nf ("toto5 " ++ id) ;;
          let decl := {| cst_universes := [];
                         cst_type := A; cst_body := Some t |} in
          let Σ' := ConstantDecl kn decl :: (fst ΣE) in
          let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
          print_nf  (id ++ " has been translated as " ++ id') ;;
          tmEval all (Some (Σ', E'))
        end
      end
    end
  end.



Definition tImplement (tsl : Translation) (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (option tsl_context) :=
  tA <- tmQuote A ;;
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  match tA' with
  | Error e => tmPrint "tsl error in type" ;; tmPrint e ;;
                tmReturn None
  | Success tA' =>
    print_nf ("tata1 " ++ id) ;;
    id' <- tmEval all (tsl_id id) ;;
    print_nf ("tata2 " ++ id) ;;
    A' <- tmUnquoteTyped Type tA' ;;
    print_nf ("tata3 " ++ id) ;;
    tmLemma id' A' ;;
    print_nf ("tata4 " ++ id) ;;
    tmAxiom id A ;;
    let decl := {| cst_universes := [];
                   cst_type := tA; cst_body := None |} in
    let Σ' := ConstantDecl id decl :: (fst ΣE) in (* should be kn *)
    let E' := (ConstRef id, tConst id' []) :: (snd ΣE) in (* id or kn ?? *)
    print_nf (id ++ " has been translated as " ++ id') ;;
    tmEval all (Some (Σ', E'))
  end.


Definition tImplementExisting (tsl_id : ident -> ident)
           (tsl_tm tsl_ty : global_context -> tsl_table -> term
                            -> tsl_result term)
           (Σ : tsl_context) (id : ident)
  : TemplateMonad (option tsl_context) :=
  e <- tmQuoteConstant id true ;;
  match e with
  | ParameterEntry _ => tmPrint "Not a definition" ;;
                       tmReturn None
  | DefinitionEntry {| definition_entry_type := A;
                       definition_entry_body := t |} =>
    match tsl_ty (fst Σ) (snd Σ) A with
    | Error _ => tmPrint "tsl error in type" ;;
                  tmReturn None
    | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      A' <- tmUnquoteTyped Type tA' ;;
      tmLemma id' A' ;;
      let decl := {| cst_universes := [];
                     cst_type := A; cst_body := Some t |} in
      let Σ' := ConstantDecl id decl :: (fst Σ) in
      let E' := (ConstRef id, tConst id' []) :: (snd Σ) in
      msg <- tmEval all (id ++ " has been translated as " ++ id') ;;
      tmPrint msg ;;
      tmReturn (Some (Σ', E'))
    end
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

Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Definition get_ident (n : name) :=
  match n with
  | nAnon => "XX"
  | nNamed i => i
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition mind_decl_to_entry (* (id : ident) *) (decl : minductive_decl)
  : mutual_inductive_entry.
Proof.
  refine ({|
             mind_entry_record := None; (* not a record *)
             mind_entry_finite := Finite; (* inductive *)
             mind_entry_params := _;
             mind_entry_inds := _;
             mind_entry_polymorphic := false;
             mind_entry_private := None;
           |}).
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* todo *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.rev (List.combine _ _)).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
    (* pose (fold_left_i (fun acc i ty => let na := tVar (get_ident (List.nth i names nAnon)) *)
    (*                                 in (na :: fst acc, substl (fst acc) ty :: snd acc)) types ([], [])). *)
    (* exact (snd p). *)
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine ({| mind_entry_typename := ind_name;
               mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
               mind_entry_template := false;
               mind_entry_consnames := _;
               mind_entry_lc := _;
            |}).
    
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.

(* Inductive eq' (A : Set) (x : A) : A -> Prop :=  eq_refl' : eq' A x x. *)
(* Quote Recursively Definition eq'_prog := eq'. *)
(* Definition eq'_decl := Eval compute in *)
(*       extract_mind_decl_from_program "Top.eq'" eq'_prog. *)

Quote Recursively Definition sigma_prog := @sigma.
Quote Recursively Definition eq_prog := @eq.
Quote Recursively Definition nat_prog := nat.

Definition eq_decl := Eval compute in
      option_get todo (extract_mind_decl_from_program "Coq.Init.Logic.eq" eq_prog).
Definition sigma_decl := Eval compute in
      option_get todo (extract_mind_decl_from_program "Template.sigma.sigma" sigma_prog).
Definition nat_decl := Eval compute in
      option_get todo (extract_mind_decl_from_program "Coq.Init.Datatypes.nat" nat_prog).

Definition eq_entry := Eval compute in mind_decl_to_entry eq_decl.
Definition sigma_entry := Eval compute in mind_decl_to_entry sigma_decl.
Definition nat_entry := Eval compute in mind_decl_to_entry nat_decl.
(* Make Inductive eq_entry. *)
(* Make Inductive sigma_entry. *)

