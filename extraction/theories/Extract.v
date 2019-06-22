
(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval.
From MetaCoq.Extraction Require EAst ELiftSubst ETyping EWcbvEval.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.

Section IsType.
  Context {F : Fuel}.
  Variables (Σ : global_context) (Γ : context).

  Fixpoint is_arity (F : Fuel) t : typing_result bool :=
    match F with
    | 0 => raise (NotEnoughFuel F)
    | S F =>
      match reduce_to_sort Σ Γ t with
      | Checked u => ret true
      | TypeError _ =>
        p <- reduce_to_prod Σ Γ t ;;
        is_arity F (snd p)
      end
    end.

  Definition is_type_or_proof t :=
    ty <- type_of Σ Γ t ;;
     if is_arity F ty then ret true
     else
       s <- type_of_as_sort Σ (type_of Σ) Γ ty ;;
       ret (Universe.is_prop s).
End IsType.

Module E := EAst.

Section Erase.
  Context `{F : Fuel}.

  Definition is_box c :=
    match c with
    | E.tBox => true
    | _ => false
    end.

  Fixpoint mkAppBox c n :=
    match n with
    | 0 => c
    | S n => mkAppBox (E.tApp c E.tBox) n
    end.

  Definition on_snd_map {A B C} (f : B -> C) (p : A * B) :=
    (fst p, f (snd p)).

  Section EraseMfix.
    Context (extract : forall (Γ : context) (t : term), typing_result E.term).

    Definition extract_mfix Γ (defs : mfixpoint term) : typing_result (EAst.mfixpoint E.term) :=
      let Γ' := (fix_decls defs ++ Γ)%list in
      monad_map (fun d => dbody' <- extract Γ' d.(dbody);;
                          ret ({| E.dname := d.(dname); E.rarg := d.(rarg);
                                  E.dbody := dbody' |})) defs.
  End EraseMfix.
  
  Fixpoint extract (Σ : global_context) (Γ : context) (t : term) : typing_result E.term :=
    b <- is_type_or_proof Σ Γ t ;;
    if (b : bool) then ret E.tBox else
    match t with
    | tRel i => ret (E.tRel i)
    | tVar n => ret (E.tVar n)
    | tEvar m l =>
      l' <- monad_map (extract Σ Γ) l;;
      ret (E.tEvar m l')
    | tSort u => ret E.tBox
    | tConst kn u => ret (E.tConst kn)
    | tInd kn u => ret E.tBox
    | tConstruct kn k u => ret (E.tConstruct kn k)
    | tProd na b t => ret E.tBox
    | tLambda na b t =>
      t' <- extract Σ (vass na b :: Γ) t;;
      ret (E.tLambda na t')
    | tLetIn na b t0 t1 =>
      b' <- extract Σ Γ b;;
      t1' <- extract Σ (vdef na b t0 :: Γ) t1;;
      ret (E.tLetIn na b' t1')
    | tApp f u =>
      f' <- extract Σ Γ f;;
      l' <- extract Σ Γ u;;
      ret (E.tApp f' l') (* if is_dummy f' then ret dummy else *)
    | tCase ip p c brs =>
      c' <- extract Σ Γ c;;
      if is_box c' then
        match brs with
        | (n, x) :: _ =>
          x' <- extract Σ Γ x;;
          ret (mkAppBox x' n) (* Singleton elimination *)
        | nil =>
          ret (E.tCase ip c' nil) (* Falsity elimination *)
        end
      else
        brs' <- monad_map (T:=typing_result) (fun x => x' <- extract Σ Γ (snd x);; ret (fst x, x')) brs;;
        ret (E.tCase ip c' brs')
    | tProj p c =>
      c' <- extract Σ Γ c;;
      ret (E.tProj p c')
    | tFix mfix n =>
      mfix' <- extract_mfix (extract Σ) Γ mfix;;
      ret (E.tFix mfix' n)
    | tCoFix mfix n =>
      mfix' <- extract_mfix (extract Σ) Γ mfix;;
      ret (E.tCoFix mfix' n)
    end.

End Erase.

Definition optM {M : Type -> Type} `{Monad M} {A B} (x : option A) (f : A -> M B) : M (option B) :=
  match x with
  | Some x => y <- f x ;; ret (Some y)
  | None => ret None
  end.

Definition extract_constant_body `{F:Fuel} Σ (cb : constant_body) : typing_result E.constant_body :=
  ty <- extract Σ [] cb.(cst_type) ;;
  body <- optM cb.(cst_body) (fun b => extract Σ [] b);;
  ret {| E.cst_type := ty; E.cst_body := body; |}.

Definition lift_opt_typing {A} (a : option A) (e : type_error) : typing_result A :=
  match a with
  | Some x => ret x
  | None => raise e
  end.

Definition extract_one_inductive_body `{F:Fuel} Σ npars arities
           (oib : one_inductive_body) : typing_result E.one_inductive_body :=
  decty <- lift_opt_typing (decompose_prod_n_assum [] npars oib.(ind_type))
        (NotAnInductive oib.(ind_type)) ;;
  let '(params, arity) := decty in
  type <- extract Σ [] oib.(ind_type) ;;
  ctors <- monad_map (fun '(x, y, z) => y' <- extract Σ arities y;; ret (x, y', z)) oib.(ind_ctors);;
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  projs <- monad_map (fun '(x, y) => y' <- extract Σ [] y;; ret (x, y')) oib.(ind_projs);;
  ret {| E.ind_name := oib.(ind_name);
         E.ind_type := type;
         E.ind_kelim := oib.(ind_kelim);
         E.ind_ctors := ctors;
         E.ind_projs := projs |}.

Definition extract_mutual_inductive_body `{F:Fuel} Σ
           (mib : mutual_inductive_body) : typing_result E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  bodies <- monad_map (extract_one_inductive_body Σ mib.(ind_npars) arities) bds ;;
  ret {| E.ind_npars := mib.(ind_npars);
         E.ind_bodies := bodies; |}.

Fixpoint extract_global_decls `{F:Fuel} univs Σ : typing_result E.global_declarations :=
  match Σ with
  | [] => ret []
  | ConstantDecl kn cb :: Σ =>
    cb' <- extract_constant_body (Σ, univs) cb;;
    Σ' <- extract_global_decls univs Σ;;
    ret (E.ConstantDecl kn cb' :: Σ')
  | InductiveDecl kn mib :: Σ =>
    mib' <- extract_mutual_inductive_body (Σ, univs) mib;;
    Σ' <- extract_global_decls univs Σ;;
    ret (E.InductiveDecl kn mib' :: Σ')
  end.

Definition extract_global `{F : Fuel} Σ :=
  let '(Σ, univs) := Σ in
  Σ' <- extract_global_decls univs (List.rev Σ);;
  ret (List.rev Σ').

(** * Erasure correctness
    
    The statement below expresses that any well-typed term's
    extraction has the same operational semantics as its source, under
    a few conditions:

    - The terms has to be locally closed, otherwise evaluation could get 
      stuck on free variables. Typing under an empty context ensures that.
    - The global environment is axiom-free, for the same reason.
    - The object is of inductive type, or more generally a function resulting 
      ultimately in an inductive value when applied.

   We use an observational equality relation to relate the two values, 
   which is indifferent to the extractd parts.
 *)

Fixpoint inductive_arity (t : term) :=
  match t with
  | tApp f _ | f =>
    match f with
    | tInd ind u => Some ind
    | _ => None
    end
  end.

(* Inductive inductive_arity : term -> Prop := *)
(* | inductive_arity_concl ind u args : inductive_arity (mkApps (tInd ind u) args) *)
(* | inductive_arity_arrow na b t : inductive_arity t -> inductive_arity (tProd na b t). *)

Definition option_is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition is_axiom_decl g :=
  match g with
  | ConstantDecl kn cb => option_is_none cb.(cst_body)
  | InductiveDecl kn ind => false
  end.

Definition axiom_free Σ :=
  List.forallb (fun g => negb (is_axiom_decl g)) Σ.

Definition computational_ind Σ ind :=
  let 'mkInd mind n := ind in
  let mib := lookup_env Σ mind in
  match mib with
  | Some (InductiveDecl kn decl) =>
    match List.nth_error decl.(ind_bodies) n with
    | Some body =>
      match destArity [] body.(ind_type) with
      | Some arity => negb (Universe.is_prop (snd arity))
      | None => false
      end
    | None => false
    end
  | _ => false
  end.

Definition computational_type Σ T :=
  exists ind, inductive_arity T = Some ind /\ computational_ind Σ ind.

(** The precondition on the extraction theorem. *)

Record extraction_pre (Σ : global_context) t T :=
  { extr_typed : Σ ;;; [] |- t : T;
    extr_env_axiom_free : axiom_free (fst Σ);
    extr_computational_type : computational_type Σ T }.

(** The observational equivalence relation between source and extractd values. *)

Inductive Question : Set  := 
| Cnstr : inductive -> nat -> Question
| Abs : Question.

Definition observe (q : Question) (v : E.term) : bool :=
  match q with
  | Cnstr i k =>
    match v with
    | E.tConstruct i' k' =>
      eq_ind i i' && eq_nat k k'
    | _ => false
    end
  | Abs =>
    match v with
    | E.tLambda _ _ => true
    | E.tFix _ _ => true
    | _ => false
    end
  end.
             

(*
Fixpoint obs_eq (Σ : global_context) (v v' : term) (T : term) (s : universe) : Prop :=
  if is_prop_sort s then is_dummy v'
  else
    match T with
    | tInd ind u =>
      (* Canonical inductive value *)
      let '(hd, args) := destApp v in
      let '(hd', args') := destApp v' in
      eq_term Σ hd hd' /\ obs_eq 
      
 | obs_eq_prf v T s : Σ ;;; [] |- v : T ->
  Σ ;;; [] |- T : tSort s ->
  is_prop_sort s ->
  obs_eq Σ v dummy

| obs_eq_cstr ind k u args args' T : Σ ;;; [] |- mkApps (tConstruct ind k u) args : T ->
  computational_type Σ T ->
  Forall2 (obs_eq Σ) args args' ->
  obs_eq Σ (mkApps (tConstruct ind k u) args) (mkApps (tConstruct ind k u) args')

| obs_eq_arrow na f f' T T' :
    Σ ;;; [] |- f : tProd na T T' ->
    (forall arg arg', obs_eq Σ arg arg' -> 
    
    obs_eq Σ f f'.                                     
*)                      

Record extraction_post (Σ : global_context) (Σ' : EAst.global_context) (t : term) (t' : E.term) : Prop :=
  { extr_value : E.term;
    extr_eval : EWcbvEval.eval Σ' t' extr_value;
    (* extr_equiv : obs_eq Σ v extr_value *) }.

(** The extraction correctness theorem we conjecture. *)

Definition erasure_correctness :=
  forall Σ t T, extraction_pre Σ t T ->
  forall v, eval Σ [] t v ->
  forall (f : Fuel) Σ' (t' : E.term),
    extract Σ [] t = Checked t' ->
    extract_global Σ = Checked Σ' ->
    extraction_post Σ Σ' t t'.
      
(* Conjecture erasure_correct : erasure_correctness. *)
