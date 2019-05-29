
(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval.
From TemplateExtraction Require EAst ELiftSubst ETyping EWcbvEval.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.

Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

Parameter is_type_or_proof : forall (Sigma : global_context) (Gamma : context) (t : PCUICAst.term), bool.
From PCUIC Require Import PCUICTyping.

Axiom is_type_or_proof_spec : forall (Sigma : global_context) (Gamma : context) (t : PCUICAst.term) T,
    Sigma ;;; Gamma |- t : T -> (is_type_or_proof Sigma Gamma t = true) <~> (isArity T + (∑ u, (Sigma ;;; Gamma |- T : tSort u) * is_prop_sort u)). 

(* Section IsType. *)
(*   (* Context {F : Fuel}. *) *)
(*   Variables (Σ : global_context) (Γ : context). *)

(*   Fixpoint is_arity (F : Fuel) t : typing_result bool := *)
(*     match F with *)
(*     | 0 => raise (NotEnoughFuel F) *)
(*     | S F => *)
(*       match reduce_to_sort Σ Γ t with *)
(*       | Checked u => ret true *)
(*       | TypeError _ => *)
(*         p <- reduce_to_prod Σ Γ t ;; *)
(*         is_arity F (snd p) *)
(*       end *)
(*     end. *)

(*   Definition is_type_or_proof t := *)
(*     ty <- type_of Σ Γ t ;; *)
(*      if is_arity F ty then ret true *)
(*      else *)
(*        s <- type_of_as_sort Σ (type_of Σ) Γ ty ;; *)
(*        ret (is_prop_sort s). *)
(* End IsType. *)

Module E := EAst.

Local Notation Ret t := t.

Section Erase.
  (* Context `{F : Fuel}. *)

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
    Context (extract : forall (Γ : context) (t : term), E.term).

    Definition extract_mfix Γ (defs : mfixpoint term) : (EAst.mfixpoint E.term) :=
      let Γ' := (fix_decls defs ++ Γ)%list in
      map (fun d => let dbody' := extract Γ' d.(dbody) in
                          Ret ({| E.dname := d.(dname); E.rarg := d.(rarg);
                                  E.dbody := dbody' |})) defs.
  End EraseMfix.
  
  Fixpoint extract (Σ : global_context) (Γ : context) (t : term) : E.term :=
    if is_type_or_proof Σ Γ t then E.tBox else
    match t with
    | tRel i => Ret (E.tRel i)
    | tVar n => Ret (E.tVar n)
    | tEvar m l =>
      Ret (E.tEvar m (map (extract Σ Γ) l))
    | tSort u => Ret E.tBox
    | tConst kn u => Ret (E.tConst kn)
    | tInd kn u => Ret E.tBox
    | tConstruct kn k u => Ret (E.tConstruct kn k)
    | tProd na b t => Ret E.tBox
    | tLambda na b t =>
      let t' := extract Σ (vass na b :: Γ) t in
      Ret (E.tLambda na t')
    | tLetIn na b t0 t1 =>
      let b' := extract Σ Γ b in
      let t1' := extract Σ (vdef na b t0 :: Γ) t1 in
      Ret (E.tLetIn na b' t1')
    | tApp f u =>
      let f' := extract Σ Γ f in
      let l' := extract Σ Γ u in
      Ret (E.tApp f' l') (* if is_dummy f' then Ret dummy else *)
    | tCase ip p c brs =>
      let c' := extract Σ Γ c in
      if is_box c' then
        match brs with
        | (n, x) :: _ =>
          let x' := extract Σ Γ x in
          Ret (mkAppBox x' n) (* Singleton elimination *)
        | nil =>
          Ret (E.tCase ip c' nil) (* Falsity elimination *)
        end
      else
        let brs' := map (B := nat * E.term) (fun x => let x' := extract Σ Γ (snd x) in Ret (fst x, x')) brs in
        Ret (E.tCase ip c' brs')
    | tProj p c =>
      let c' := extract Σ Γ c in
      Ret (E.tProj p c')
    | tFix mfix n =>
      let mfix' := extract_mfix (extract Σ) Γ mfix in
      Ret (E.tFix mfix' n)
    | tCoFix mfix n =>
      let mfix' := extract_mfix (extract Σ) Γ mfix in
      Ret (E.tCoFix mfix' n)
    end.

End Erase.


(* Definition optM {A B} (x : option A) (f : A -> B) : M (option B) := *)
(*   match x with *)
(*   | Some x => y <- f x ;; ret (Some y) *)
(*   | None => ret None *)
(*   end. *)

Definition extract_constant_body Σ (cb : constant_body) : E.constant_body :=
  let ty := extract Σ [] cb.(cst_type) in
  let body := option_map (fun b => extract Σ [] b) cb.(cst_body)  in
  Ret {| E.cst_type := ty; E.cst_body := body; |}.

(* Definition lift_opt_typing {A} (a : option A) (e : type_error) : typing_result A := *)
(*   match a with *)
(*   | Some x => ret x *)
(*   | None => raise e *)
(*   end. *)

Definition opt_def {A} (a : option A) (e : A) : A :=
  match a with
  | Some x => Ret x
  | None => e
  end.


Definition extract_one_inductive_body (Σ : global_context) (npars : nat) (arities : context)
           (oib : one_inductive_body) : E.one_inductive_body :=
  let decty := opt_def (decompose_prod_n_assum [] npars oib.(ind_type)) ([], tRel 0) in
  let '(params, arity) := decty in
  let type := Ret (extract Σ [] oib.(ind_type)) in
  let ctors := map (fun '(x, y, z) => let y' := Ret (extract Σ arities y) in Ret (x, y', z)) oib.(ind_ctors) in
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  let projs := map (fun '(x, y) => let y' := Ret (extract Σ [] y) in Ret (x, y')) oib.(ind_projs) in
  Ret {| E.ind_name := oib.(ind_name);
         E.ind_type := type;
         E.ind_kelim := oib.(ind_kelim);
         E.ind_ctors := ctors;
         E.ind_projs := projs |}.

Definition extract_mutual_inductive_body Σ
           (mib : mutual_inductive_body) : E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  let bodies := map (extract_one_inductive_body Σ mib.(ind_npars) arities) bds in
  Ret {| E.ind_npars := mib.(ind_npars);
         E.ind_bodies := bodies; |}.

Fixpoint extract_global_decls univs Σ : E.global_declarations :=
  match Σ with
  | [] => []
  | ConstantDecl kn cb :: Σ =>
    let cb' := extract_constant_body (Σ, univs) cb in
    let Σ' := extract_global_decls univs Σ in
    E.ConstantDecl kn cb' :: Σ'
  | InductiveDecl kn mib :: Σ =>
    let mib' := extract_mutual_inductive_body (Σ, univs) mib in
    let Σ' := extract_global_decls univs Σ in
    E.InductiveDecl kn mib' :: Σ'
  end.

Definition extract_global Σ :=
  let '(Σ, univs) := Σ in
  extract_global_decls univs Σ.

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
      | Some arity => negb (is_prop_sort (snd arity))
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
    extr_env_wf : wf Σ ;
    (* extr_computational_type : computational_type Σ T *) }.

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
             


(* Fixpoint obs_eq (Σ : global_context) (v v' : term) (T : term) (s : universe) : Prop := *)
(*   if is_prop_sort s then is_dummy v' *)
(*   else *)
(*     match T with *)
(*     | tInd ind u => *)
(*       (* Canonical inductive value *) *)
(*       let '(hd, args) := destApp v in *)
(*       let '(hd', args') := destApp v' in *)
(*       eq_term Σ hd hd' /\ obs_eq  *)
      
(*  | obs_eq_prf v T s : Σ ;;; [] |- v : T -> *)
(*   Σ ;;; [] |- T : tSort s -> *)
(*   is_prop_sort s -> *)
(*   obs_eq Σ v dummy *)

(* | obs_eq_cstr ind k u args args' T : Σ ;;; [] |- mkApps (tConstruct ind k u) args : T -> *)
(*   computational_type Σ T -> *)
(*   Forall2 (obs_eq Σ) args args' -> *)
(*   obs_eq Σ (mkApps (tConstruct ind k u) args) (mkApps (tConstruct ind k u) args') *)

(* | obs_eq_arrow na f f' T T' : *)
(*     Σ ;;; [] |- f : tProd na T T' -> *)
(*     (forall arg arg', obs_eq Σ arg arg' ->  *)
    
(*     obs_eq Σ f f'.                                                            *)

Record extraction_post (Σ : global_context) (Σ' : EAst.global_context) (t : term) (t' : E.term) (v : term) : Prop :=
  { extr_value : E.term;
    extr_eval : EWcbvEval.eval Σ' t' extr_value
    (* extr_equiv : obs_eq Σ v extr_value *) }.

(** The extraction correctness theorem we conjecture. *)

Definition erasure_correctness :=
  forall Σ t T, extraction_pre Σ t T ->
  forall v, eval Σ [] t v ->
     EWcbvEval.eval (extract_global Σ) (extract Σ [] t) (extract Σ [] v).
      
(* Conjecture erasure_correct : erasure_correctness. *)
