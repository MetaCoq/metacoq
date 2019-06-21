
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

<<<<<<< HEAD
Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

Parameter is_type_or_proof : forall (Sigma : global_context) (Gamma : context) (t : PCUICAst.term), bool.
From MetaCoq.PCUIC Require Import PCUICTyping.

Definition Is_Type_or_Proof Σ Γ t := ∑ T, Σ ;;; Γ |- t : T × (isArity T + (∑ u, (Σ ;;; Γ |- T : tSort u) * is_prop_sort u))%type.

Axiom is_type_or_proof_spec : forall (Sigma : global_context) (Gamma : context) (t : PCUICAst.term) T,
    Sigma ;;; Gamma |- t : T -> (is_type_or_proof Sigma Gamma t = true) <~> Is_Type_or_Proof Sigma Gamma t.

(* Section IsType. *)
(*   Context {F : Fuel}. *)
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
(*        ret (Universe.is_prop s). *)
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
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
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
      (* if is_box c' then *)
      (*   match brs with *)
      (*   | (n, x) :: _ => *)
      (*     let x' := extract Σ Γ x in *)
      (*     Ret (mkAppBox x' n) (* Singleton elimination *) *)
      (*   | nil => *)
      (*     Ret (E.tCase ip c' nil) (* Falsity elimination *) *)
      (*   end *)
      (* else *)
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
  Ret {| E.cst_body := body; |}.

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
  let ctors := map (fun '(x, y, z) => let y' := Ret (extract Σ arities y) in Ret (x, y', z)) oib.(ind_ctors) in
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  let projs := map (fun '(x, y) => let y' := Ret (extract Σ [] y) in Ret (x, y')) oib.(ind_projs) in
  Ret {| E.ind_name := oib.(ind_name);
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

Inductive erases (Σ : global_context) (Γ : context) : term -> E.term -> Prop :=
| erases_tRel i :
    erases Σ Γ (tRel i) (E.tRel i)
| erases_tVar n :
    erases Σ Γ (tVar n) (E.tVar n)
| erases_tEvar m m' l l' :
    All2 (erases Σ Γ) l l' ->
    erases Σ Γ (tEvar m l) (E.tEvar m' l')
| erases_tLambda na b t t' :
    erases Σ (vass na b :: Γ) t t' ->
    erases Σ Γ (tLambda na b t) (E.tLambda na t')
| erases_tLetIn na t1 t1' T t2 t2'  :
    erases Σ Γ t1 t1' ->
    erases Σ (vdef na t1 T :: Γ) t2 t2' ->
    erases Σ Γ (tLetIn na t1 T t2) (E.tLetIn na t1' t2')
| erases_tApp f u f' u' :
    erases Σ Γ f f' ->
    erases Σ Γ u u' ->
    erases Σ Γ (tApp f u) (E.tApp f' u') 
| erases_tConst kn u :
    erases Σ Γ (tConst kn u) (E.tConst kn)
| erases_tConstruct kn k n :
    erases Σ Γ (tConstruct kn k n) (E.tConstruct kn k)
| erases_tCase1 ip T c brs c' brs' :
    erases Σ Γ c c' ->
    All2 (fun x x' => erases Σ Γ (snd x) (snd x') × fst x = fst x') brs brs' ->
    erases Σ Γ (tCase ip T c brs) (E.tCase ip c' brs')
(* | erases_tCase2 ip T c : *)
(*     erases Σ Γ c E.tBox -> *)
(*     erases Σ Γ (tCase ip T c []) (E.tCase ip E.tBox []) *)
(* | erases_tCase3 ip T c brs n x x' : *)
(*     erases Σ Γ c E.tBox -> *)
(*     erases Σ Γ x x' -> *)
(*     erases Σ Γ (tCase ip T c ((n, x) :: brs)) (mkAppBox x' n) *)
| erases_tProj p c c' :
    erases Σ Γ c c' ->
    erases Σ Γ (tProj p c) (E.tProj p c')
| erases_tFix mfix n mfix' :
    All2 (fun d d' => dname d = E.dname d' ×
                   rarg d = E.rarg d' ×
                   erases Σ (Γ ,,, PCUICLiftSubst.fix_context mfix) (dbody d) (E.dbody d')) mfix mfix' ->
    erases Σ Γ (tFix mfix n) (E.tFix mfix' n)
| erases_tCoFix mfix n mfix' :
    All2 (fun d d' => dname d = E.dname d' ×
                   rarg d = E.rarg d' ×
                   erases Σ (Γ ,,, PCUICLiftSubst.fix_context mfix) (dbody d) (E.dbody d')) mfix mfix' ->
    erases Σ Γ (tCoFix mfix n) (E.tCoFix mfix' n)
(* | erases_tSort u : erases Σ Γ (tSort u) E.tBox *)
(* | erases_tInd i u : erases Σ Γ (tInd i u) (E.tBox) *)
| erases_box t :
    Is_Type_or_Proof Σ Γ t ->              
    erases Σ Γ t E.tBox
.

Notation "Σ ;;; Γ |- s ⇝ℇ t" := (erases Σ Γ s t) (at level 50, Γ, s, t at next level) : type_scope.

Definition erases_constant_body (Σ : global_context) (cb : constant_body) (cb' : E.constant_body) :=
  match cst_body cb, E.cst_body cb' with
  | Some b, Some b' => erases Σ [] b b'
  | None, None => True
  | _, _ => False
  end.

Definition erases_one_inductive_body (Σ : global_context) (npars : nat) (arities : context) (oib : one_inductive_body) (oib' : E.one_inductive_body) :=
  let decty := opt_def (decompose_prod_n_assum [] npars oib.(ind_type)) ([], tRel 0) in
  let '(params, arity) := decty in
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  Forall2 (fun '((i,t), n) '((i',t'), n') => erases Σ arities t t' /\ n = n' /\ i = i') oib.(ind_ctors) oib'.(E.ind_ctors) /\
  Forall2 (fun '(i,t) '(i',t') => erases Σ [] t t' /\ i = i') oib.(ind_projs) oib'.(E.ind_projs) /\
  oib'.(E.ind_name) = oib.(ind_name) /\
  oib'.(E.ind_kelim) = oib.(ind_kelim).

Definition erases_mutual_inductive_body (Σ : global_context) (mib : mutual_inductive_body) (mib' : E.mutual_inductive_body) :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  Forall2 (erases_one_inductive_body Σ mib.(ind_npars) arities) bds (mib'.(E.ind_bodies)) /\
  mib.(ind_npars) = mib'.(E.ind_npars).
  
Inductive erases_global_decls : constraints -> global_declarations -> E.global_declarations -> Prop :=
| erases_global_nil univ : erases_global_decls univ [] []
| erases_global_cnst Σ univs cb cb' kn Σ' :
    erases_constant_body (Σ, univs) cb cb' ->
    erases_global_decls univs Σ Σ' ->
    erases_global_decls univs (ConstantDecl kn cb :: Σ) (E.ConstantDecl kn cb' :: Σ')
| erases_global_ind Σ univs mib mib' kn Σ' :
    erases_mutual_inductive_body (Σ, univs) mib mib' ->
    erases_global_decls univs Σ Σ' ->
    erases_global_decls univs (InductiveDecl kn mib :: Σ) (E.InductiveDecl kn mib' :: Σ').

Definition erases_global '(Σ, univs) Σ' := erases_global_decls univs Σ Σ'.

(** * Erasure correctness
    
    The statement below expresses that any well-typed term's
    extraction has the same operational semantics as its source, under
    a few conditions:

    - The terms has to be locally closed, otherwise evaluation could get 
      stuck on free variables. Typing under an empty context ensures that.
    - The global environment is axiom-free, for the same reason.
    - The object is of inductive type, or more generally a function resulting 
      ultimately in an inductive value when applied.

 *)

Fixpoint inductive_arity (t : term) :=
  match t with
  | tApp f _ | f =>
    match f with
    | tInd ind u => Some ind
    | _ => None
    end
  end.

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

(* (** The precondition on the extraction theorem. *) *)

(* Record extraction_pre (Σ : global_context) t T := *)
(*   { extr_typed : Σ ;;; [] |- t : T; *)
(*     extr_env_axiom_free : axiom_free (fst Σ); *)
(*     extr_env_wf : wf Σ ; *)
(*     (* extr_computational_type : computational_type Σ T *) }. *)

(* (** The extraction correctness theorem we conjecture. *) *)

(* Definition erasure_correctness := *)
(*   forall Σ t T, extraction_pre Σ t T -> *)
(*   forall v, eval Σ [] t v -> *)
(*      EWcbvEval.eval (extract_global Σ) (extract Σ [] t) (extract Σ [] v). *)
      
(* (* Conjecture erasure_correct : erasure_correctness. *) *)
