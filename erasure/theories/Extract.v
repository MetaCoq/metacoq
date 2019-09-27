(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICElimination.
From MetaCoq.Erasure Require EAst ELiftSubst ETyping.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Local Existing Instance extraction_checker_flags.

Definition isErasable Σ Γ t := ∑ T, Σ ;;; Γ |- t : T × (isArity T + (∑ u, (Σ ;;; Γ |- T : tSort u) * is_prop_sort u))%type.

Module E := EAst.
Local Notation Ret t := t.


Fixpoint mkAppBox c n :=
  match n with
  | 0 => c
  | S n => mkAppBox (E.tApp c E.tBox) n
  end.

Definition opt_def {A} (a : option A) (e : A) : A :=
  match a with
  | Some x => Ret x
  | None => e
  end.

Reserved Notation "Σ ;;; Γ |- s ⇝ℇ t" (at level 50, Γ, s, t at next level).

Inductive erases (Σ : global_env_ext) (Γ : context) : term -> E.term -> Prop :=
    erases_tRel : forall i : nat, Σ;;; Γ |- tRel i ⇝ℇ E.tRel i
  | erases_tVar : forall n : ident, Σ;;; Γ |- tVar n ⇝ℇ E.tVar n
  | erases_tEvar : forall (m m' : nat) (l : list term) (l' : list E.term),
                   All2 (erases Σ Γ) l l' -> Σ;;; Γ |- tEvar m l ⇝ℇ E.tEvar m' l'
  | erases_tLambda : forall (na : name) (b t : term) (t' : E.term),
                     Σ;;; (vass na b :: Γ) |- t ⇝ℇ t' ->
                     Σ;;; Γ |- tLambda na b t ⇝ℇ E.tLambda na t'
  | erases_tLetIn : forall (na : name) (t1 : term) (t1' : E.term) 
                      (T t2 : term) (t2' : E.term),
                    Σ;;; Γ |- t1 ⇝ℇ t1' ->
                    Σ;;; (vdef na t1 T :: Γ) |- t2 ⇝ℇ t2' ->
                    Σ;;; Γ |- tLetIn na t1 T t2 ⇝ℇ E.tLetIn na t1' t2'
  | erases_tApp : forall (f u : term) (f' u' : E.term),
                  Σ;;; Γ |- f ⇝ℇ f' ->
                  Σ;;; Γ |- u ⇝ℇ u' -> Σ;;; Γ |- tApp f u ⇝ℇ E.tApp f' u'
  | erases_tConst : forall (kn : kername) (u : universe_instance),
                    Σ;;; Γ |- tConst kn u ⇝ℇ E.tConst kn
  | erases_tConstruct : forall (kn : inductive) (k : nat) (n : universe_instance),
                        Σ;;; Γ |- tConstruct kn k n ⇝ℇ E.tConstruct kn k
  | erases_tCase1 : forall (ind : inductive) (npar : nat) (T c : term)
                      (brs : list (nat × term)) (c' : E.term) 
                      (brs' : list (nat × E.term)),
                    Informative Σ ind ->
                    Σ;;; Γ |- c ⇝ℇ c' ->
                    All2
                      (fun (x : nat × term) (x' : nat × E.term) =>
                       Σ;;; Γ |- snd x ⇝ℇ snd x' × fst x = fst x') brs brs' ->
                    Σ;;; Γ |- tCase (ind, npar) T c brs ⇝ℇ E.tCase (ind, npar) c' brs'
  | erases_tProj : forall (p : (inductive × nat) × nat) (c : term) (c' : E.term),
                   let ind := fst (fst p) in
                   Informative Σ ind ->
                   Σ;;; Γ |- c ⇝ℇ c' -> Σ;;; Γ |- tProj p c ⇝ℇ E.tProj p c'
  | erases_tFix : forall (mfix : mfixpoint term) (n : nat) (mfix' : list (E.def E.term)),
                  All2
                    (fun (d : def term) (d' : E.def E.term) =>
                     dname d = E.dname d'
                     × rarg d = E.rarg d'
                       × Σ;;; Γ ,,, PCUICLiftSubst.fix_context mfix |- 
                         dbody d ⇝ℇ E.dbody d') mfix mfix' ->
                  Σ;;; Γ |- tFix mfix n ⇝ℇ E.tFix mfix' n
  | erases_tCoFix : forall (mfix : mfixpoint term) (n : nat) (mfix' : list (E.def E.term)),
                    All2
                      (fun (d : def term) (d' : E.def E.term) =>
                       dname d = E.dname d'
                       × rarg d = E.rarg d'
                         × Σ;;; Γ ,,, PCUICLiftSubst.fix_context mfix |- 
                           dbody d ⇝ℇ E.dbody d') mfix mfix' ->
                    Σ;;; Γ |- tCoFix mfix n ⇝ℇ E.tCoFix mfix' n
  | erases_box : forall t : term, isErasable Σ Γ t -> Σ;;; Γ |- t ⇝ℇ E.tBox where "Σ ;;; Γ |- s ⇝ℇ t" := (erases Σ Γ s t).

Definition erases_constant_body (Σ : global_env_ext) (cb : constant_body) (cb' : E.constant_body) :=
  match cst_body cb, E.cst_body cb' with
  | Some b, Some b' => erases Σ [] b b'
  | None, None => True
  | _, _ => False
  end.

Definition erases_one_inductive_body (Σ : global_env_ext) (npars : nat) (arities : context) (oib : one_inductive_body) (oib' : E.one_inductive_body) :=
  let decty := opt_def (decompose_prod_n_assum [] npars oib.(ind_type)) ([], tRel 0) in
  let '(params, arity) := decty in
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  Forall2 (fun '((i,t), n) '((i',t'), n') => erases Σ arities t t' /\ n = n' /\ i = i') oib.(ind_ctors) oib'.(E.ind_ctors) /\
  Forall2 (fun '(i,t) '(i',t') => erases Σ [] t t' /\ i = i') oib.(ind_projs) oib'.(E.ind_projs) /\
  oib'.(E.ind_name) = oib.(ind_name) /\
  oib'.(E.ind_kelim) = oib.(ind_kelim).

Definition erases_mutual_inductive_body (Σ : global_env_ext) (mib : mutual_inductive_body) (mib' : E.mutual_inductive_body) :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  Forall2 (erases_one_inductive_body Σ mib.(ind_npars) arities) bds (mib'.(E.ind_bodies)) /\
  mib.(ind_npars) = mib'.(E.ind_npars).
  
Inductive erases_global_decls : global_env -> E.global_declarations -> Prop :=
| erases_global_nil : erases_global_decls [] []
| erases_global_cnst Σ cb cb' kn Σ' :
    erases_constant_body (Σ, cst_universes cb) cb cb' ->
    erases_global_decls Σ Σ' ->
    erases_global_decls (ConstantDecl kn cb :: Σ) (E.ConstantDecl kn cb' :: Σ')
| erases_global_ind Σ univs mib mib' kn Σ' :
    erases_mutual_inductive_body (Σ, univs) mib mib' ->
    erases_global_decls Σ Σ' ->
    erases_global_decls (InductiveDecl kn mib :: Σ) (E.InductiveDecl kn mib' :: Σ').

Definition erases_global Σ Σ' := erases_global_decls Σ Σ'.

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
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.
  (* List.forallb (fun g => negb (is_axiom_decl g)) Σ. *)

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
