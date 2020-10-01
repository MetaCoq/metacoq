(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     PCUICElimination.
From MetaCoq.Erasure Require EAst ETyping.


Local Existing Instance extraction_checker_flags.

Definition isErasable Σ Γ t := ∑ T, Σ ;;; Γ |- t : T × (isArity T + (∑ u, (Σ ;;; Γ |- T : tSort u) * Universe.is_prop u))%type.

Module E := EAst.


Fixpoint mkAppBox c n :=
  match n with
  | 0 => c
  | S n => mkAppBox (E.tApp c E.tBox) n
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
  | erases_tConst : forall (kn : kername) (u : Instance.t),
                    Σ;;; Γ |- tConst kn u ⇝ℇ E.tConst kn
  | erases_tConstruct : forall (kn : inductive) (k : nat) (n : Instance.t),
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

Lemma erases_forall_list_ind
      Σ (P : context -> term -> E.term -> Prop)
      (Hrel : forall Γ i, P Γ (tRel i) (E.tRel i))
      (Hvar : forall Γ n, P Γ (tVar n) (E.tVar n))
      (Hevar : forall Γ m m' l l',
          All2 (erases Σ Γ) l l' ->
          Forall2 (P Γ) l l' ->
          P Γ (tEvar m l) (E.tEvar m' l'))
      (Hlam : forall Γ na b t t',
          Σ;;; (vass na b :: Γ) |- t ⇝ℇ t' ->
          P (vass na b :: Γ) t t' ->
          P Γ (tLambda na b t) (E.tLambda na t'))
      (Hletin : forall Γ na t1 t1' T t2 t2',
          Σ;;; Γ |- t1 ⇝ℇ t1' ->
          P Γ t1 t1' ->
          Σ;;; (vdef na t1 T :: Γ) |- t2 ⇝ℇ t2' ->
          P (vdef na t1 T :: Γ) t2 t2' ->
          P Γ (tLetIn na t1 T t2) (E.tLetIn na t1' t2'))
      (Happ : forall Γ f4 u f' u',
          Σ;;; Γ |- f4 ⇝ℇ f' ->
          P Γ f4 f' -> Σ;;; Γ |- u ⇝ℇ u' ->
          P Γ u u' ->
          P Γ (tApp f4 u) (E.tApp f' u'))
      (Hconst : forall Γ kn u,
          P Γ (tConst kn u) (E.tConst kn))
      (Hconstruct : forall Γ kn k n,
          P Γ (tConstruct kn k n) (E.tConstruct kn k))
      (Hcase : forall Γ ind npar T c brs c' brs',
          PCUICElimination.Informative Σ ind ->
          Σ;;; Γ |- c ⇝ℇ c' ->
          P Γ c c' ->
          All2 (fun x x' => Σ;;; Γ |- x.2 ⇝ℇ x'.2 × x.1 = x'.1) brs brs' ->
          Forall2 (fun br br' => P Γ br.2 br'.2) brs brs' ->
          P Γ (tCase (ind, npar) T c brs) (E.tCase (ind, npar) c' brs'))
      (Hproj : forall Γ p c c',
          let ind := p.1.1 in
          PCUICElimination.Informative Σ ind ->
          Σ;;; Γ |- c ⇝ℇ c' ->
          P Γ c c' ->
          P Γ (tProj p c) (E.tProj p c'))
      (Hfix : forall Γ mfix n mfix',
          All2
            (fun d d' =>
               dname d = E.dname d' ×
               rarg d = E.rarg d' ×
               Σ;;; app_context Γ (PCUICLiftSubst.fix_context mfix) |- dbody d ⇝ℇ E.dbody d')
            mfix mfix' ->
          Forall2 (fun d d' =>
                     P (app_context Γ (PCUICLiftSubst.fix_context mfix))
                       (dbody d)
                       (EAst.dbody d') ) mfix mfix' ->
          P Γ (tFix mfix n) (E.tFix mfix' n))
      (Hcofix : forall Γ mfix n mfix',
          All2
            (fun d d' =>
               dname d = E.dname d' ×
               rarg d = E.rarg d' ×
               Σ;;; app_context Γ (PCUICLiftSubst.fix_context mfix) |- dbody d ⇝ℇ E.dbody d')
            mfix mfix' ->
          Forall2 (fun d d' =>
                     P (app_context Γ (PCUICLiftSubst.fix_context mfix))
                       (dbody d)
                       (EAst.dbody d') ) mfix mfix' ->
          P Γ (tCoFix mfix n) (E.tCoFix mfix' n))
      (Hbox : forall Γ t, isErasable Σ Γ t -> P Γ t E.tBox) :
  forall Γ t t0,
    Σ;;; Γ |- t ⇝ℇ t0 ->
    P Γ t t0.
Proof.
  fix f 4.
  intros Γ t et er.
  move f at top.
  destruct er;
    try solve [match goal with
    | [H: _ |- _] => apply H
    end; auto].
  - apply Hevar; [assumption|].
    revert l l' X.
    fix f' 3.
    intros l l' [].
    + now constructor.
    + constructor; [now apply f|now apply f'].
  - apply Hcase; try assumption.
    + now apply f.
    + revert brs brs' X.
      fix f' 3.
      intros brs brs' []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - apply Hfix; try assumption.
    revert X.
    generalize mfix at 1 3.
    intros mfix_gen.
    revert mfix mfix'.
    fix f' 3.
    intros mfix mfix' []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - apply Hcofix; try assumption.
    revert X.
    generalize mfix at 1 3.
    intros mfix_gen.
    revert mfix mfix'.
    fix f' 3.
    intros mfix mfix' []; [now constructor|].
    constructor; [now apply f|now apply f'].
Defined.

Definition erases_constant_body (Σ : global_env_ext) (cb : constant_body) (cb' : E.constant_body) :=
  match cst_body cb, E.cst_body cb' with
  | Some b, Some b' => erases Σ [] b b'
  | None, None => True
  | _, _ => False
  end.

Definition erases_one_inductive_body (Σ : global_env_ext) (npars : nat) (arities : context) (oib : one_inductive_body) (oib' : E.one_inductive_body) :=
  let decty := option_get ([], tRel 0) (decompose_prod_n_assum [] npars oib.(ind_type)) in
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
    erases_global_decls ((kn, ConstantDecl cb) :: Σ) ((kn, E.ConstantDecl cb') :: Σ')
| erases_global_ind Σ univs mib mib' kn Σ' :
    erases_mutual_inductive_body (Σ, univs) mib mib' ->
    erases_global_decls Σ Σ' ->
    erases_global_decls ((kn, InductiveDecl mib) :: Σ) ((kn, E.InductiveDecl mib') :: Σ').

Definition erases_global Σ Σ' := erases_global_decls Σ Σ'.

(* For erasure evaluation correctness we do not need the full global
   environment to be erased, rather only (constant) dependencies of
   terms need to be there. *)
Inductive erases_deps (Σ : global_env) (Σ' : E.global_declarations) : E.term -> Prop :=
| erases_deps_tBox : erases_deps Σ Σ' E.tBox
| erases_deps_tRel i : erases_deps Σ Σ' (E.tRel i)
| erases_deps_tVar n : erases_deps Σ Σ' (E.tVar n)
| erases_deps_tEvar m l :
    Forall (erases_deps Σ Σ') l ->
    erases_deps Σ Σ' (E.tEvar m l)
| erases_deps_tLambda na body :
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (E.tLambda na body)
| erases_deps_tLetIn na val body :
    erases_deps Σ Σ' val ->
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (E.tLetIn na val body)
| erases_deps_tApp hd arg :
    erases_deps Σ Σ' hd ->
    erases_deps Σ Σ' arg ->
    erases_deps Σ Σ' (E.tApp hd arg)
| erases_deps_tConst kn cb cb' :
    PCUICTyping.declared_constant Σ kn cb ->
    ETyping.declared_constant Σ' kn cb' ->
    erases_constant_body (Σ, cst_universes cb) cb cb' ->
    (forall body, E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
    erases_deps Σ Σ' (E.tConst kn)
| erases_deps_tConstruct ind c :
    erases_deps Σ Σ' (E.tConstruct ind c)
| erases_deps_tCase p discr brs :
    erases_deps Σ Σ' discr ->
    Forall (fun br => erases_deps Σ Σ' br.2) brs ->
    erases_deps Σ Σ' (E.tCase p discr brs)
| erases_deps_tProj p t :
    erases_deps Σ Σ' t ->
    erases_deps Σ Σ' (E.tProj p t)
| erases_deps_tFix defs i :
    Forall (fun d => erases_deps Σ Σ' (E.dbody d)) defs ->
    erases_deps Σ Σ' (E.tFix defs i)
| erases_deps_tCoFix defs i :
    Forall (fun d => erases_deps Σ Σ' (E.dbody d)) defs ->
    erases_deps Σ Σ' (E.tCoFix defs i).

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
  | ConstantDecl cb => option_is_none cb.(cst_body)
  | InductiveDecl ind => false
  end.

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.
  (* List.forallb (fun g => negb (is_axiom_decl g)) Σ. *)

Definition computational_ind Σ ind :=
  let 'mkInd mind n := ind in
  let mib := lookup_env Σ mind in
  match mib with
  | Some (InductiveDecl decl) =>
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
