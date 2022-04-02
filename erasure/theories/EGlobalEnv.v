(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils BasicAst Reflect.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst EReflect ECSubst.
Require Import ssreflect.
Import MCMonadNotation.

(** * Global environments 

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)
(** ** Environment lookup *)

Fixpoint lookup_env (Σ : global_context) id : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if eq_kername id hd.1 then Some hd.2
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_context) id decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl decl).

Definition declared_inductive Σ ind mdecl decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
  declared_inductive Σ (fst cstr) mdecl idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

Definition declared_projection Σ (proj : projection) mdecl idecl pdecl : Prop :=
  declared_inductive Σ (fst (fst proj)) mdecl idecl /\
  List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl.

Lemma elookup_env_cons_fresh {kn d Σ kn'} : 
  kn <> kn' ->
  EGlobalEnv.lookup_env ((kn, d) :: Σ) kn' = EGlobalEnv.lookup_env Σ kn'.
Proof.
  simpl. change (eq_kername kn' kn) with (eqb kn' kn).
  destruct (eqb_spec kn' kn). subst => //. auto. 
Qed.

Section Lookups.
  Context (Σ : global_declarations).

  Definition lookup_constant kn : option constant_body :=
    decl <- lookup_env Σ kn;; 
    match decl with
    | ConstantDecl cdecl => ret cdecl
    | InductiveDecl mdecl => None
    end.

  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- lookup_env Σ kn;; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).
  
  Definition lookup_inductive_pars kn : option nat := 
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_npars).
  
  Definition lookup_constructor kn c : option (mutual_inductive_body * one_inductive_body * (ident * nat)) :=
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).
  
  Definition lookup_constructor_pars_args kn c : option (nat * nat) := 
    '(mdecl, idecl, cdecl) <- lookup_constructor kn c ;;
    ret (mdecl.(ind_npars), cdecl.2).
End Lookups.

(** Knowledge of propositionality status of an inductive type and parameters *)

Definition inductive_isprop_and_pars Σ ind :=
  match lookup_env Σ (inductive_mind ind) with
  | Some (InductiveDecl mdecl) =>
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with 
    | Some idecl => Some (idecl.(ind_propositional), mdecl.(ind_npars))
    | None => None
    end
  | _ => None
  end.

Definition closed_decl (d : EAst.global_decl) := 
  match d with
  | EAst.ConstantDecl cb => 
    option_default (ELiftSubst.closedn 0) (EAst.cst_body cb) true
  | EAst.InductiveDecl _ => true
  end.

Definition closed_env (Σ : EAst.global_declarations) := 
  forallb (test_snd closed_decl) Σ.
  
(** Environment extension and uniqueness of declarations in well-formed global environments *)

Definition extends (Σ Σ' : global_declarations) := ∑ Σ'', Σ' = (Σ'' ++ Σ)%list.

Definition fresh_global kn (Σ : global_declarations) :=
  Forall (fun x => x.1 <> kn) Σ.

Lemma lookup_env_Some_fresh {Σ c decl} :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  case: eqb_spec; intros e; subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.


(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor_app_or_box t :=
  match t with
  | tBox => true
  | a =>
    let (f, a) := decompose_app a in
    match f with
    | tConstruct _ _ => true
    | _ => false
    end
  end.

Definition is_nth_constructor_app_or_box n ts :=
  match List.nth_error ts n with
  | Some a => is_constructor_app_or_box a
  | None => false
  end.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Definition tDummy := tVar "".

Definition iota_red npar args (br : list name * term) :=
  substl (List.rev (List.skipn npar args)) br.2.

Definition isSome {A} (o : option A) := 
  match o with 
  | None => false
  | Some _ => true
  end.

Class ETermFlags := 
  { has_tBox : bool
  ; has_tRel : bool
  ; has_tVar : bool
  ; has_tEvar : bool
  ; has_tLambda : bool
  ; has_tLetIn : bool
  ; has_tApp : bool
  ; has_tConst : bool
  ; has_tConstruct : bool
  ; has_tCase : bool
  ; has_tProj : bool
  ; has_tFix : bool
  ; has_tCoFix : bool
  }.

Class EEnvFlags := {
  has_axioms : bool;
  has_cstr_params : bool;
  term_switches :> ETermFlags }.
  
Definition all_term_flags := 
  {| has_tBox := true
    ; has_tRel := true
    ; has_tVar := true
    ; has_tEvar := true
    ; has_tLambda := true
    ; has_tLetIn := true
    ; has_tApp := true
    ; has_tConst := true
    ; has_tConstruct := true
    ; has_tCase := true
    ; has_tProj := true
    ; has_tFix := true
    ; has_tCoFix := true
  |}.

Definition all_env_flags := 
  {| has_axioms := true; 
     term_switches := all_term_flags;
     has_cstr_params := true |}.
    
Section wf.
  
  Context {sw  : EEnvFlags}.
  Variable Σ : global_context.

  (* a term term is wellformed if
    - it is closed up to k,
    - it only contains constructos as indicated by sw,
    - all occuring constructors are defined,
    - all occuring constants are defined, and
    - if has_axioms is false, all occuring constants have bodies *)
  
  Fixpoint wellformed k (t : term) : bool :=
    match t with
    | tRel i => has_tRel && Nat.ltb i k
    | tEvar ev args => has_tEvar && List.forallb (wellformed k) args
    | tLambda _ M => has_tLambda && wellformed (S k) M
    | tApp u v => has_tApp && wellformed k u && wellformed k v
    | tLetIn na b b' => has_tLetIn && wellformed k b && wellformed (S k) b'
    | tCase ind c brs => has_tCase && 
      let brs' := List.forallb (fun br => wellformed (#|br.1| + k) br.2) brs in
      isSome (lookup_inductive Σ ind.1) && wellformed k c && brs'
    | tProj p c => has_tProj && isSome (lookup_inductive Σ p.1.1) && wellformed k c
    | tFix mfix idx => has_tFix &&
      let k' := List.length mfix + k in
      List.forallb (test_def (wellformed k')) mfix
    | tCoFix mfix idx => has_tCoFix &&
      let k' := List.length mfix + k in
      List.forallb (test_def (wellformed k')) mfix
    | tBox => has_tBox
    | tConst kn => has_tConst && 
      match lookup_constant Σ kn with
      | Some d => has_axioms || isSome d.(cst_body)
      | _ => false 
      end
    | tConstruct ind c => has_tConstruct && isSome (lookup_constructor Σ ind c)
    | tVar _ => has_tVar
    end.

End wf.

Definition wf_global_decl {sw : EEnvFlags} Σ d : bool :=
  match d with
  | ConstantDecl cb => option_default (fun b => wellformed Σ 0 b) cb.(cst_body) has_axioms
  | InductiveDecl idecl => has_cstr_params || (idecl.(ind_npars) == 0)
  end.

Inductive wf_glob {efl : EEnvFlags} : global_declarations -> Prop :=
| wf_glob_nil : wf_glob []
| wf_glob_cons kn d Σ : 
  wf_glob Σ ->
  wf_global_decl Σ d ->
  fresh_global kn Σ ->
  wf_glob ((kn, d) :: Σ).
Derive Signature for wf_glob.

Implicit Types (efl : EEnvFlags).

Lemma extends_lookup {efl} {Σ Σ' c decl} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *.
  - simpl. auto.
  - specialize (IHΣ'' c decl). forward IHΣ''.
    + now inv wfΣ'.
    + intros HΣ. specialize (IHΣ'' HΣ).
      inv wfΣ'. simpl in *.
      case: eqb_spec; intros e; subst; auto.
      apply lookup_env_Some_fresh in IHΣ''; contradiction.
Qed.

Lemma extends_is_propositional {efl} {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind b, inductive_isprop_and_pars Σ ind = Some b -> inductive_isprop_and_pars Σ' ind = Some b.
Proof.
  intros wf ex ind b.
  rewrite /inductive_isprop_and_pars.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).
Qed.

