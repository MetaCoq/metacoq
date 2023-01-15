(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Primitive.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases.

Import MCMonadNotation.

(* TODO: remove this export *)
From MetaCoq Require Export LibHypsNaming.

Require Import ssreflect ssrbool.
Require Import Equations.Type.Relation.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of PCUIC terms.
  These come with many additional functions, to define the reduction operations,
  deal with arities, declarations in the environment etc...

 *)

Fixpoint isArity T :=
  match T with
  | tSort u => True
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => False
  end.

Definition type_of_constructor mdecl (cdecl : constructor_body) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u (cstr_type cdecl)).

(** ** Typing relation *)

Include PCUICEnvTyping.

(* AXIOM Postulate existence of a guard condition checker *)

Inductive FixCoFix : Type := Fix | CoFix.

Class GuardChecker :=
{ (* guard check for both fixpoints (Fix) and cofixpoints (CoFix)  *)
  guard : FixCoFix -> global_env_ext -> context -> mfixpoint term -> Prop ;
}.

Axiom guard_checking : GuardChecker.
#[global]
Existing Instance guard_checking.

Definition fix_guard := guard Fix.
Definition cofix_guard := guard CoFix.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition isFinite (r : recursivity_kind) :=
  match r with
  | Finite => true
  | _ => false
  end.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind
  (lookup: kername -> option global_decl) ind r :=
  match lookup ind with
  | Some (InductiveDecl mib) => ReflectEq.eqb mib.(ind_finite) r
  | _ => false
  end.

Definition check_one_fix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  match nth_error (List.rev (smash_context [] ctx)) arg with
  | Some argd =>
    let (hd, args) := decompose_app argd.(decl_type) in
    match destInd hd with
    | Some (mkInd mind _, u) => Some mind
    | None => None (* Not recursive on an inductive type *)
    end
  | None => None (* Recursive argument not found *)
  end.

Definition wf_fixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive fixpoints are all on the same mututal
       inductive block *)
    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind Finite
  | _ => false
  end.

Definition wf_fixpoint (Σ : global_env) := wf_fixpoint_gen (lookup_env Σ).

Definition check_one_cofix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  let (hd, args) := decompose_app ty in
  match destInd hd with
  | Some (mkInd ind _, u) => Some ind
  | None => None (* Not recursive on an inductive type *)
  end.

Definition wf_cofixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive cofixpoints are all producing
       coinductives in the same mututal coinductive block *)
    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind CoFinite
  | _ => false
  end.

Definition wf_cofixpoint (Σ : global_env) := wf_cofixpoint_gen (lookup_env Σ).

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).

Variant case_side_conditions `{checker_flags} wf_local_fun typing Σ Γ ci p ps mdecl idecl indices predctx :=
| case_side_info
    (eq_npars : mdecl.(ind_npars) = ci.(ci_npar))
    (wf_pred : wf_predicate mdecl idecl p)
    (cons : consistent_instance_ext Σ (ind_universes mdecl) p.(puinst))
    (wf_pctx : wf_local_fun Σ (Γ ,,, predctx))
    (* The predicate context is fixed, it is only used as a cache for information from the
      global environment *)
    (conv_pctx : eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl))
    (allowed_elim : is_allowed_elimination Σ idecl.(ind_kelim) ps)
    (ind_inst : ctx_inst typing Σ Γ (p.(pparams) ++ indices)
                         (List.rev (subst_instance p.(puinst)
                                                   (ind_params mdecl ,,, ind_indices idecl))))
    (not_cofinite : isCoFinite mdecl.(ind_finite) = false).

Variant case_branch_typing `{checker_flags} wf_local_fun typing Σ Γ (ci:case_info) p ps mdecl idecl ptm  brs :=
| case_branch_info
    (wf_brs : wf_branches idecl brs)
    (brs_ty :
       All2i (fun i cdecl br =>
        (* Also a cache, brctxty is built from br.(bcontext) by substituting in the
           parameters and universe instance  *)
                eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
                let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
                (wf_local_fun Σ (Γ ,,, brctxty.1) ×
                ((typing Σ (Γ ,,, brctxty.1) br.(bbody) (brctxty.2)) ×
                (typing Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))))
             0 idecl.(ind_ctors) brs).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel : forall n decl,
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort : forall s,
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Prod : forall na A B s1 s2,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda : forall na A t s1 B,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- tLambda na A t : tProd na A B

| type_LetIn : forall na b B t s1 A,
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App : forall t na A B s u,
    (* Paranoid assumption, allows to show equivalence with template-coq,
       but eventually unnecessary thanks to validity. *)
    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Const : forall cst u decl,
    wf_local Σ Γ ->
    declared_constant Σ cst decl ->
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- tConst cst u : decl.(cst_type)@[u]

| type_Ind : forall ind u mdecl idecl,
    wf_local Σ Γ ->
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tInd ind u : idecl.(ind_type)@[u]

| type_Construct : forall ind i u mdecl idecl cdecl,
    wf_local Σ Γ ->
    declared_constructor Σ (ind, i) mdecl idecl cdecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tConstruct ind i u : type_of_constructor mdecl cdecl (ind, i) u

| type_Case : forall ci p c brs indices ps mdecl idecl,
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    case_side_conditions (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                         mdecl idecl indices predctx  ->
    case_branch_typing (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                        mdecl idecl ptm brs ->
    Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj : forall p c u mdecl idecl cdecl pdecl args,
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) pdecl.(proj_type)@[u]

| type_Fix : forall mfix n decl,
    wf_local Σ Γ ->
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix : forall mfix n decl,
    wf_local Σ Γ ->
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Prim p prim_ty cdecl :
   wf_local Σ Γ ->
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants cdecl ->
   Σ ;;; Γ |- tPrim p : tConst prim_ty []

| type_Cumul : forall t A B s,
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <=s B ->
    Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).

Lemma meta_conv {cf} {Σ Γ t A B} :
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros h []; assumption.
Qed.

Lemma meta_conv_term {cf} {Σ Γ t t' A} :
    Σ ;;; Γ |- t : A ->
    t = t' ->
    Σ ;;; Γ |- t' : A.
Proof.
  intros h []. assumption.
Qed.

Lemma meta_conv_all {cf} {Σ Γ t A Γ' t' A'} :
    Σ ;;; Γ |- t : A ->
    Γ = Γ' -> t = t' -> A = A' ->
    Σ ;;; Γ' |- t' : A'.
Proof.
  intros h [] [] []; assumption.
Qed.

(** ** Typechecking of global environments *)

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

Module PCUICTypingDef <: EnvironmentTyping.Typing PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec.

  Definition typing := @typing.

End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  EnvironmentTyping.DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICTermUtils
    PCUICEnvTyping
    PCUICConversion
    PCUICConversionParSpec
    PCUICTypingDef
    PCUICLookup
    PCUICGlobalMaps.
Include PCUICDeclarationTyping.

Inductive welltyped {cf} Σ Γ t : Prop :=
| iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

Arguments iswelltyped {cf Σ Γ t A} h.

Definition isType_welltyped {cf Σ} {Γ T}
  : isType Σ Γ T -> welltyped Σ Γ T.
Proof.
  intros []. now econstructor.
Qed.
Global Hint Resolve isType_welltyped : pcuic.

Definition isWfArity {cf:checker_flags} Σ (Γ : context) T :=
  (isType Σ Γ T × { ctx & { s & (destArity [] T = Some (ctx, s)) } }).

Definition tybranches {cf} Σ Γ ci mdecl idecl p ps ptm n ctors brs :=
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
   (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) *
   (let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    wf_local Σ (Γ,,, brctxty.1)
    × Σ;;; Γ,,, brctxty.1 |- bbody br : brctxty.2
      × Σ;;; Γ,,, brctxty.1 |- brctxty.2 : tSort ps)) n ctors brs.

Definition branches_size {cf} {Σ Γ ci mdecl idecl p ps ptm brs}
   (typing_size : forall Σ Γ t T, Σ ;;; Γ |- t : T -> size)
  {n ctors}
  (a : tybranches Σ Γ ci mdecl idecl p ps ptm n ctors brs) : size :=
  (all2i_size _ (fun i x y p =>
    Nat.max
      (All_local_env_size typing_size _ _ p.2.1)
      (Nat.max (typing_size _ _ _ _ p.2.2.1) (typing_size _ _ _ _ p.2.2.2))) a).

Section CtxInstSize.
  Context {cf} (typing : global_env_ext -> context -> term -> term -> Type)
  (typing_size : forall {Σ Γ t T}, typing Σ Γ t T -> size).

  Fixpoint ctx_inst_size {Σ Γ args Δ} (c : ctx_inst typing Σ Γ args Δ) : size :=
  match c with
  | ctx_inst_nil => 0
  | ctx_inst_ass na t i inst Δ ty ctxi => (typing_size _ _ _ _ ty) + (ctx_inst_size ctxi)
  | ctx_inst_def na b t inst Δ ctxi => S (ctx_inst_size ctxi)
  end.
End CtxInstSize.

Definition typing_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix typing_size 5.
  destruct 1.
  10: destruct c0, c1.
  all: repeat match goal with
           | H : typing _ _ _ _ |- _ => apply typing_size in H
    end;
    match goal with
    | H : All2i _ _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H : _ + _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
  - exact (S (All_local_env_size typing_size _ _ a)).
  - exact (S (All_local_env_size typing_size _ _ a)).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (Nat.max (All_local_env_size typing_size _ _ wf_pctx)
      (Nat.max (ctx_inst_size _ typing_size ind_inst)
        (Nat.max d2 (Nat.max d3 (branches_size typing_size brs_ty)))))).
  - exact (S (Nat.max (Nat.max (All_local_env_size typing_size _ _ a)
    (all_size _ (fun x p => (infer_sort_size (typing_sort_size typing_size)) Σ _ _ p) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ p) a1))).
  - exact (S (Nat.max (Nat.max (All_local_env_size typing_size _ _ a)
    (all_size _ (fun x p => (infer_sort_size (typing_sort_size typing_size)) Σ _ _ p) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ p) a1))).
  - exact (S (All_local_env_size typing_size _ _ a)).
Defined.

Lemma typing_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; try destruct c0, c1; simpl; try lia.
Qed.

Fixpoint global_declarations_size (Σ : global_declarations) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (global_declarations_size Σ)
  end.

Definition globenv_size (Σ : global_env) : size :=
  global_declarations_size Σ.(declarations).

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

(** We make these well-formedness conditions type-classes as they are genrally
    globally available. *)
Definition wf `{checker_flags} := Forall_decls_typing typing.
Existing Class wf.
#[global]
Hint Mode wf + + : typeclass_intances.

Lemma wf_env_non_var_levels (Σ : global_env) `{checker_flags} (hΣ : ∥ wf Σ ∥) :
  LS.For_all (negb ∘ Level.is_var) (PCUICLookup.global_levels Σ).
Proof. now destruct hΣ as [[[_ [? _]] _]]. Qed.

Definition wf_ext `{checker_flags} := on_global_env_ext cumulSpec0 (lift_typing typing).
Existing Class wf_ext.
#[global]
Hint Mode wf_ext + + : typeclass_intances.

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. intro H; apply H. Qed.
#[global]
Existing Instance wf_ext_wf.
Coercion wf_ext_wf : wf_ext >-> wf.
#[global]
Hint Resolve wf_ext_wf : core.

Lemma wf_ext_consistent {cf:checker_flags} Σ :
  wf_ext Σ -> consistent Σ.
Proof. intros [_ [_ [_ [? _]]]]; assumption. Qed.
#[global]
Hint Resolve wf_ext_consistent : core.

Lemma wf_local_app_l `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
Proof.
  induction Γ'. auto.
  simpl. intros H'; inv H'; eauto.
Defined.
#[global] Hint Immediate wf_local_app_l : wf.

Lemma typing_wf_local `{checker_flags} {Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_local Σ Γ.
Proof.
  induction 1; eauto using wf_local_app_l.
Defined.

#[global]
Hint Extern 4 (wf_local _ ?Γ) =>
  match goal with
  | [ H : typing _ _ _ _ |- _ ] => exact (typing_wf_local H)
  | [ H : PCUICTypingDef.typing _ _ _ _ _ |- _ ] => exact (typing_wf_local H)
  end : pcuic.

#[global]
Hint Resolve typing_wf_local : wf.

Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) (PΓ : forall Σ Γ, Type) :=
  forall Σ (wfΣ : wf Σ.1) Γ t T (ty : Σ ;;; Γ |- t : T),
    Forall_decls_typing P Σ.1 *
    (PΓ Σ Γ * P Σ Γ t T).

Lemma env_prop_typing `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma type_Prop_wf `{checker_flags} Σ Γ : wf_local Σ Γ -> Σ ;;; Γ |- tSort Universe.lProp : tSort Universe.type1.
Proof.
  repeat constructor; auto.
Defined.

Lemma env_prop_wf_local `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ), PΓ Σ Γ.
Proof. intros.
  pose (type_Prop_wf _ _ wfΓ).
  now destruct (X _ wfΣ _ _ _ t) as [? [? ?]].
Qed.

Lemma type_Prop `{checker_flags} Σ : Σ ;;; [] |- tSort Universe.lProp : tSort Universe.type1.
  repeat constructor.
Defined.

Lemma env_prop_sigma `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall (Σ : global_env) (wfΣ : wf Σ), Forall_decls_typing P Σ.
Proof.
  intros. red in X. eapply (X (empty_ext Σ)).
  apply wfΣ.
  apply type_Prop.
Defined.

Lemma type_Cumul' {cf:checker_flags} {Σ Γ t} T {T'} :
  Σ ;;; Γ |- t : T ->
  isType Σ Γ T' ->
  Σ ;;; Γ |- T <=s T' ->
  Σ ;;; Γ |- t : T'.
Proof.
  intros Ht [s Hs] cum.
  eapply type_Cumul; eauto.
Qed.

Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
  All_local_env_size (@typing_size _) Σ _ (wf_local_app_l _ _ _ Hwf) <=
  All_local_env_size (@typing_size _) Σ _ Hwf.
Proof.
  induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
  depelim Hwf.
  - specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r; cbn. lia.
  - specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. cbn. lia.
Qed.

Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  All_local_env_size (@typing_size _) Σ _ (typing_wf_local d) < typing_size d.
Proof.
  induction d; try destruct c0, c1; simpl;
  change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
  (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size H); try lia.
Qed.

Lemma wf_local_inv `{checker_flags} {Σ Γ'} (w : wf_local Σ Γ') :
  forall d Γ,
    Γ' = d :: Γ ->
    ∑ w' : wf_local Σ Γ,
      match d.(decl_body) with
      | Some b =>
        ∑ u (ty : Σ ;;; Γ |- b : d.(decl_type)),
          { ty' : Σ ;;; Γ |- d.(decl_type) : tSort u |
            All_local_env_size (@typing_size _) Σ _ w' <
            All_local_env_size (@typing_size _) _ _ w /\
            typing_size ty <= All_local_env_size (@typing_size _) _ _ w /\
            typing_size ty' <= All_local_env_size (@typing_size _) _ _ w }

      | None =>
        ∑ u,
          { ty : Σ ;;; Γ |- d.(decl_type) : tSort u |
            All_local_env_size (@typing_size _) Σ _ w' <
            All_local_env_size (@typing_size _) _ _ w /\
            typing_size ty <= All_local_env_size (@typing_size _) _ _ w }
      end.
Proof.
  intros d Γ.
  destruct w.
  - simpl. congruence.
  - intros [=]. subst d Γ0.
    exists w. simpl. destruct l. exists x. exists t0. pose (typing_size_pos t0).
    cbn. split.
    + lia.
    + auto with arith.
  - intros [=]. subst d Γ0.
    exists w. simpl. simpl in l. destruct l as [u h].
    simpl in l0.
    exists u, l0, h. cbn.
    pose (typing_size_pos h).
    pose (typing_size_pos l0).
    intuition eauto.
    all: try lia.
Qed.

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis on typing judgments in application spines,
    fix and cofix blocks. This general version allows to get the induction hypothesis on
    any subderivation of the head of applications.

    The specialized version `typing_ind_env` below is the one used in general, with
    no special case for applications.
 *)

Lemma typing_ind_env_app_size `{cf : checker_flags} :
 forall (P : global_env_ext -> context -> term -> term -> Type)
        (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
        (PΓ : global_env_ext -> context -> Type),

   (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
        All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
       nth_error Γ n = Some decl ->
       PΓ Σ Γ ->
       P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : Universe.t),
       PΓ Σ Γ ->
       wf_universe Σ u ->
       P Σ Γ (tSort u) (tSort (Universe.super u))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term) (s1 s2 : Universe.t),
       PΓ Σ Γ ->
       Σ ;;; Γ |- t : tSort s1 ->
       P Σ Γ t (tSort s1) ->
       Σ ;;; Γ,, vass n t |- b : tSort s2 ->
       P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term)
           (s1 : Universe.t) (bty : term),
       PΓ Σ Γ ->
       Σ ;;; Γ |- t : tSort s1 ->
       P Σ Γ t (tSort s1) ->
       Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (b b_ty b' : term)
           (s1 : Universe.t) (b'_ty : term),
       PΓ Σ Γ ->
       Σ ;;; Γ |- b_ty : tSort s1 ->
       P Σ Γ b_ty (tSort s1) ->
       Σ ;;; Γ |- b : b_ty ->
       P Σ Γ b b_ty ->
       Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
       P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u s,
       PΓ Σ Γ ->
       forall (Hp : Σ ;;; Γ |- tProd na A B : tSort s), P Σ Γ (tProd na A B) (tSort s) ->
       forall (Ht : Σ ;;; Γ |- t : tProd na A B), P Σ Γ t (tProd na A B) ->

       (* Give a stronger induction hypothesis allowing to crawl under applications *)
       (forall t' T' (Ht' : Σ ;;; Γ |- t' : T'), typing_size Ht' <= max (typing_size Ht) (typing_size Hp) -> P Σ Γ t' T') ->

       Σ ;;; Γ |- u : A -> P Σ Γ u A ->
       P Σ Γ (tApp t u) (B{0 := u})) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
       Forall_decls_typing P Σ.1 ->
       PΓ Σ Γ ->
       declared_constant Σ.1 cst decl ->
       consistent_instance_ext Σ decl.(cst_universes) u ->
       P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
         mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
       Forall_decls_typing P Σ.1 ->
       PΓ Σ Γ ->
       consistent_instance_ext Σ mdecl.(ind_universes) u ->
       P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
           mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
       Forall_decls_typing P Σ.1 ->
       PΓ Σ Γ ->
       consistent_instance_ext Σ mdecl.(ind_universes) u ->
       P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

     (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
      forall (ci : case_info) p c brs indices ps mdecl idecl
        (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        mdecl.(ind_npars) = ci.(ci_npar) ->
        eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        wf_predicate mdecl idecl p ->
        consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
        forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
        P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
        wf_local Σ (Γ ,,, predctx) ->
        PΓ Σ (Γ ,,, predctx) ->
        is_allowed_elimination Σ idecl.(ind_kelim) ps ->
        ctx_inst (Prop_conj typing P) Σ Γ (p.(pparams) ++ indices)
          (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
        Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
        P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
        isCoFinite mdecl.(ind_finite) = false ->
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        wf_branches idecl brs ->
        All2i (fun i cdecl br =>
          (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
          let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
          (PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typing P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
        P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
         mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
       Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
       Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
       P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
       #|args| = ind_npars mdecl ->
       P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
       let types := fix_context mfix in
       fix_guard Σ Γ mfix ->
       nth_error mfix n = Some decl ->
       PΓ Σ (Γ ,,, types) ->
       All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
       All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
       wf_fixpoint Σ mfix ->
       P Σ Γ (tFix mfix n) decl.(dtype)) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
       let types := fix_context mfix in
       cofix_guard Σ Γ mfix ->
       nth_error mfix n = Some decl ->
       PΓ Σ (Γ ,,, types) ->
       All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
       All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
       wf_cofixpoint Σ mfix ->
       P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val term) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants cdecl ->
      P Σ Γ (tPrim p) (tConst prim_ty [])) ->

   (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
       PΓ Σ Γ ->
       Σ ;;; Γ |- t : A ->
       P Σ Γ t A ->
       Σ ;;; Γ |- B : tSort s ->
       P Σ Γ B (tSort s) ->
       Σ ;;; Γ |- A <=s B ->
       P Σ Γ t B) ->

      env_prop P PΓ.
Proof.
  intros P Pdecl PΓ.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
    otherwise it takes forever to execure the "pose", for some reason *)
  pose proof (@Fix_F { Σ & { wfΣ : wf Σ.1 & { Γ & { t & { T & Σ ;;; Γ |- t : T }}}}}) as p0.
  specialize (p0 (PCUICUtils.dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => precompose lt (fun x => typing_size x.π2.π2.π2.π2)))) as p.
  set (foo := (Σ; wfΣ; Γ; t; _; H) : { Σ & { wfΣ : wf Σ.1 & { Γ & { t & { T & Σ ;;; Γ |- t : T }}}}}).
  change Σ with foo.π1.
  change Γ with foo.π2.π2.π1.
  change t with foo.π2.π2.π2.π1.
  change T with foo.π2.π2.π2.π2.π1.
  change H with foo.π2.π2.π2.π2.π2.
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply PCUICUtils.wf_dlexprod; intros; apply wf_precompose; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ t T H.
  intros (Σ & wfΣ & Γ & t & t0 & H). simpl.
  intros IH. simpl in IH.
  split.
  - clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13.
    destruct Σ as [Σ φ].
    red. cbn. do 2 red in wfΣ. cbn in wfΣ.
    destruct Σ as [univs Σ]; cbn in *.
    set (Σg:= {| universes := univs; declarations := Σ |}) in *.
    destruct wfΣ; split => //.
    unfold Σg in o |- *; cbn in o.
    rename o into ongu. rename o0 into o. cbn in o |- *.
    destruct o. { constructor. }
    rename o0 into Xg.
    set (wfΣ := (ongu, o) : on_global_env cumulSpec0 (lift_typing typing) {| universes := univs; declarations := Σ |}).
    set (Σ':= {| universes := univs; declarations := Σ |}) in *.
    destruct Xg.
    rename on_global_decl_d into Xg.
    constructor; auto; try constructor; auto.
    * unshelve eset (IH' := IH ((Σ', udecl); (wfΣ; []; (tSort Universe.lProp); _; _))).
      shelve. simpl. apply type_Prop.
      forward IH'. constructor 1; cbn. lia.
      apply IH'; auto.

    * simpl. simpl in *.
      destruct d.
      + destruct c; simpl in *.
        destruct cst_body0; apply lift_typing_impl with (1 := Xg); intros ? Hs.
        all: specialize (IH ((Σ', udecl); wfΣ; _; _; _; Hs)).
        all: forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
        all: apply IH.
      + red in Xg.
        destruct Xg as [onI onP onnp]; constructor; eauto.
        { unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
          constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
          clear IH; rename IH' into IH.
          eapply Alli_impl; eauto. cbn in IH. clear onI onP onnp. intros n x Xg.
          refine {| ind_arity_eq := Xg.(ind_arity_eq);
                    ind_cunivs := Xg.(ind_cunivs) |}.
          - apply onArity in Xg.
            apply lift_typing_impl with (1 := Xg); intros ? Hs.
            apply (IH (_; _; _; Hs)).
          - pose proof Xg.(onConstructors) as Xg'.
            eapply All2_impl; eauto. intros.
            destruct X as [cass tyeq onctyp oncargs oncind].
            unshelve econstructor; eauto.
            { apply lift_typing_impl with (1 := onctyp); intros ? Hs.
              apply (IH (_; _; _; Hs)). }
            { apply sorts_local_ctx_impl with (1 := oncargs); intros Γ' t' T' HT'.
              apply lift_typing_impl with (1 := HT'); intros ? Hs.
              apply (IH (_; _; _; Hs)). }
            { clear -IH oncind.
              revert oncind.
              generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
              generalize (cstr_indices x0). induction 1; constructor; auto.
              do 2 red in t0 |- *.
              apply (IH (_; (_; (_; t0)))). }
          - pose proof (onProjections Xg); auto.
          - destruct Xg. simpl. unfold check_ind_sorts in *.
            destruct Universe.is_prop; auto.
            destruct Universe.is_sprop; auto.
            split. apply ind_sorts. destruct indices_matter; auto.
            eapply type_local_ctx_impl. eapply ind_sorts. intros ??? HT.
            apply lift_typing_impl with (1 := HT); intros ? Hs.
            apply (IH (_; _; _; Hs)).
           - apply (onIndices Xg). }
        { red in onP |- *.
          apply All_local_env_impl with (1 := onP); intros ??? HT.
          apply lift_typing_impl with (1 := HT); intros ? Hs.
          apply (IH ((Σ', udecl); (wfΣ; _; _; _; Hs))).
          constructor 1. simpl. subst Σ' Σg; cbn; lia. }

  - assert (forall Γ t T (Hty : Σ ;;; Γ |- t : T),
                  typing_size Hty < typing_size H ->
                  Forall_decls_typing P Σ.1 * P Σ Γ t T).
    { intros.
      specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ _ (existT _ _ Hty)))))).
      simpl in IH.
      forward IH.
      constructor 2. simpl. apply H0.
      split; apply IH. }
    (* rename X13 into X14. *)

    assert (Hdecls: typing_size H > 1 -> Forall_decls_typing P Σ.1).
    { specialize (X14 _ _ _  (type_Prop _)).
      cbn in X14. intros Hle. apply X14. lia. }
    assert (Hwf : forall Γ' (Hwf : wf_local Σ Γ'),
      All_local_env_size (@typing_size _) _ _ Hwf < typing_size H ->
      PΓ Σ Γ').
    { intros. eapply (XΓ _ _ _ Hwf); auto.
      clear -Pdecl wfΣ X14 H0.
      revert Hwf H0.
      induction Hwf; cbn in *; try destruct t2 as [u Hu]; simpl in *; constructor.
      - simpl in *. apply IHHwf. lia.
      - red. apply (X14 _ _ _ Hu). lia.
      - simpl in *. apply IHHwf. lia.
      - red. apply (X14 _ _ _ t3). lia.
      - red. simpl. apply (X14 _ _ _ Hu). lia. }

    assert (Htywf : forall Γ' t T (Hty : Σ ;;; Γ' |- t : T),
      typing_size Hty <= typing_size H ->
      PΓ Σ Γ').
    { intros. eapply (Hwf _ (typing_wf_local Hty)); auto.
      pose proof (typing_wf_local_size Hty). lia. }

    clear IH.
    assert (pΓ : PΓ Σ Γ).
    { apply (Htywf _ _ _ H). lia. }
    split; auto.
    set (wfΓ := typing_wf_local H); clearbody wfΓ.

    destruct H; simpl in pΓ;
      try solve [  match reverse goal with
                      H : _ |- _ => eapply H
                    end; eauto;
                    unshelve eapply X14; simpl; auto with arith].

    -- match reverse goal with
          H : _ |- _ => eapply H
        end; eauto;
          unshelve eapply X14; simpl; eauto with arith wf.

    -- match reverse goal with
          H : _ |- _ => eapply H
          end; eauto. all:try unshelve eapply X14; simpl; auto; try lia.
        exact H. 2:exact H0. 1-2:lia.
        simpl. instantiate (1:= H). instantiate (1:=H0).
        intros.
        eapply X14. instantiate (1 := Ht').
        simpl. lia.

    -- match reverse goal with
        H : _ |- _ => eapply H
        end; eauto.
        simpl in Hdecls. apply Hdecls; lia.

    -- eapply X6; eauto.
      apply Hdecls; simpl; lia.

    -- eapply X7; eauto. apply Hdecls; simpl; lia.

    -- simpl in pΓ. destruct c0, c1.
       eapply (X8 Σ wfΣ Γ (typing_wf_local H0) ci); eauto.
        ++ eapply (X14 _ _ _ H); eauto. rewrite /predctx; simpl; lia.
        ++ eapply (X14 _ _ _ H); eauto. rewrite /predctx; simpl; lia.
        ++ eapply (Hwf _ wf_pctx). rewrite /predctx; simpl.
          change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
          (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size cf).
          lia.
        ++ clear -ind_inst X14.
          assert (forall (Γ' : context) (t T : term) (Hty : Σ;;; Γ' |- t : T),
            typing_size Hty <= ctx_inst_size _ (@typing_size _) ind_inst ->
            P Σ Γ' t T).
          { intros. eapply (X14 _ _ _ Hty). simpl.
            change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
            (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size cf).
            lia. }
          clear -X ind_inst.
          revert ind_inst X.
          generalize (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl))).
          generalize (pparams p ++ indices).
          intros l c ctxi IH; induction ctxi; constructor; eauto.
          * split; tas. eapply (IH _ _ _ t0); simpl; auto. lia.
          * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.
          * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.

        ++ eapply (X14 _ _ _ H0); simpl. lia.
        ++ clear Hdecls. simpl in Hwf, Htywf, X14.
          clear -Hwf Htywf X14.
          subst ptm predctx; induction brs_ty.
          ** constructor.
          ** destruct r0 as [eq [wfcbc [t t0]]]. constructor.
              --- split; auto. intros brctxty.
                  repeat split.
                  +++ eapply (Hwf _ wfcbc); eauto. simpl.
                    change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
                      (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size cf).
                    lia.
                  +++ exact t.
                  +++ unshelve eapply (X14 _ _ _ t _); eauto.
                      simpl. lia.
                  +++ simpl; auto with arith.
                  +++ eapply (X14 _ _ _ t0); eauto. simpl; auto with arith.
                      lia.
              --- apply IHbrs_ty; auto. intros. apply (X14 _ _ _ Hty).
                  simpl. clear -H1; lia.
                  intros.
                  eapply (Hwf _ Hwf0). simpl. clear -H1; lia.
                  intros.
                  eapply (Htywf _ _ _ Hty). simpl; clear -H1. lia.

    -- eapply X9; eauto. apply Hdecls; simpl.
        pose proof (typing_size_pos H). lia.
        eapply (X14 _ _ _  H). simpl. lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
        eapply X10; eauto; clear X10. simpl in *.
        * assert(forall Γ0 (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                  typing_size Hty <
                        S
                          (all_size _ (fun (x : def term) p => typing_size p) a1) ->
                        PΓ Σ Γ0).
          {intros. eapply (Htywf _ _ _ Hty); eauto. lia. }
          destruct mfix. now rewrite nth_error_nil in e.
          depelim a1.
          eapply (X _ _ _ t). simpl. lia.
        * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                    typing_size Hty <
                    S (all_size (fun x : def term =>
                    ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                      (fun (x : def term)
                      (p : ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s) =>
                    let 'existT s d := p in typing_size d) a0) ->
                    Forall_decls_typing P Σ.1 * P Σ Γ t T).
          intros; eauto. eapply (X14 _ _ _ Hty); eauto. simpl. unfold infer_sort. lia.
          clear Hwf Htywf X14 a pΓ Hdecls.
          clear -a0 X.
          induction a0; constructor.
          destruct p as [s Hs]. exists s; split; auto.
          apply (X (dtype x) (tSort s) Hs). simpl. lia.
          apply IHa0. intros. eapply (X _ _ Hty); eauto.
          simpl. lia.
        * simpl in X14.
          assert(forall Γ0 : context,
                  wf_local Σ Γ0 ->
                forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                  typing_size Hty <
                        S
                          (all_size _ (fun (x : def term) p => typing_size p) a1) ->
                        Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
          {intros. eapply (X14 _ _ _ Hty); eauto. lia. }
          clear X14 Hwf Htywf.
          clear e decl f a0 Hdecls i.
          remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.

          induction a1; econstructor; eauto.
          ++ split; auto.
            eapply (X _ (typing_wf_local p) _ _ p). simpl. lia.
          ++ eapply IHa1. intros.
            eapply (X _ X0 _ _ Hty). simpl; lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12.
        eapply X11; eauto; clear X11. simpl in *.
        * assert(forall Γ0 (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                  typing_size Hty <
                        S
                          (all_size _ (fun (x : def term) p => typing_size p) a1) ->
                        PΓ Σ Γ0).
          {intros. eapply (Htywf _ _ _ Hty); eauto. lia. }
          destruct mfix. now rewrite nth_error_nil in e.
          depelim a1.
          eapply (X _ _ _ t). simpl. lia.
        * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                  typing_size Hty <
                  S (all_size (fun x : def term =>
                  ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                    (fun (x : def term)
                    (p : ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s) =>
                  let 'existT s d := p in typing_size d) a0) ->
                  Forall_decls_typing P Σ.1 * P Σ Γ t T).
        intros; eauto. eapply (X14 _ _ _ Hty); eauto. simpl. unfold infer_sort. lia.
        clear Hwf Htywf X14 a pΓ Hdecls.
        clear -a0 X.
        induction a0; constructor.
        destruct p as [s Hs]. exists s; split; auto.
        apply (X (dtype x) (tSort s) Hs). simpl. lia.
        apply IHa0. intros. eapply (X _ _ Hty); eauto.
        simpl. lia.
      * simpl in X14.
        assert(forall Γ0 : context,
                wf_local Σ Γ0 ->
              forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                typing_size Hty <
                      S
                        (all_size (fun x : def term => (Σ;;; Γ ,,, fix_context mfix |- dbody x : lift0 #|fix_context mfix| (dtype x))%type)
                                  (fun (x : def term) p => typing_size p) a1) ->
                      Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
        {intros. eapply (X14 _ _ _ Hty); eauto. lia. }
        clear X14 Hwf Htywf.
        clear e decl c a0 Hdecls i.
        remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.

        induction a1; econstructor; eauto.
        ++ split; auto.
          eapply (X _ (typing_wf_local p) _ _ p). simpl. lia.
        ++ eapply IHa1. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.
Qed.

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : global_env_ext -> context -> Type),

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
         All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : Universe.t),
        PΓ Σ Γ ->
        wf_universe Σ u ->
        P Σ Γ (tSort u) (tSort (Universe.super u))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term)
            (s1 : Universe.t) (bty : term),
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (b b_ty b' : term)
            (s1 : Universe.t) (b'_ty : term),
        PΓ Σ Γ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- tProd na A B : tSort s -> P Σ Γ (tProd na A B) (tSort s) ->
        Σ ;;; Γ |- t : tProd na A B -> P Σ Γ t (tProd na A B) ->
        Σ ;;; Γ |- u : A -> P Σ Γ u A ->
        P Σ Γ (tApp t u) (B{0 := u})) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      Forall_decls_typing P Σ.1 ->
      PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      wf_local Σ (Γ ,,, predctx) ->
      forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      ctx_inst (Prop_conj typing P) Σ Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
      Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      isCoFinite mdecl.(ind_finite) = false ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (PΓ Σ (Γ ,,, brctxty.1) ×
          Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2 ×
          Prop_conj typing P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_fixpoint Σ mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_cofixpoint Σ mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val term) prim_ty cdecl,
        PΓ Σ Γ ->
        primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants cdecl ->
        P Σ Γ (tPrim p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |- B : tSort s ->
        P Σ Γ B (tSort s) ->
        Σ ;;; Γ |- A <=s B ->
        P Σ Γ t B) ->

       env_prop P PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_prop.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  apply typing_ind_env_app_size; eauto.
Qed.

Ltac my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (wf (fst_ctx ?E)) => fresh "wf" E
  | (wf _) => fresh "wf"
  | consistent_instance_ext _ _ ?cu => fresh "cu" cu
  | (typing _ _ ?t _) => fresh "type" t
  | (@cumulSpec _ _ _ ?t _) => fresh "cumul" t
  | (@convSpec _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_judgment (@typing _) _ _) ?G) => fresh "wf" G
  | (All_local_env (lift_judgment (@typing _) _) _) => fresh "wf"
  | (All_local_env _ _ ?G) => fresh "H" G
  | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Section All_local_env.
  (** * Lemmas about All_local_env *)

  Context {cf: checker_flags}.

  Lemma nth_error_All_local_env {P Γ n} (isdecl : n < #|Γ|) :
    All_local_env P Γ ->
    on_some (on_local_decl P (skipn (S n) Γ)) (nth_error Γ n).
  Proof using Type.
    induction 1 in n, isdecl |- *. red; simpl.
    - destruct n; simpl; inv isdecl.
    - destruct n. red; simpl. red. simpl. apply t0.
      simpl. apply IHX. simpl in isdecl. lia.
    - destruct n. auto.
      apply IHX. simpl in *. lia.
  Qed.

  Lemma lookup_on_global_env P (Σ : global_env) c decl :
    on_global_env cumulSpec0 P Σ ->
    lookup_env Σ c = Some decl ->
    { Σ' : global_env & [× extends Σ' Σ, on_global_env cumulSpec0 P Σ' &
       on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl] }.
  Proof using Type.
    destruct Σ as [univs Σ retro]; rewrite /on_global_env /lookup_env; cbn.
    intros [cu Σp].
    induction Σp; simpl. congruence.
    destruct (eqb_specT c kn); subst.
    - intros [= ->].
      exists ({| universes := univs; declarations := Σ; retroknowledge := retro |}).
      split.
      * red; cbn. split; [split;[lsets|csets]| |].
        exists [(kn, decl)] => //.
        apply Environment.Retroknowledge.extends_refl.
      * split => //.
      * destruct o; assumption.
    - intros hl. destruct (IHΣp hl) as [Σ' []].
      exists Σ'.
      split=> //.
      destruct e as [eu ed]. red; cbn in *.
      split; [auto| |auto].
      destruct ed as [Σ'' ->].
      exists (Σ'' ,, (kn, d)) => //.
  Qed.

  Lemma All_local_env_app (P : context -> term -> typ_or_sort -> Type) l l' :
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l' ->
    All_local_env P (l ,,, l').
  Proof using Type.
    induction l'; simpl; auto. intuition.
    intuition. destruct a. destruct decl_body.
    inv b. econstructor; eauto. inv b; econstructor; eauto.
  Qed.

  Lemma All_local_env_app_inv (P : context -> term -> typ_or_sort -> Type) l l' :
    All_local_env P (l ,,, l') ->
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l'.
  Proof using Type.
    apply All_local_app_rel.
  Qed.

  Definition wf_local_rel_app_inv {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ->
    wf_local_rel Σ Γ1 Γ2 * wf_local_rel Σ (Γ1 ,,, Γ2) Γ3.
  Proof.
    intros h. apply All_local_env_app_inv in h as [h1 h2].
    split.
    - exact h1.
    - eapply All_local_env_impl. 1: exact h2.
      intros Γ t [T|] h.
      all: cbn in *.
      all: change PCUICEnvironment.app_context with app_context in *.
      all: rewrite <- app_context_assoc.
      all: auto.
  Defined.

  Lemma All_local_env_lookup {P Γ n} {decl} :
    All_local_env P Γ ->
    nth_error Γ n = Some decl ->
    on_local_decl P (skipn (S n) Γ) decl.
  Proof using Type.
    induction 1 in n, decl |- *. simpl. destruct n; simpl; congruence.
    destruct n. red. simpl. intros [= <-]. simpl. apply t0.
    simpl in *. eapply IHX.
    destruct n. simpl. intros [= <-]. auto.
    eapply IHX.
  Qed.

  Definition wf_local_rel_app {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 Γ2 -> wf_local_rel Σ (Γ1 ,,, Γ2) Γ3
    -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3).
  Proof.
    intros h1 h2. eapply All_local_env_app.
    split.
    - assumption.
    - eapply All_local_env_impl.
      + eassumption.
      + change PCUICEnvironment.app_context with app_context.
        intros Γ t []; cbn;
        now rewrite app_context_assoc.
  Defined.

  Definition wf_local_app {Σ Γ1 Γ2} :
    wf_local Σ Γ1 ->
    wf_local_rel Σ Γ1 Γ2 ->
    wf_local Σ (Γ1 ,,, Γ2).
  Proof using Type.
    intros H1 H2. apply All_local_env_app.
    now split.
  Qed.

  Definition wf_local_app_inv {Σ Γ1 Γ2} :
    wf_local Σ (Γ1 ,,, Γ2) ->
    wf_local Σ Γ1 * wf_local_rel Σ Γ1 Γ2.
  Proof using Type.
    apply All_local_env_app_inv.
  Qed.

  Lemma wf_local_app_ind {Σ Γ1 Γ2} :
    wf_local Σ Γ1 ->
    (wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2) ->
    wf_local Σ (Γ1 ,,, Γ2).
  Proof using Type.
    intros wf IH.
    apply wf_local_app; auto.
  Qed.

  Lemma All_local_env_map (P : context -> term -> typ_or_sort -> Type) f l :
    (forall u, f (tSort u) = tSort u) ->
    All_local_env (fun Γ t T => P (map (map_decl f) Γ) (f t) (typ_or_sort_map f T)) l
    -> All_local_env P (map (map_decl f) l).
  Proof using Type.
    intros Hf. induction 1; econstructor; eauto.
  Qed.

  Definition property :=
    forall (Σ : global_env_ext) (Γ : context),
      wf_local Σ Γ -> forall t T : term, typing Σ Γ t T -> Type.

  Definition lookup_wf_local {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
             (isdecl : n < #|Γ|) :
    All_local_env P (skipn (S n) Γ).
  Proof.
    induction wfΓ in n, isdecl |- *; simpl. constructor.
    cbn -[skipn] in *. destruct n.
    simpl. exact wfΓ.
    apply IHwfΓ. auto with arith.
    destruct n. exact wfΓ.
    apply IHwfΓ. auto with arith.
  Defined.

  Lemma wf_local_app_skipn {Σ Γ Γ' n} :
    wf_local Σ (Γ ,,, Γ') ->
    wf_local Σ (Γ ,,, skipn n Γ').
  Proof using Type.
    intros wf.
    destruct (le_dec n #|Γ'|).
    unfold app_context.
    replace Γ with (skipn (n - #|Γ'|) Γ).
    rewrite -skipn_app. now apply All_local_env_skipn.
    replace (n - #|Γ'|) with 0 by lia. now rewrite skipn_0.
    rewrite List.skipn_all2. lia.
    now eapply wf_local_app_l in wf.
  Qed.

  Definition on_local_decl_glob (P : term -> typ_or_sort -> Type) d :=
    match d.(decl_body) with
    | Some b => P b (Typ d.(decl_type)) × P d.(decl_type) Sort
    | None => P d.(decl_type) Sort
    end.

  Definition lookup_wf_local_decl {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
             {decl} (eq : nth_error Γ n = Some decl) :
    ∑ Pskip : All_local_env P (skipn (S n) Γ),
             on_local_decl_glob (P (skipn (S n) Γ)) decl.
  Proof.
    induction wfΓ in n, decl, eq |- *; simpl.
    - elimtype False. destruct n; depelim eq.
    - destruct n.
      + simpl. exists wfΓ. injection eq; intros <-. apply t0.
      + apply IHwfΓ. auto with arith.
    - destruct n.
      + exists wfΓ. injection eq; intros <-.
        simpl. split; auto.
      + apply IHwfΓ. apply eq.
  Defined.

  Definition on_wf_local_decl {Σ Γ}
             (P : forall Σ Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T -> Type)
             (wfΓ : wf_local Σ Γ) {d} (H : on_local_decl_glob (lift_typing typing Σ Γ) d) :=
    match d as d' return (on_local_decl_glob (lift_typing typing Σ Γ) d') -> Type with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |} =>
      fun H => (P Σ Γ wfΓ b ty H.1 * P Σ Γ wfΓ _ _ (projT2 (snd H)))%type
    | {| decl_name := na; decl_body := None; decl_type := ty |} => fun H => P Σ Γ wfΓ _ _ (projT2 H)
    end H.

  Lemma nth_error_All_local_env_over {P Σ Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : wf_local Σ Γ} :
    All_local_env_over typing P Σ Γ wfΓ ->
    let Γ' := skipn (S n) Γ in
    let p := lookup_wf_local_decl wfΓ n eq in
    (All_local_env_over typing P Σ Γ' (projT1 p) * on_wf_local_decl P (projT1 p) (projT2 p))%type.
  Proof.
    induction 1 in n, decl, eq |- *. simpl.
    - destruct n; simpl; elimtype False; discriminate eq.
    - destruct n. cbn [skipn]. noconf eq. split. apply X. simpl. apply Hs.
      simpl. apply IHX.
    - destruct n. noconf eq. simpl. split; auto.
      apply IHX.
  Defined.

  Lemma All_local_env_prod_inv :
    forall P Q Γ,
      All_local_env (fun Δ A t => P Δ A t × Q Δ A t) Γ ->
      All_local_env P Γ × All_local_env Q Γ.
  Proof using Type.
    intros P Q Γ h.
    induction h.
    - split ; constructor.
    - destruct IHh, t0.
      split ; constructor ; auto.
    - destruct IHh, t0, t1.
      split ; constructor ; auto.
  Qed.

  Lemma All_local_env_lift_prod_inv :
    forall Σ P Q Δ,
      All_local_env (lift_typing (fun Σ Γ => Trel_conj (P Σ Γ) (Q Σ Γ)) Σ) Δ ->
      All_local_env (lift_typing P Σ) Δ × All_local_env (lift_typing Q Σ) Δ.
  Proof using Type.
    intros Σ P Q Δ h.
    induction h.
    - split ; constructor.
    - destruct IHh. destruct t0 as [? [? ?]].
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
    - destruct IHh. destruct t0 as [? [? ?]]. destruct t1.
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
  Qed.

End All_local_env.
