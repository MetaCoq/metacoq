(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICCases.

Set Default Goal Selector "!".

(** * Definition of cumulativity and conversion relations *)


(* todo mode typing notation *)
Reserved Notation " Σ ;;; Γ |- t <=s u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t =s u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumulSpec (Σ : global_env) (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) : term -> term -> Type :=

(* transitivity *)

| cumul_Trans t u v :
    cumulSpec Σ Re Rle Γ t u ->
    cumulSpec Σ Re Rle Γ u v ->    
    cumulSpec Σ Re Rle Γ t v 

(* symmetry *)

| cumul_Sym t u :
    cumulSpec Σ Re Rle Γ t u ->
    cumulSpec Σ Re Rle Γ u t  

(* reflexivity *)

| cumul_Refl t :
    cumulSpec Σ Re Rle Γ t t 

(* Cumulativity rules *)

| cumul_Ind i u u' args args':
    R_global_instance Σ Re Rle (IndRef i) #|args| u u' ->
    #|args| = #|args'| ->
    All2 (cumulSpec Σ Re Re Γ) args args' ->
    cumulSpec Σ Re Rle Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')

| cumul_Construct i k u u' args args':
    R_global_instance Σ Re Rle (ConstructRef i k) #|args| u u' ->
    #|args| = #|args'| ->
    All2 (cumulSpec Σ Re Re Γ) args args' ->
    cumulSpec Σ Re Rle Γ (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')

| cumul_Sort s s' :
    Rle s s' ->
    cumulSpec Σ Re Rle Γ (tSort s) (tSort s')

| cumul_Const c u u' :
    R_universe_instance Re u u' ->
    cumulSpec Σ Re Rle Γ (tConst c u) (tConst c u')

(* congruence rules *)

| cumul_Evar e args args' :
    All2 (cumulSpec Σ Re Re Γ) args args' ->
    cumulSpec Σ Re Rle Γ (tEvar e args) (tEvar e args')

| cumul_App t t' u u' :
    cumulSpec Σ Re Rle Γ t t' ->
    cumulSpec Σ Re Re Γ u u' ->
    cumulSpec Σ Re Rle Γ (tApp t u) (tApp t' u')

| cumul_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    cumulSpec Σ Re Re Γ ty ty' ->
    cumulSpec Σ Re Rle Γ t t' ->
    cumulSpec Σ Re Rle Γ (tLambda na ty t) (tLambda na' ty' t')

| cumul_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    cumulSpec Σ Re Re Γ a a' ->
    cumulSpec Σ Re Rle Γ b b' ->
    cumulSpec Σ Re Rle Γ (tProd na a b) (tProd na' a' b')

| cumul_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    cumulSpec Σ Re Re Γ t t' ->
    cumulSpec Σ Re Re Γ ty ty' ->
    cumulSpec Σ Re Rle Γ u u' ->
    cumulSpec Σ Re Rle Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')

| cumul_Case indn p p' c c' brs brs' :
    eq_predicate (cumulSpec Σ Re Re Γ) Re p p' ->
    cumulSpec Σ Re Re Γ c c' ->
    All2 (fun x y =>
      eq_context_gen eq eq (bcontext x) (bcontext y) *
      cumulSpec Σ Re Re Γ (bbody x) (bbody y)
    ) brs brs' ->
    cumulSpec Σ Re Rle Γ (tCase indn p c brs) (tCase indn p' c' brs')

| cumul_Proj p c c' :
    cumulSpec Σ Re Re Γ c c' ->
    cumulSpec Σ Re Rle Γ (tProj p c) (tProj p c')

| cumul_Fix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec Σ Re Re Γ x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    cumulSpec Σ Re Rle Γ (tFix mfix idx) (tFix mfix' idx)

| cumul_CoFix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec Σ Re Re Γ x .(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    cumulSpec Σ Re Rle Γ (tCoFix mfix idx) (tCoFix mfix' idx)

(** Reductions *)

(** Beta red *)
| cumul_beta na t b a :
    cumulSpec Σ Re Rle Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| cumul_zeta na b t b' :
    cumulSpec Σ Re Rle Γ (tLetIn na b t b') (subst10 b b')

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    cumulSpec Σ Re Rle Γ (tRel i) (lift0 (S i) body)

(** iota red *)
| cumul_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    cumulSpec Σ Re Rle Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
                         (iota_red ci.(ci_npar) p args br)

(** Fix unfolding, with guard *)
| cumul_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    cumulSpec Σ Re Rle Γ (mkApps (tFix mfix idx) args)
                         (mkApps fn args)

(** CoFix-case unfolding *)
| cumul_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec Σ Re Rle Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
                         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| cumul_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec Σ Re Rle Γ (tProj p (mkApps (tCoFix mfix idx) args))
                         (tProj p (mkApps fn args))

(** Constant unfolding *)
| cumul_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    cumulSpec Σ Re Rle Γ (tConst c u) (subst_instance u body)

(** Proj *)
| cumul_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    cumulSpec Σ Re Rle Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg.

