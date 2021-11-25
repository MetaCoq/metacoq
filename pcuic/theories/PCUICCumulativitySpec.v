(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICCases PCUICOnFreeVars.

Set Default Goal Selector "!".

Reserved Notation " Σ ;;; Γ |- t <=s u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t =s u " (at level 50, Γ, t, u at next level).

Definition cumul_predicate (cumul : context -> term -> term -> Type) Γ Re p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn))).

(** * Definition of cumulativity and conversion relations *)

Inductive cumulSpec0 (Σ : global_env) (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) : term -> term -> Type :=

(* transitivity *)

| cumul_Trans t u v :
    is_closed_context Γ -> is_open_term Γ u -> 
    cumulSpec0 Σ Re Rle Γ t u ->
    cumulSpec0 Σ Re Rle Γ u v ->    
    cumulSpec0 Σ Re Rle Γ t v 

(* symmetry *)

| cumul_Sym t u :
    cumulSpec0 Σ Re Re Γ t u ->
    cumulSpec0 Σ Re Rle Γ u t  

(* reflexivity *)

| cumul_Refl t :
    cumulSpec0 Σ Re Rle Γ t t 

(* Cumulativity rules *)

| cumul_Ind i u u' args args':
    R_global_instance Σ Re Rle (IndRef i) #|args| u u' ->
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')

| cumul_Construct i k u u' args args':
    R_global_instance Σ Re Rle (ConstructRef i k) #|args| u u' ->
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')

| cumul_Sort s s' :
    Rle s s' ->
    cumulSpec0 Σ Re Rle Γ (tSort s) (tSort s')

| cumul_Const c u u' :
    R_universe_instance Re u u' ->
    cumulSpec0 Σ Re Rle Γ (tConst c u) (tConst c u')

(* congruence rules *)

| cumul_Evar e args args' :
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (tEvar e args) (tEvar e args')

| cumul_App t t' u u' :
    cumulSpec0 Σ Re Rle Γ t t' ->
    cumulSpec0 Σ Re Re Γ u u' ->
    cumulSpec0 Σ Re Rle Γ (tApp t u) (tApp t' u')

| cumul_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ ty ty' ->
    cumulSpec0 Σ Re Rle (Γ ,, vass na ty) t t' ->
    cumulSpec0 Σ Re Rle Γ (tLambda na ty t) (tLambda na' ty' t')

| cumul_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ a a' ->
    cumulSpec0 Σ Re Rle (Γ ,, vass na a) b b' ->
    cumulSpec0 Σ Re Rle Γ (tProd na a b) (tProd na' a' b')

| cumul_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ t t' ->
    cumulSpec0 Σ Re Re Γ ty ty' ->
    cumulSpec0 Σ Re Rle (Γ ,, vdef na t ty) u u' ->
    cumulSpec0 Σ Re Rle Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')

| cumul_Case indn p p' c c' brs brs' :
    cumul_predicate (cumulSpec0 Σ Re Re) Γ Re p p' ->
    cumulSpec0 Σ Re Re Γ c c' ->
    All2 (fun br br' =>
      eq_context_gen eq eq (bcontext br) (bcontext br') * 
      cumulSpec0 Σ Re Re (Γ ,,, inst_case_branch_context p br) (bbody br) (bbody br')
    ) brs brs' ->
    cumulSpec0 Σ Re Rle Γ (tCase indn p c brs) (tCase indn p' c' brs')

| cumul_Proj p c c' :
    cumulSpec0 Σ Re Re Γ c c' ->
    cumulSpec0 Σ Re Rle Γ (tProj p c) (tProj p c')

| cumul_Fix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec0 Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec0 Σ Re Re (Γ ,,, fix_context mfix) x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    cumulSpec0 Σ Re Rle Γ (tFix mfix idx) (tFix mfix' idx)

| cumul_CoFix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec0 Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec0 Σ Re Re (Γ ,,, fix_context mfix) x .(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    cumulSpec0 Σ Re Rle Γ (tCoFix mfix idx) (tCoFix mfix' idx)

(** Reductions *)

(** Beta red *)
| cumul_beta na t b a :
    cumulSpec0 Σ Re Rle Γ (tApp (tLambda na t b) a) (b {0 := a})

(** Let *)
| cumul_zeta na b t b' :
    cumulSpec0 Σ Re Rle Γ (tLetIn na b t b') (b' {0 := b})

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    cumulSpec0 Σ Re Rle Γ (tRel i) (lift0 (S i) body)

(** iota red *)
| cumul_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    cumulSpec0 Σ Re Rle Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
                         (iota_red ci.(ci_npar) p args br)

(** Fix unfolding, with guard *)
| cumul_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tFix mfix idx) args)
                         (mkApps fn args)

(** CoFix-case unfolding *)
| cumul_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec0 Σ Re Rle Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
                         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| cumul_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec0 Σ Re Rle Γ (tProj p (mkApps (tCoFix mfix idx) args))
                         (tProj p (mkApps fn args))

(** Constant unfolding *)
| cumul_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    cumulSpec0 Σ Re Rle Γ (tConst c u) (subst_instance u body)

(** Proj *)
| cumul_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    cumulSpec0 Σ Re Rle Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg.

Definition convSpec `{checker_flags} Σ :=
  let φ := (global_ext_constraints Σ) in cumulSpec0 Σ.1 (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition cumulSpec `{checker_flags} Σ :=
  let φ := (global_ext_constraints Σ) in cumulSpec0 Σ.1 (eq_universe φ) (leq_universe φ).

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u).
Notation " Σ ;;; Γ |- t =s u " := (@convSpec _ Σ Γ t u).
  
Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICEnvTyping.
  Definition conv := @convSpec.
  Definition cumul := @cumulSpec.
End PCUICConversionParSpec.

Module PCUICConversionSpec := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICEnvTyping PCUICConversionParSpec.
Include PCUICConversionSpec.

Notation conv_context Σ Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
Notation cumul_context Σ Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').


#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl.
Qed.

#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl || apply leq_term_refl.
Qed.

#[global]
Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumulSpec Σ Γ).
Proof.
  intro. constructor 3.
Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convSpec Σ Γ).
Proof.
  intro; constructor 3. 
Qed.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
  Notation cumul_context Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').

  Global Instance conv_ctx_refl : Reflexive (All2_fold (conv_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity.
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (All2_fold (cumul_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity. 
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.


Definition cumulSpec0_ctx Σ Re Rle := (OnOne2_local_env (on_one_decl (fun Δ t t' => cumulSpec0 Σ Re Rle Δ t t'))).
Definition cumulSpec0_ctx_rel Σ Re Rle Γ := (OnOne2_local_env (on_one_decl (fun Δ t t' => cumulSpec0 Σ Re Rle (Γ ,,, Δ) t t'))).

Lemma cumul0_ind_all :
  forall (Σ : global_env) (P : forall (Re Rle : Universe.t -> Universe.t -> Prop), context -> term -> term -> Type),

        (* beta *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na : aname) (t b a : term),
        P Re Rle Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

        (* let *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na : aname) (b t b' : term), P Re Rle  Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Re Rle  Γ (tRel i) ((lift0 (S i)) body)) ->

        (* iota *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
          P Re Rle  Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

        (* fix unfolding *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Re Rle Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

      (* cofix unfolding *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Re Rle Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Re Rle Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

        (* constant unfolding *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Re Rle Γ (tConst c u) (subst_instance u body)) ->

        (* Proj *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Re Rle  Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

        (* transitivity *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t u v : term),
           cumulSpec0 Σ Re Rle Γ t u -> P Re Rle Γ t u ->
           cumulSpec0 Σ Re Rle Γ u v -> P Re Rle Γ u v ->
           P Re Rle Γ t v) ->

        (* symmetry *)
       (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t u : term),
       cumulSpec0 Σ Re Re Γ u t -> P Re Re Γ u t ->
       P Re Rle Γ t u) ->

        (* reflexivity *)
        (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t : term),
        P Re Rle Γ t t) ->
        
        (* congruence rules *)

        (forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na na' : aname) (ty ty' t t' : term),
        eq_binder_annot na na' ->  
        cumulSpec0 Σ Re Re Γ ty ty' -> P Re Re Γ ty ty' -> 
        cumulSpec0 Σ Re Rle (Γ ,, vass na ty) t t' -> P Re Rle (Γ ,, vass na ty) t t' -> 
        P Re Rle Γ (tLambda na ty t) (tLambda na' ty' t')) ->

       (* (forall (Γ : context) (na : aname) (ty ty' t t : term),
        eq_binder_annot na na' ->  
        cumulSpec0 Σ Re Rle Σ Γ ty ty' -> P Re Rle Γ ty ty' -> 
        cumulSpec0 Σ Re Rle Σ Γ t t' -> P Re Rle Γ t t' -> 
        P Γ (tLambda na ty t) (tLambda na' ty' t')) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->
       
       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br)) 
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) -> *)

       forall (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t t0 : term), cumulSpec0 Σ Re Rle Γ t t0 -> P Re Rle Γ t t0.
Proof.
  intros. rename X12 into Xlast. revert Re Rle Γ t t0 Xlast.
  fix aux 4. intros Re Rle Γ t u.
  move aux at top.
  destruct 1.
  - eapply X8; eauto.   
  - eapply X9; eauto.   
  - eapply X10; eauto.   
 - admit.
 - admit.
 - admit.
 - admit.
 - admit.
 - admit.
 - eapply X11; eauto.   
 - admit.
 - admit.
 - admit.
 - admit.
 - admit.
 - admit.
 - eapply X.
 - eapply X0.
 - eapply X1; eauto. 
 - eapply X2; eauto.
 - eapply X3; eauto.
 - eapply X4; eauto.
 - eapply X5; eauto.
 - eapply X6; eauto.
 - eapply X7; eauto.
Admitted.   
      
 (* eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.

  - revert params' o.
    generalize (pparams p).
    fix auxl 3.
    intros params params' [].
    + constructor. split; auto.
    + constructor. auto.
      
  - revert brs' o.
    revert brs.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + simpl in *. constructor; intros; intuition auto.
    + constructor. eapply auxl. apply Hl.

  - revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto.
    + constructor. auto.

  - eapply X23.
    revert mfix0 mfix1 o; fix auxl 3.
    intros l l' Hl; destruct Hl;
    constructor; try split; auto; intuition.

  - eapply X24.
    revert o. generalize (fix_context mfix0). intros c Xnew.
    revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X25.
    revert mfix0 mfix1 o.
    fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X26.
    revert o. generalize (fix_context mfix0). intros c new.
    revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined. *)