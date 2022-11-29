(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICCases PCUICOnFreeVars.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

Definition cumul_predicate (cumul : context -> term -> term -> Type) Γ Re p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn))).

Reserved Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤s[ pb ]  u").

Definition cumul_Ind_univ {cf} (Σ : global_env_ext) pb i napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (IndRef i) napp.

Definition cumul_Construct_univ {cf} (Σ : global_env_ext) pb  i k napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (ConstructRef i k) napp.

(** * Definition of cumulativity and conversion relations *)

Inductive cumulSpec0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb) : term -> term -> Type :=

(* transitivity *)

| cumul_Trans : forall t u v,
    is_closed_context Γ -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤s[pb] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] v ->
    Σ ;;; Γ ⊢ t ≤s[pb] v

(* symmetry *)

| cumul_Sym : forall t u,
    Σ ;;; Γ ⊢ t ≤s[Conv] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] t

(* reflexivity *)

| cumul_Refl : forall t,
    Σ ;;; Γ ⊢ t ≤s[pb] t

(* Cumulativity rules *)

| cumul_Ind : forall i u u' args args',
    cumul_Ind_univ Σ pb i #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤s[pb] mkApps (tInd i u') args'

| cumul_Construct : forall i k u u' args args',
    cumul_Construct_univ Σ pb i k #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args ≤s[pb] mkApps (tConstruct i k u') args'

| cumul_Sort : forall s s',
    compare_universe pb Σ s s' ->
    Σ ;;; Γ ⊢ tSort s ≤s[pb] tSort s'

| cumul_Const : forall c u u',
    R_universe_instance (compare_universe Conv Σ) u u' ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] tConst c u'

(* congruence rules *)

| cumul_Evar : forall e args args',
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ tEvar e args ≤s[pb] tEvar e args'

| cumul_App : forall t t' u u',
    Σ ;;; Γ ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ u ≤s[Conv] u' ->
    Σ ;;; Γ ⊢ tApp t u ≤s[pb] tApp t' u'

| cumul_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t ≤s[pb] tLambda na' ty' t'

| cumul_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a ≤s[Conv] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b ≤s[pb] b' ->
    Σ ;;; Γ ⊢ tProd na a b ≤s[pb] tProd na' a' b'

| cumul_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t ≤s[Conv] t' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u ≤s[pb] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u ≤s[pb] tLetIn na' t' ty' u'

| cumul_Case indn : forall p p' c c' brs brs',
    cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ (compare_universe Conv Σ) p p' ->
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    All2 (fun br br' =>
      eq_context_gen eq eq (bcontext br) (bcontext br') ×
      Σ ;;; Γ ,,, inst_case_branch_context p br ⊢ bbody br ≤s[Conv] bbody br'
    ) brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs ≤s[pb] tCase indn p' c' brs'

| cumul_Proj : forall p c c',
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    Σ ;;; Γ ⊢ tProj p c ≤s[pb] tProj p c'

| cumul_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx

| cumul_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx ≤s[pb] tCoFix mfix' idx

(** Reductions *)

(** Beta red *)
| cumul_beta : forall na t b a,
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b {0 := a}

(** Let *)
| cumul_zeta : forall na b t b',
    Σ ;;; Γ ⊢ tLetIn na b t b' ≤s[pb] b' {0 := b}

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ ⊢ tRel i ≤s[pb] lift0 (S i) body

(** iota red *)
| cumul_iota : forall ci c u args p brs br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤s[pb] iota_red ci.(ci_npar) p args br

(** Fix unfolding, with guard *)
| cumul_fix : forall mfix idx args narg fn,
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤s[pb] mkApps fn args

(** CoFix-case unfolding *)
| cumul_cofix_case : forall ip p mfix idx args narg fn brs,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ≤s[pb] tCase ip p (mkApps fn args) brs

(** CoFix-proj unfolding *)
| cumul_cofix_proj : forall p mfix idx args narg fn,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ≤s[pb] tProj p (mkApps fn args)

(** Constant unfolding *)
| cumul_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
    decl.(cst_body) = Some body ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] body@[u]

(** Proj *)
| cumul_proj : forall p args u arg,
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ≤s[pb] arg

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u " := (@cumulSpec0 _ Σ Γ pb t u) : type_scope.

Definition convSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Conv.
Definition cumulSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Cumul.

(* ** Syntactic cumulativity up-to universes *)

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).
Notation " Σ ;;; Γ |- t =s u " := (@convSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).

Include PCUICConversion.

Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  Definition cumul_gen := @cumulSpec0.
End PCUICConversionParSpec.


Notation " Σ ⊢ Γ ≤s[ pb ] Δ " := (@cumul_pb_context _ pb Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.
Notation " Σ ⊢ Γ ≤s Δ " := (@cumul_pb_context _ Cumul Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.
Notation " Σ ⊢ Γ =s Δ " := (@cumul_pb_context _ Conv Σ Γ Δ) (at level 50, Γ, Δ at next level) : type_scope.

#[global]
Instance cumul_spec_refl {cf:checker_flags} Σ Γ pb : Reflexive (cumulSpec0 Σ Γ pb).
Proof. intro; constructor 3. Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convSpec Σ Γ) := _.

#[global]
Instance cumul_pb_decls_refl {cf:checker_flags} pb Σ Γ Γ' : Reflexive (cumul_pb_decls cumulSpec0 pb Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; reflexivity.
Qed.

#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls cumulSpec0 Σ Γ Γ') := _.
#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls cumulSpec0 Σ Γ Γ') := _.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context := (conv_context cumulSpec0 Σ).
  Notation cumul_context := (cumul_context cumulSpec0 Σ).

  Global Instance cumul_pb_ctx_refl pb : Reflexive (cumul_pb_context cumulSpec0 pb Σ).
  Proof using Type.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity.
  Qed.

  Global Instance conv_ctx_refl : Reflexive (conv_context) := _.
  Global Instance cumul_ctx_refl : Reflexive (cumul_context) := _.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.

Lemma cumulSpec0_ind_all :
  forall {cf} (Σ : global_env_ext)
         (P : conv_pb -> context -> term -> term -> Type),

        (* beta *)
       (forall (pb : conv_pb) (Γ : context) (na : aname) (t b a : term),
        P pb Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

        (* let *)
       (forall (pb : conv_pb) (Γ : context) (na : aname) (b t b' : term), P pb Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (pb : conv_pb) (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P pb Γ (tRel i) ((lift0 (S i)) body)) ->

        (* iota *)
       (forall (pb : conv_pb) (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P pb Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

        (* fix unfolding *)
       (forall (pb : conv_pb) (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P pb Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

      (* cofix unfolding *)
       (forall (pb : conv_pb) (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P pb Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (pb : conv_pb) (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P pb Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

        (* constant unfolding *)
       (forall (pb : conv_pb) (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P pb Γ (tConst c u) (subst_instance u body)) ->

        (* Proj *)
       (forall (pb : conv_pb) (Γ : context)p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P pb Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

        (* transitivity *)
       (forall (pb : conv_pb) (Γ : context) (t u v : term),
          is_closed_context Γ -> is_open_term Γ u ->
          cumulSpec0 Σ Γ pb t u -> P pb Γ t u ->
          cumulSpec0 Σ Γ pb u v -> P pb Γ u v ->
          P pb Γ t v) ->

        (* symmetry *)
       (forall (pb : conv_pb) (Γ : context) (t u : term),
        cumulSpec0 Σ Γ Conv u t -> P Conv Γ u t ->
         P pb Γ t u) ->

        (* reflexivity *)
        (forall (pb : conv_pb) (Γ : context) (t : term),
        P pb Γ t t) ->

        (* congruence rules *)

        (forall (pb : conv_pb) (Γ : context) (ev : nat) (l l' : list term),
          All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Conv Γ)) l l' -> P pb Γ (tEvar ev l) (tEvar ev l')) ->

        (forall (pb : conv_pb) (Γ : context) (t t' u u' : term),
          cumulSpec0 Σ Γ pb t t' -> P pb Γ t t' ->
          cumulSpec0 Σ Γ Conv u u' -> P Conv Γ u u' ->
          P pb Γ (tApp t u) (tApp t' u')) ->

        (forall (pb : conv_pb) (Γ : context) (na na' : aname) (ty ty' t t' : term),
          eq_binder_annot na na' ->
          cumulSpec0 Σ Γ Conv ty ty' -> P Conv Γ ty ty' ->
          cumulSpec0 Σ (Γ ,, vass na ty) pb t t' -> P pb (Γ ,, vass na ty) t t' ->
          P pb Γ (tLambda na ty t) (tLambda na' ty' t')) ->

        (forall (pb : conv_pb) (Γ : context) (na na' : binder_annot name) (a a' b b' : term),
          eq_binder_annot na na' ->
          cumulSpec0 Σ Γ Conv a a' -> P Conv Γ a a' ->
          cumulSpec0 Σ (Γ,, vass na a) pb b b' -> P pb (Γ,, vass na a) b b' ->
          P pb Γ (tProd na a b) (tProd na' a' b')) ->

     (forall (pb : conv_pb) (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term),
        eq_binder_annot na na' ->  cumulSpec0 Σ Γ Conv t t' -> P Conv Γ t t' ->
        cumulSpec0 Σ Γ  Conv ty ty' -> P Conv Γ ty ty' ->
        cumulSpec0 Σ (Γ,, vdef na t ty) pb u u' -> P pb (Γ,, vdef na t ty) u u' ->
        P pb Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

      (forall (pb : conv_pb) (Γ : context) (indn : case_info) (p p' : predicate term)
        (c c' : term) (brs brs' : list (branch term)),
        cumul_predicate (fun Γ t u => cumulSpec0 Σ Γ Conv t u × P Conv Γ t u) Γ
          (compare_universe Conv Σ) p p' ->
        cumulSpec0 Σ Γ Conv c c' -> P Conv Γ c c' ->
        All2
          (Trel_conj (fun br br' : branch term =>
               eq_context_gen eq eq (bcontext br) (bcontext br') *
               cumulSpec0 Σ (Γ,,, inst_case_branch_context p br) Conv
                 (bbody br) (bbody br'))
            (fun br br' => P Conv (Γ,,, inst_case_branch_context p br) (bbody br) (bbody br'))) brs brs' ->
       P pb Γ (tCase indn p c brs) (tCase indn p' c' brs')) ->

       (forall (pb : conv_pb) (Γ : context)
          (p : projection) (c c' : term),
        cumulSpec0 Σ Γ Conv c c' -> P Conv Γ c c' ->
         P pb Γ (tProj p c) (tProj p c')) ->

       (forall (pb : conv_pb) (Γ : context)
          (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
          All2
            (fun x y : def term =>
             ((cumulSpec0 Σ Γ Conv (dtype x) (dtype y) ×
                P Conv Γ (dtype x) (dtype y)
               × cumulSpec0 Σ (Γ,,, fix_context mfix) Conv
                   (dbody x) (dbody y)) ×
                P Conv (Γ,,, fix_context mfix) (dbody x) (dbody y) × rarg x = rarg y) *
             eq_binder_annot (dname x) (dname y)) mfix mfix' ->
           P pb Γ (tFix mfix idx) (tFix mfix' idx)) ->

       (forall (pb : conv_pb) (Γ : context)
           (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
           All2
             (fun x y : def term =>
              ((cumulSpec0 Σ Γ Conv (dtype x) (dtype y) ×
                 P Conv Γ (dtype x) (dtype y)
                × cumulSpec0 Σ (Γ,,, fix_context mfix) Conv
                    (dbody x) (dbody y)) × P Conv (Γ,,, fix_context mfix)
                    (dbody x) (dbody y) × rarg x = rarg y) *
              eq_binder_annot (dname x) (dname y)) mfix mfix' ->
            P pb Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->

      (* cumulativity rules *)

      (forall (pb : conv_pb)
            (Γ : context) (i : inductive) (u u' : list Level.t)
            (args args' : list term),
      R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (IndRef i) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Conv Γ)) args args' ->
      P pb Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')) ->

    (forall (pb : conv_pb)
      (Γ : context) (i : inductive) (k : nat)
      (u u' : list Level.t) (args args' : list term),
      R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (ConstructRef i k) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Conv Γ)) args args' ->
      P pb Γ (mkApps (tConstruct i k u) args)
              (mkApps (tConstruct i k u') args')) ->

      (forall (pb : conv_pb)
          (Γ : context) (s s' : Universe.t),
          compare_universe pb Σ s s' -> P pb Γ (tSort s) (tSort s')) ->

      (forall (pb : conv_pb)
          (Γ : context) (c : kername) (u u' : list Level.t),
          R_universe_instance (compare_universe Conv Σ) u u' -> P pb Γ (tConst c u) (tConst c u') ) ->

       forall (pb : conv_pb) (Γ : context) (t t0 : term), cumulSpec0 Σ Γ pb t t0 -> P pb Γ t t0.
Proof.
  intros. rename X24 into Xlast. revert pb Γ t t0 Xlast.
  fix aux 5. intros pb Γ t u.
  move aux at top.
  destruct 1.
  - eapply X8; eauto.
  - eapply X9; eauto.
  - eapply X10; eauto.
  - eapply X20; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X21; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X22; eauto.
  - eapply X23; eauto.
  - eapply X11.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X12; eauto.
  - eapply X13; eauto.
  - eapply X14; eauto.
  - eapply X15; eauto.
  - eapply X16 ; eauto.
    + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
      repeat split ; eauto.
      * revert c0. generalize (pparams p), (pparams p').
        fix aux' 3; destruct 1; constructor; auto.
    + revert brs brs' a.
      fix aux' 3; destruct 1; constructor; intuition auto.
  - eapply X17 ; eauto.
  - eapply X18 ; eauto.
    revert a.
    set (mfixAbs := mfix). unfold mfixAbs at 2 5.
    clearbody mfixAbs.
    revert mfix mfix'.
    fix aux' 3; destruct 1; constructor.
    + intuition auto.
    + auto.
  - eapply X19 ; eauto.
    revert a.
    set (mfixAbs := mfix). unfold mfixAbs at 2 5.
    clearbody mfixAbs.
    revert mfix mfix'.
    fix aux' 3; destruct 1; constructor.
    + intuition auto.
    + auto.
  - eapply X.
  - eapply X0.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
Defined.

Lemma convSpec0_ind_all :
  forall {cf} (Σ : global_env_ext)
         (P : context -> term -> term -> Type),

        (* beta *)
       (forall  (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

        (* let *)
       (forall  (Γ : context) (na : aname) (b t b' : term), P  Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall  (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P  Γ (tRel i) ((lift0 (S i)) body)) ->

        (* iota *)
       (forall  (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P  Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

        (* fix unfolding *)
       (forall  (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

      (* cofix unfolding *)
       (forall  (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall  (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

        (* constant unfolding *)
       (forall  (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

        (* Proj *)
       (forall  (Γ : context) p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P  Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

        (* transitivity *)
       (forall  (Γ : context) (t u v : term),
          is_closed_context Γ -> is_open_term Γ u ->
          cumulSpec0 Σ Γ Conv t u -> P Γ t u ->
          cumulSpec0 Σ Γ Conv u v -> P Γ u v ->
          P Γ t v) ->

        (* symmetry *)
       (forall  (Γ : context) (t u : term),
        cumulSpec0 Σ Γ Conv u t -> P Γ u t ->
        P Γ t u) ->

        (* reflexivity *)
        (forall  (Γ : context) (t : term),
        P Γ t t) ->

        (* congruence rules *)

        (forall  (Γ : context) (ev : nat) (l l' : list term),
          All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

        (forall  (Γ : context) (t t' u u' : term),
          cumulSpec0 Σ Γ Conv t t' -> P Γ t t' ->
          cumulSpec0 Σ Γ Conv u u' -> P Γ u u' ->
          P Γ (tApp t u) (tApp t' u')) ->

        (forall  (Γ : context) (na na' : aname) (ty ty' t t' : term),
          eq_binder_annot na na' ->
          cumulSpec0 Σ Γ Conv ty ty' -> P Γ ty ty' ->
          cumulSpec0 Σ (Γ ,, vass na ty) Conv t t' -> P (Γ ,, vass na ty) t t' ->
          P Γ (tLambda na ty t) (tLambda na' ty' t')) ->

        (forall  (Γ : context) (na na' : binder_annot name) (a a' b b' : term),
          eq_binder_annot na na' ->
          cumulSpec0 Σ Γ Conv a a' -> P Γ a a' ->
          cumulSpec0 Σ (Γ,, vass na a) Conv b b' -> P (Γ,, vass na a) b b' ->
          P Γ (tProd na a b) (tProd na' a' b')) ->

     (forall  (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term),
        eq_binder_annot na na' ->  cumulSpec0 Σ Γ Conv t t' -> P Γ t t' ->
        cumulSpec0 Σ Γ Conv ty ty' -> P Γ ty ty' ->
        cumulSpec0 Σ (Γ,, vdef na t ty) Conv u u' -> P (Γ,, vdef na t ty) u u' ->
        P Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

      (forall  (Γ : context) (indn : case_info) (p p' : predicate term)
        (c c' : term) (brs brs' : list (branch term)),
        cumul_predicate (fun Γ t u => cumulSpec0 Σ Γ Conv t u * P Γ t u) Γ (compare_universe Conv Σ) p p' ->
        cumulSpec0 Σ Γ Conv c c' -> P Γ c c' ->
        All2
          (Trel_conj (fun br br' : branch term =>
               eq_context_gen eq eq (bcontext br) (bcontext br') *
               cumulSpec0 Σ (Γ,,, inst_case_branch_context p br) Conv
                 (bbody br) (bbody br'))
            (fun br br' => P (Γ,,, inst_case_branch_context p br) (bbody br) (bbody br'))) brs brs' ->
       P Γ (tCase indn p c brs) (tCase indn p' c' brs')) ->

       (forall  (Γ : context)
          (p : projection) (c c' : term),
        cumulSpec0 Σ Γ Conv c c' -> P Γ c c' ->
         P Γ (tProj p c) (tProj p c')) ->

       (forall  (Γ : context)
          (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
          All2
            (fun x y : def term =>
             ((cumulSpec0 Σ Γ Conv (dtype x) (dtype y) ×
                P Γ (dtype x) (dtype y)
               × cumulSpec0 Σ (Γ,,, fix_context mfix) Conv
                   (dbody x) (dbody y)) × P (Γ,,, fix_context mfix)
                   (dbody x) (dbody y) × rarg x = rarg y) *
             eq_binder_annot (dname x) (dname y)) mfix mfix' ->
           P Γ (tFix mfix idx) (tFix mfix' idx)) ->

       (forall  (Γ : context)
           (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
           All2
             (fun x y : def term =>
              ((cumulSpec0 Σ Γ Conv (dtype x) (dtype y) ×
                 P Γ (dtype x) (dtype y)
                × cumulSpec0 Σ (Γ,,, fix_context mfix) Conv
                    (dbody x) (dbody y)) × P (Γ,,, fix_context mfix)
                    (dbody x) (dbody y) × rarg x = rarg y) *
              eq_binder_annot (dname x) (dname y)) mfix mfix' ->
            P Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->

      (* cumulativiity rules *)

      (forall
            (Γ : context) (i : inductive) (u u' : list Level.t)
            (args args' : list term),
      R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (IndRef i) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Γ)) args args' ->
      P Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')) ->

    (forall
      (Γ : context) (i : inductive) (k : nat)
      (u u' : list Level.t) (args args' : list term),
      R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (ConstructRef i k) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Γ Conv) (P Γ)) args args' ->
      P Γ (mkApps (tConstruct i k u) args)
              (mkApps (tConstruct i k u') args')) ->

      (forall
          (Γ : context) (s s' : Universe.t),
          eq_universe Σ s s' -> P Γ (tSort s) (tSort s')) ->

      (forall
          (Γ : context) (c : kername) (u u' : list Level.t),
          R_universe_instance (eq_universe Σ) u u' -> P Γ (tConst c u) (tConst c u') ) ->

       forall  (Γ : context) (t t0 : term), cumulSpec0 Σ Γ Conv t t0 -> P Γ t t0.
Proof.
  intros. rename X24 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t u.
  move aux at top.
  destruct 1.
  - eapply X8; eauto.
  - eapply X9; eauto.
  - eapply X10; eauto.
  - eapply X20; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X21; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X22; eauto.
  - eapply X23; eauto.
  - eapply X11.
    revert args args' a.
    fix aux' 3; destruct 1; constructor; auto.
  - eapply X12; eauto.
  - eapply X13; eauto.
  - eapply X14; eauto.
  - eapply X15; eauto.
  - eapply X16 ; eauto.
    + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
      repeat split ; eauto.
      * revert c0. generalize (pparams p), (pparams p').
        fix aux' 3; destruct 1; constructor; auto.
    + revert brs brs' a.
      fix aux' 3; destruct 1; constructor; intuition auto.
  - eapply X17 ; eauto.
  - eapply X18 ; eauto.
    revert a.
    set (mfixAbs := mfix). unfold mfixAbs at 2 5.
    clearbody mfixAbs.
    revert mfix mfix'.
    fix aux' 3; destruct 1; constructor.
    + intuition auto.
    + auto.
  - eapply X19 ; eauto.
    revert a.
    set (mfixAbs := mfix). unfold mfixAbs at 2 5.
    clearbody mfixAbs.
    revert mfix mfix'.
    fix aux' 3; destruct 1; constructor.
    + intuition auto.
    + auto.
  - eapply X.
  - eapply X0.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
Defined.
