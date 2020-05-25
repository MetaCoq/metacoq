(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils
  EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition.

From MetaCoq Require Export LibHypsNaming.
Require Import ssreflect.
Set Asymmetric Patterns.
Require Import Equations.Type.Relation.
From Equations Require Import Equations.
Import MonadNotation.

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of PCUIC terms.
  These come with many additional functions, to define the reduction operations,
  deal with arities, declarations in the environment etc...

 *)

Definition isSort T :=
  match T with
  | tSort u => True
  | _ => False
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => True
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => False
  end.


Module PCUICLookup := Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

(** Inductive substitution, to produce a constructors' type *)
Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.
Hint Rewrite inds_length : len.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind. simpl. reflexivity.
  now rewrite app_length /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Definition type_of_constructor mdecl (cdecl : ident * term * nat) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance_constr u (snd (fst cdecl))).

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

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
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

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.

Hint Rewrite subst_context_length subst_instance_context_length 
  app_context_length map_context_length fix_context_length fix_subst_length cofix_subst_length 
  map_length app_length lift_context_length 
  @mapi_length @mapi_rec_length List.rev_length Nat.add_0_r : len.

Definition tDummy := tVar String.EmptyString.

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a :
    red1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| red_iota ind pars c u args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs)
         (iota_red pars c args brs)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) (subst_instance_constr u body)

(** Proj *)
| red_proj i pars narg args k u arg:
    nth_error args (pars + narg) = Some arg ->
    red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args)) arg


| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred ind p p' c brs : red1 Σ Γ p p' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p' c brs)
| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' :
    OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (tApp N1 M2)
| app_red_r M2 N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : name) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : name) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ind : inductive) (pars c : nat) (u : Instance.t) (args : list term)
          (p : term) (brs : list (nat * term)),
        P Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs) (iota_red pars c args brs)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) (ip : inductive * nat) (p : term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (nat * term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance_constr u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (k : nat) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args)) arg) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ind : inductive * nat) (p p' c : term) (brs : list (nat * term)),
        red1 Σ Γ p p' -> P Γ p p' -> P Γ (tCase ind p c brs) (tCase ind p' c brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c c' : term) (brs : list (nat * term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c : term) (brs brs' : list (nat * term)),
           OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) snd fst) brs brs' ->
           P Γ (tCase ind p c brs) (tCase ind p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : name) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : name) (M2 N2 M1 : term),
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
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros. rename X26 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1; match goal with
              | |- P _ (tFix _ _) (tFix _ _) => idtac
              | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
              | |- P _ (mkApps (tFix _ _) _) _ => idtac
              | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
              | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
              | H : _ |- _ => eapply H; eauto
              end.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.

  - revert brs brs' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. intuition auto. constructor. intuition auto.

  - revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - eapply X22.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X23.
    revert o. generalize (fix_context mfix0). intros c Xnew.
    revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X24.
    revert mfix0 mfix1 o.
    fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X25.
    revert o. generalize (fix_context mfix0). intros c new.
    revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.


(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Type :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

(** *** η-conversion *)

(* [eta_expands u v] states v is an expansion of u *)
Definition eta_expands u v : Type :=
  ∑ na A t π,
    u = zipc t π /\
    v = zipc (tLambda na A (tApp (lift0 1 t) (tRel 0))) π.

Definition eta_eq :=
  clos_refl_sym_trans eta_expands.

(** ** Utilities for typing *)

(** Decompose an arity into a context and a sort *)

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Lemma destArity_app_aux {Γ Γ' t}
  : destArity (Γ ,,, Γ') t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                                        (destArity Γ' t).
Proof.
  revert Γ'.
  induction t; cbn; intro Γ'; try reflexivity.
  - rewrite <- app_context_cons. now eapply IHt2.
  - rewrite <- app_context_cons. now eapply IHt3.
Qed.

Lemma destArity_app {Γ t}
  : destArity Γ t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                               (destArity [] t).
Proof.
  exact (@destArity_app_aux Γ [] t).
Qed.

Lemma destArity_app_Some {Γ t ctx s}
  : destArity Γ t = Some (ctx, s)
    -> ∑ ctx', destArity [] t = Some (ctx', s) /\ ctx = Γ ,,, ctx'.
Proof.
  intros H. rewrite destArity_app in H.
  destruct (destArity [] t) as [[ctx' s']|]; cbn in *.
  exists ctx'. inversion H. now subst.
  discriminate H.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> mkApps f l = tApp (mkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  intros. rewrite <- mkApps_nested. simpl. f_equal.
  rewrite removelast_app. congruence. simpl. now rewrite app_nil_r.
  rewrite last_app. congruence.
  reflexivity.
Qed.

Lemma destArity_tFix {mfix idx args} :
  destArity [] (mkApps (tFix mfix idx) args) = None.
Proof.
  induction args. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_tApp {t u l} :
  destArity [] (mkApps (tApp t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_tInd {t u l} :
  destArity [] (mkApps (tInd t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.


Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t = u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u
| cumul_eta_l t u v : eta_expands t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_eta_r t u v : Σ ;;; Γ |- t <= v -> eta_expands u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

(** *** Conversion

   Defined as cumulativity in both directions.
 *)


Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u
| conv_eta_l t u v : eta_expands t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_eta_r t u v : Σ ;;; Γ |- t = v -> eta_expands u v -> Σ ;;; Γ |- t = u
where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.

Hint Resolve cumul_refl conv_refl : pcuic.


(** ** Typing relation *)

Module PCUICEnvTyping := EnvTyping PCUICTerm PCUICEnvironment.
Include PCUICEnvTyping.

Section WfArity.
  Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

  Definition isWfArity Σ (Γ : context) T :=
    { ctx & { s & (destArity [] T = Some (ctx, s)) * All_local_env (lift_typing typing Σ) (Γ ,,, ctx) } }.

  Context (property : forall (Σ : global_env_ext) (Γ : context),
              All_local_env (lift_typing typing Σ) Γ ->
              forall (t T : term), typing Σ Γ t T -> Type).

  Definition isWfArity_prop Σ (Γ : context) T :=
    { wfa : isWfArity Σ Γ T & All_local_env_over typing property Σ _ (snd (projT2 (projT2 wfa))) }.
End WfArity.

(* AXIOM GUARD CONDITION *)
Axiom fix_guard : mfixpoint term -> bool.

Axiom fix_guard_red1 :
  forall Σ Γ mfix mfix' idx,
    fix_guard mfix ->
    red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_eq_term :
  forall mfix mfix' idx,
    fix_guard mfix ->
    upto_names (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_rename :
  forall mfix f,
    let mfix' :=
        map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix
    in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_lift :
  forall mfix n k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (lift n k) (lift n k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_subst :
  forall mfix s k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

(* AXIOM Cofix Guard Condition (guarded by constructors) *)

Axiom cofix_guard : mfixpoint term -> bool.

Axiom cofix_guard_red1 :
  forall Σ Γ mfix mfix' idx,
    cofix_guard mfix ->
    red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard mfix'.

Axiom cofix_guard_eq_term :
  forall mfix mfix' idx,
    cofix_guard mfix ->
    upto_names (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard mfix'.

Axiom cofix_guard_rename :
  forall mfix f,
    let mfix' :=
        map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix
    in
    cofix_guard mfix ->
    cofix_guard mfix'.

Axiom cofix_guard_lift :
  forall mfix n k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (lift n k) (lift n k')) mfix in
    cofix_guard mfix ->
    cofix_guard mfix'.

Axiom cofix_guard_subst :
  forall mfix s k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    cofix_guard mfix ->
    cofix_guard mfix'.

(* AXIOM INDUCTIVE GUARD CONDITION *)
Axiom ind_guard : mutual_inductive_body -> bool.

(* Mark unfinished subgoals due to eta conversion *)
Axiom todoeta : forall {A}, A.
Ltac todoeta := apply todoeta.

(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst params pars s ty :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, tProd _ _ B =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) B
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, tLetIn _ _ _ b' => instantiate_params_subst params pars (subst0 s b :: s) b'
    | _, _ => None (* Not enough products in the type *)
    end
  end.

(* If [ty] is [Π params . B] *)
(* and [⊢ pars : params] *)
(* then [instantiate_params] is [B{pars}] *)

Definition instantiate_params (params : context) (pars : list term) (ty : term) : option term :=
  match instantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (subst0 s ty)
  | None => None
  end.

Lemma instantiate_params_ params pars ty :
  instantiate_params params pars ty
  = option_map (fun '(s, ty) => subst0 s ty)
               (instantiate_params_subst (List.rev params) pars [] ty).
Proof.
  unfold instantiate_params.
  repeat (destruct ?; cbnr).
Qed.

(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat × term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
      Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance_constr u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
         (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance_context u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed.

(* [params] and output already instanciated by [u] *)
Definition build_case_predicate_type ind mdecl idecl params u ps : option term :=
  X <- instantiate_params (subst_instance_context u (ind_params mdecl)) params
                         (subst_instance_constr u (ind_type idecl)) ;;
  X <- destArity [] X ;;
  let inddecl :=
      {| decl_name := nNamed idecl.(ind_name);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|X.1|) params ++ to_extended_list X.1) |} in
  ret (it_mkProd_or_LetIn (X.1 ,, inddecl) (tSort ps)).
  
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

Definition check_recursivity_kind Σ ind r :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mib) => PCUICReflect.eqb mib.(ind_finite) r
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

Definition wf_fixpoint (Σ : global_env) mfix :=
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive fixpoints are all on the same mututal
       inductive block *)
    forallb (PCUICReflect.eqb ind) inds &&
    check_recursivity_kind Σ ind Finite
  | _ => false
  end.

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

Definition wf_cofixpoint (Σ : global_env) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive cofixpoints are all producing
       coinductives in the same mututal coinductive block *)
    forallb (PCUICReflect.eqb ind) inds &&
    check_recursivity_kind Σ ind CoFinite
  | _ => false
  end.

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    All_local_env (lift_typing typing Σ) Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort l :
    All_local_env (lift_typing typing Σ) Γ ->
    LevelSet.In l (global_ext_levels Σ) ->
    Σ ;;; Γ |- tSort (Universe.make l) : tSort (Universe.super l)

| type_Prod na A B s1 s2 :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda na A t s1 B :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- (tLambda na A t) : tProd na A B

| type_LetIn na b B t s1 A :
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App t na A B u :
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Const cst u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance_constr u decl.(cst_type)

| type_Ind ind u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance_constr u idecl.(ind_type)

| type_Construct ind i u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case indnpar u p c brs args :
    let ind := indnpar.1 in
    let npar := indnpar.2 in
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
    Σ ;;; Γ |- p : pty ->
    leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    isCoFinite mdecl.(ind_finite) = false ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
    All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2) * (Σ ;;; Γ |- bty.2 : tSort ps)) brs btys ->
    Σ ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c])

| type_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance_constr u ty)

| type_Fix mfix n decl :
    fix_guard mfix ->
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))
      * (isLambda d.(dbody) = true)%type) mfix ->
    wf_fixpoint Σ.1 mfix -> 
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)
  
| type_CoFix mfix n decl :
    cofix_guard mfix ->
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ.1 mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)
  
| type_Cumul t A B :
    Σ ;;; Γ |- t : A ->
    (isWfArity typing Σ Γ B + {s & Σ ;;; Γ |- B : tSort s})%type ->
    Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T) : type_scope.

Notation wf_local Σ Γ := (All_local_env (lift_typing typing Σ) Γ).

Lemma meta_conv {cf : checker_flags} Σ Γ t A B :
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros h []; assumption.
Qed.


(** ** Typechecking of global environments *)

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.


Module PCUICTypingDef <: Typing PCUICTerm PCUICEnvironment PCUICEnvTyping.

  Definition ind_guard := ind_guard.
  Definition typing := @typing.
  Definition smash_context := smash_context.
  Definition lift_context := lift_context.
  Definition subst_telescope := subst_telescope.
  Definition subst := subst.
  Definition lift := lift.
  Definition inds := inds.  
End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICEnvTyping
    PCUICTypingDef
    PCUICLookup.
Include PCUICDeclarationTyping.

Definition typing_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix typing_size 5.
  destruct 1 ;
    repeat match goal with
           | H : typing _ _ _ _ |- _ => apply typing_size in H
           end;
    match goal with
    | H : All2 _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H : _ + _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
  - exact (S (wf_local_size _ typing_size _ a)).
  - exact (S (wf_local_size _ typing_size _ a)).
  - exact (S (S (wf_local_size _ typing_size _ a))).
  - exact (S (S (wf_local_size _ typing_size _ a))).
  - exact (S (S (wf_local_size _ typing_size _ a))).
  - exact (S (Nat.max d1 (Nat.max d2
                                (all2_size _ (fun x y p => Nat.max (typing_size Σ Γ (snd x) (snd y) (snd (fst p))) (typing_size _ _ _ _ (snd p))) a)))).
  - exact (S (Nat.max (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x  p => typing_size Σ _ _ _ p.π2) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ (fst p)) a1))).
  - exact (S (Nat.max (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x  p => typing_size Σ _ _ _ p.π2) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ p) a1))).
  - destruct s. red in i.
    exact (S (Nat.max (wf_local_size _ typing_size _ (snd (projT2 (projT2 i)))) d)).
    destruct s as [u Hu]. apply typing_size in Hu.
    exact (S (Nat.max d Hu)).
Defined.

Lemma typing_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; simpl; try lia. destruct s as [s | [u Hu]]; try lia.
Qed.

Fixpoint globenv_size (Σ : global_env) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} := Forall_decls_typing typing.
Definition wf_ext `{checker_flags} := on_global_env_ext (lift_typing typing).

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. intro H; apply H. Qed.

Hint Resolve wf_ext_wf : core.

Lemma wf_ext_consistent {cf:checker_flags} Σ :
  wf_ext Σ -> consistent Σ.
Proof.
  intros [? [? [? [? ?]]]]; assumption.
Qed.

Hint Resolve wf_ext_consistent : core.


Lemma wf_local_app `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
Proof.
  induction Γ'. auto.
  simpl. intros H'; inv H'; eauto.
Defined.
Hint Resolve wf_local_app : wf.

Lemma typing_wf_local `{checker_flags} {Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_local Σ Γ.
Proof.
  induction 1; eauto using wf_local_app.
Defined.
Hint Resolve typing_wf_local : wf.

Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) (PΓ : forall Σ Γ, wf_local Σ Γ ->  Type) :=
  forall Σ (wfΣ : wf Σ.1) Γ t T (ty : Σ ;;; Γ |- t : T),
    Forall_decls_typing P Σ.1 * 
    PΓ Σ Γ (typing_wf_local ty) *
    P Σ Γ t T.

Lemma env_prop_typing `{checker_flags} P PΓ : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma type_Prop_wf `{checker_flags} Σ Γ : wf_local Σ Γ -> Σ ;;; Γ |- tSort Universe.type0m : tSort Universe.type1.
Proof. 
  repeat constructor; auto.
  apply prop_global_ext_levels.
Defined.

Lemma env_prop_wf_local `{checker_flags} P PΓ : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ), PΓ Σ Γ wfΓ.
Proof. intros.
  pose (type_Prop_wf _ _ wfΓ).
  now destruct (X _ wfΣ _ _ _ t) as [[? ?] ?].
Qed.

Lemma type_Prop `{checker_flags} Σ : Σ ;;; [] |- tSort Universe.type0m : tSort Universe.type1.
  repeat constructor.
  apply prop_global_ext_levels.
Defined.

Lemma env_prop_sigma `{checker_flags} P PΓ : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ), Forall_decls_typing P Σ.
Proof.
  intros. red in X. eapply (X (empty_ext Σ)).
  apply wfΣ.
  apply type_Prop.
Defined.


Derive Signature for All_local_env.

Set Equations With UIP.
Derive NoConfusion for context_decl.
Derive NoConfusion for list.
Derive NoConfusion for All_local_env.

Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
  wf_local_size Σ (@typing_size _) _ (wf_local_app _ _ _ Hwf) <=
  wf_local_size Σ (@typing_size _) _ Hwf.
Proof.
  induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
  depelim Hwf.
  - inversion H0. subst. noconf H4. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ Hwf). lia.
  - inversion H0. subst. noconf H4. specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. simpl. lia.
Qed.

Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  wf_local_size Σ (@typing_size _) _ (typing_wf_local d) < typing_size d.
Proof.
  induction d; simpl; 
  change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
  (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size H); try lia.
  - destruct indnpar as [ind' npar']; cbn in *; subst ind npar. lia.
  - destruct s as [s | [u Hu]]; try lia.
Qed.

Lemma wf_local_inv `{checker_flags} {Σ Γ'} (w : wf_local Σ Γ') :
  forall d Γ,
    Γ' = d :: Γ ->
    ∑ w' : wf_local Σ Γ,
      match d.(decl_body) with
      | Some b =>
        ∑ u (ty : Σ ;;; Γ |- b : d.(decl_type)),
          { ty' : Σ ;;; Γ |- d.(decl_type) : tSort u |
            wf_local_size Σ (@typing_size _) _ w' <
            wf_local_size _ (@typing_size _) _ w /\
            typing_size ty <= wf_local_size _ (@typing_size _) _ w /\
            typing_size ty' <= wf_local_size _ (@typing_size _) _ w }

      | None =>
        ∑ u,
          { ty : Σ ;;; Γ |- d.(decl_type) : tSort u |
            wf_local_size Σ (@typing_size _) _ w' <
            wf_local_size _ (@typing_size _) _ w /\
            typing_size ty <= wf_local_size _ (@typing_size _) _ w }
      end.
Proof.
  intros d Γ.
  destruct w.
  - simpl. congruence.
  - intros [=]. subst d Γ0.
    exists w. simpl. destruct l. exists x. exists t0. pose (typing_size_pos t0).
    simpl. split.
    + lia.
    + auto with arith.
  - intros [=]. subst d Γ0.
    exists w. simpl. simpl in l. destruct l as [u h].
    simpl in l0.
    exists u, l0, h. simpl.
    pose (typing_size_pos h).
    pose (typing_size_pos l0).
    intuition eauto.
    all: try lia.
Qed.

Derive Signature for Alli.

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : forall Σ Γ, wf_local Σ Γ -> Type),

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ), 
         All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ wfΓ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        PΓ Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        P Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term)
            (s1 : Universe.t) (bty : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b b_ty b' : term)
            (s1 : Universe.t) (b'_ty : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tProd na A B -> P Σ Γ t (tProd na A B) ->
        Σ ;;; Γ |- u : A -> P Σ Γ u A ->
        P Σ Γ (tApp t u) (B{0 := u})) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing P Σ.1 -> PΓ Σ Γ wfΓ ->
        ind_npars mdecl = npar ->
        let params := firstn npar args in
        forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
        Σ ;;; Γ |- p : pty ->
        P Σ Γ p pty ->
        leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
        Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
        isCoFinite mdecl.(ind_finite) = false ->
        P Σ Γ c (mkApps (tInd ind u) args) ->
        forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
        All2 (fun br bty => (br.1 = bty.1) *
                         (Σ ;;; Γ |- br.2 : bty.2) * P Σ Γ br.2 bty.2 *
                         (Σ ;;; Γ |- bty.2 : tSort ps) * P Σ Γ bty.2 (tSort ps))
             brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
        Forall_decls_typing P Σ.1 -> PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ Γ wfΓ ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
                   (isLambda d.(dbody) = true)%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        wf_fixpoint Σ.1 mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ Γ wfΓ ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        wf_cofixpoint Σ.1 mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        (isWfArity_prop typing Pdecl Σ Γ B + {s & (Σ ;;; Γ |- B : tSort s) * P Σ Γ B (tSort s)})%type ->
        Σ ;;; Γ |- A <= B ->
        P Σ Γ t B) ->

       env_prop P PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_prop.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
   otherwise it takes forever to execure the "pose", for some reason *)
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & 
                          { t : term & { T : term & Σ ;;; Γ |- t : T }}}}})) as p0.
  specialize (p0 (dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => precompose lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 x)))))))) as p.
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ t (existT _ _ H)))) : { Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}).
  change Σ with (projT1 foo).
  change Γ with (projT1 (projT2 (projT2 foo))).
  change t with (projT1 (projT2 (projT2 (projT2 foo)))).
  change T with (projT1 (projT2 (projT2 (projT2 (projT2 foo))))).
  change H with (projT2 (projT2 (projT2 (projT2 (projT2 foo))))).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_dlexprod; intros; apply wf_precompose; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ t T H.
  intros (Σ & wfΣ & Γ & t & t0 & H). simpl.
  intros IH. simpl in IH.
  split. split.
  destruct Σ as [Σ φ]. destruct Σ.
  constructor.
  cbn in wfΣ; inversion_clear wfΣ. auto.
  inv wfΣ.
  rename X14 into Xg.
  constructor; auto. unfold Forall_decls_typing in IH.
  - simple refine (let IH' := IH ((Σ, udecl); (X13; []; (tSort Universe.type0m ); _; _)) in _).
    shelve. simpl. apply type_Prop.
    forward IH'. constructor 1; cbn. lia.
    apply IH'; auto.
  - simpl. simpl in *.
    destruct d; simpl.
    + destruct c; simpl in *.
      destruct cst_body; simpl in *.
      simpl.
      intros. red in Xg. simpl in Xg.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ [] (existT _ _ (existT _ _ Xg)))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia.
      apply IH.
      red. simpl. red in Xg; simpl in Xg.
      destruct Xg as [s Hs]. red. simpl.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ [] (existT _ _ (existT _ _ Hs)))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia. exists s. eapply IH.
    + red in Xg.
      destruct Xg as [onI onP onnp]; constructor; eauto.
      eapply Alli_impl; eauto. clear onI onP onnp; intros n x Xg.
      refine {| ind_indices := Xg.(ind_indices);
                ind_arity_eq := Xg.(ind_arity_eq);
                ind_cshapes := Xg.(ind_cshapes) |}.
                
      ++ apply onArity in Xg. destruct Xg as [s Hs]. exists s; auto.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ [] (existT _ _ (existT _ _ Hs)))))).
         simpl in IH. simpl. apply IH; constructor 1; simpl; lia.
      ++ pose proof Xg.(onConstructors) as Xg'.
         eapply All2_impl; eauto. intros.
         destruct X14 as [cass chead tyeq onctyp oncargs oncind].
         unshelve econstructor; eauto.
         destruct onctyp as [s Hs].
         simpl in Hs.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ Hs)))))).
         simpl in IH. simpl. exists s. simpl. apply IH; constructor 1; simpl; auto with arith.
         eapply type_local_ctx_impl; eauto. simpl. intros. red in X14.
         destruct T.
         specialize (IH ((Σ, udecl); (X13; _; _; _; X14))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
         destruct X14 as [u Hu]. exists u.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ Hu)))))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
         clear -X13 IH oncind.
         revert oncind.
         generalize (List.rev (lift_context #|cshape_args y| 0 (ind_indices Xg))).
         generalize (cshape_indices y). induction 1; constructor; auto.
         red in p0 |- *.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ p0)))))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
      ++ intros Hprojs; pose proof (onProjections Xg Hprojs); auto. 
      ++ destruct Xg. simpl. unfold check_ind_sorts in *.
         destruct universe_family; auto.
         +++ split. apply ind_sorts0. destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts0.
             intros. red in X14.
             destruct T.
             specialize (IH ((Σ, udecl); (X13; _; _; _; X14))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
             destruct X14 as [u Hu]. exists u.
             specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ Hu)))))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
         +++ split. apply ind_sorts0. destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts0.
             intros. red in X14.
             destruct T.
             specialize (IH ((Σ, udecl); (X13; _; _; _; X14))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
             destruct X14 as [u Hu]. exists u.
             specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ Hu)))))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
      ++ red in onP |- *.
         eapply All_local_env_impl; eauto.
         intros. destruct T; simpl in X14.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ X14)))))).
         simpl in IH. apply IH. constructor 1. simpl. lia.
         destruct X14 as [u Hu].
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ _ (existT _ _ Hu)))))).
         simpl in IH. simpl. exists u. apply IH. constructor 1. simpl. lia.

  - assert (forall Γ t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               Forall_decls_typing P Σ.1 * P Σ Γ t T).
    intros.
    specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ _ (existT _ _ Hty)))))).
    simpl in IH.
    forward IH.
    constructor 2. simpl. apply H0.
    split; apply IH. clear IH.
    rename X13 into X14.

    assert (All_local_env_over typing Pdecl Σ Γ (typing_wf_local H)).
    { clear -Pdecl wfΣ X14.
      pose proof (typing_wf_local_size H).
      set (foo := typing_wf_local H) in *.
      clearbody foo.
      revert foo H0. generalize Γ at 1 2 4.
      induction foo; simpl in *; try destruct t2 as [u Hu]; simpl in *; constructor.
      - simpl in *. apply IHfoo. lia.
      - red. eapply (X14 _ _ _ Hu). lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ _ _ t3). lia.
      - red. apply (X14 _ _ _ Hu). lia. }
    eapply XΓ; eauto.

  - assert (forall Γ t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               Forall_decls_typing P Σ.1 * P Σ Γ t T).
    intros.
    specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ _ (existT _ _ Hty)))))).
    simpl in IH.
    forward IH.
    constructor 2. simpl. apply H0.
    split; apply IH. clear IH.
    rename X13 into X14.

    assert (Hdecls: typing_size H > 1 -> Forall_decls_typing P Σ.1).
    { specialize (X14 _ _ _  (type_Prop _)).
      simpl in X14. intros Hle. apply X14. lia. }

    assert (All_local_env_over typing Pdecl Σ Γ (typing_wf_local H)).
    { clear -Pdecl wfΣ X14.
      pose proof (typing_wf_local_size H).
      set (foo := typing_wf_local H) in *.
      clearbody foo.
      revert foo H0. generalize Γ at 1 2 4.
      induction foo; simpl in *; try destruct t2 as [u Hu]; simpl in *; constructor.
      - simpl in *. apply IHfoo. lia.
      - red. eapply (X14 _ _ _ Hu). lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ _ _ t3). lia.
      - red. apply (X14 _ _ _ Hu). lia. }
    apply XΓ in X13. all:auto.

    destruct H;
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
       end; eauto.
       simpl in Hdecls. apply Hdecls; lia.

    -- eapply X6; eauto.
      apply Hdecls; simpl; lia.

    -- eapply X7; eauto. apply Hdecls; simpl; lia.

    -- destruct indnpar as [ind' npar'];
         cbn in ind; cbn in npar; subst ind; subst npar.
       eapply X8; eauto.
       ++ eapply (X14 _ _ _ H); eauto. simpl; auto with arith.
       ++ eapply (X14 _ _ _ H); eauto. simpl; auto with arith.
       ++ simpl in *.
          eapply (X14 _ _ _ H0); eauto. clear. lia.
       ++ clear X13 Hdecls. revert a X14. simpl. clear. intros.
          induction a; simpl in *.
          ** constructor.
          ** destruct r as [[? ?] ?]. constructor.
             --- intuition eauto.
                 +++ eapply (X14 _ _ _ t); eauto. simpl; auto with arith.
                     lia.
                 +++ eapply (X14 _ _ _ t0); eauto. simpl; auto with arith.
                     lia.
             --- apply IHa. auto. intros.
                 eapply (X14 _ _ _ Hty). lia.

    -- eapply X9; eauto. apply Hdecls; simpl.
       pose proof (typing_size_pos H). lia.
       eapply (X14 _ _ _  H). simpl. lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
       eapply X10; eauto; clear X10. simpl in *.
       * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                    typing_size Hty <
                    S (all_size (fun x : def term =>
                    ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                     (fun (x : def term)
                     (p : ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s) =>
                   typing_size p.π2) a0) ->
                    Forall_decls_typing P Σ.1 * P Σ Γ t T).
         intros; eauto. eapply (X14 _ _ _ Hty); eauto. lia.
         clear X13 X14 a Hdecls.
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
                         (all_size _ (fun (x : def term) p => typing_size (fst p)) a1) ->
                        Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
         {intros. eapply (X14 _ _ _ Hty); eauto. lia. }
         clear X14 X13.
         clear e decl i a0 Hdecls i0.
         remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
 
         induction a1; econstructor; eauto.
         ++ split; auto. 
           eapply (X _ (typing_wf_local (fst p)) _ _ (fst p)). simpl. lia.
         ++ eapply IHa1. intros.
           eapply (X _ X0 _ _ Hty). simpl; lia.       

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12.
       eapply X11; eauto; clear X11. simpl in *.
       * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                  typing_size Hty <
                  S (all_size (fun x : def term =>
                  ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                    (fun (x : def term)
                    (p : ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s) =>
                  typing_size p.π2) a0) ->
                  Forall_decls_typing P Σ.1 * P Σ Γ t T).
        intros; eauto. eapply (X14 _ _ _ Hty); eauto. lia.
        clear X13 X14 a  Hdecls.
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
        clear X14 X13.
        clear e decl i a0 Hdecls i0.
        remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.

        induction a1; econstructor; eauto.
        ++ split; auto. 
          eapply (X _ (typing_wf_local p) _ _ p). simpl. lia.
        ++ eapply IHa1. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.

    -- eapply X12; eauto.
       ++ eapply (X14 _ _ _ H); simpl. destruct s as [s | [u Hu]]; lia.
       ++ simpl in X14, X13.
          destruct s as [s | [u Hu]].
          ** left.
             red. exists s. red in s. revert X14.
             generalize (snd (projT2 (projT2 s))).
             induction a; simpl in *; intros X14 *; constructor.
             --- apply IHa. intros. eapply (X14 _ _ _ Hty). lia.
             --- red. eapply (X14 _ _ _ (projT2 t1)). destruct t1. simpl. lia.
             --- apply IHa. intros. eapply (X14 _ _ _ Hty). lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
          ** right.
             exists u. intuition eauto. unshelve eapply X14. all: eauto. lia.
Qed.
Print Assumptions typing_ind_env.

Ltac my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (wf (fst_ctx ?E)) => fresh "wf" E
  | (wf _) => fresh "wf"
  | (typing _ _ ?t _) => fresh "type" t
  | (@cumul _ _ _ ?t _) => fresh "cumul" t
  | (conv _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_typing (@typing _) _) ?G) => fresh "wf" G
  | (All_local_env (lift_typing (@typing _) _) _) => fresh "wf"
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
  Proof.
    induction 1 in n, isdecl |- *. red; simpl.
    - destruct n; simpl; inv isdecl.
    - destruct n. red; simpl. red. simpl. apply t0.
      simpl. apply IHX. simpl in isdecl. lia.
    - destruct n. auto.
      apply IHX. simpl in *. lia.
  Qed.

  Lemma lookup_on_global_env P Σ c decl :
    on_global_env P Σ ->
    lookup_env Σ c = Some decl ->
    { Σ' & { wfΣ' : on_global_env P Σ'.1 & on_global_decl P Σ' c decl } }.
  Proof.
    induction 1; simpl. congruence.
    unfold eq_kername; destruct kername_eq_dec; subst.
    intros [= ->].
    exists (Σ, udecl). exists X. auto.
    apply IHX.
  Qed.

  Lemma All_local_env_app (P : context -> term -> option term -> Type) l l' :
    All_local_env P (l ,,, l') ->
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l'.
  Proof.
    induction l'; simpl; split; auto.
    - constructor.
    - unfold app_context in X.
      inv X.
      + intuition auto.
      + apply IHl'. auto.
    - inv X.
      + eapply localenv_cons_abs.
        * apply IHl'. apply X0.
        * apply X1.
      + eapply localenv_cons_def.
        * apply IHl'. apply X0.
        * apply X1.
        * apply X2.
  Qed.

  Definition wf_local_rel_app {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ->
    wf_local_rel Σ Γ1 Γ2 * wf_local_rel Σ (Γ1 ,,, Γ2) Γ3.
  Proof.
    intros h. apply All_local_env_app in h as [h1 h2].
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
  Proof.
    induction 1 in n, decl |- *. simpl. destruct n; simpl; congruence.
    destruct n. red. simpl. intros [= <-]. simpl. apply t0.
    simpl in *. eapply IHX.
    destruct n. simpl. intros [= <-]. auto.
    eapply IHX.
  Qed.

  Lemma All_local_env_app_inv (P : context -> term -> option term -> Type) l l' :
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l' ->
    All_local_env P (l ,,, l').
  Proof.
    induction l'; simpl; auto. intuition.
    intuition. destruct a. destruct decl_body.
    inv b. econstructor; eauto. inv b; econstructor; eauto. Qed.


  Definition wf_local_rel_app_inv {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 Γ2 -> wf_local_rel Σ (Γ1 ,,, Γ2) Γ3
    -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3).
  Proof.
    intros h1 h2. eapply All_local_env_app_inv.
    split.
    - assumption.
    - eapply All_local_env_impl.
      + eassumption.
      + change PCUICEnvironment.app_context with app_context.
        intros Γ t []; cbn;
        now rewrite app_context_assoc.
  Defined.


  Lemma All_local_env_map (P : context -> term -> option term -> Type) f l :
    (forall u, f (tSort u) = tSort u) ->
    All_local_env (fun Γ t T => P (map (map_decl f) Γ) (f t) (option_map f T)) l
    -> All_local_env P (map (map_decl f) l).
  Proof.
    intros Hf. induction 1; econstructor; eauto.
  Qed.

  Definition property :=
    forall (Σ : global_env_ext) (Γ : context),
      All_local_env (lift_typing typing Σ) Γ -> forall t T : term, typing Σ Γ t T -> Type.

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

  Definition on_local_decl_glob (P : term -> option term -> Type) d :=
    match d.(decl_body) with
    | Some b => (P b (Some d.(decl_type)) * P d.(decl_type) None)%type
    | None => P d.(decl_type) None
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

  Lemma nth_error_All_local_env_over {P Σ Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : All_local_env (lift_typing typing Σ) Γ} :
    All_local_env_over typing P Σ Γ wfΓ ->
    let Γ' := skipn (S n) Γ in
    let p := lookup_wf_local_decl wfΓ n eq in
    (All_local_env_over typing P Σ Γ' (projT1 p) * on_wf_local_decl P (projT1 p) (projT2 p))%type.
  Proof.
    induction 1 in n, decl, eq |- *. simpl.
    - destruct n; simpl; elimtype False; discriminate eq.
    - destruct n. cbn [skipn]. noconf eq. split. apply X. simpl. apply p.
      simpl. apply IHX.
    - destruct n. noconf eq. simpl. split; auto.
      apply IHX.
  Defined.

  Lemma All_local_env_prod_inv :
    forall P Q Γ,
      All_local_env (fun Δ A t => P Δ A t × Q Δ A t) Γ ->
      All_local_env P Γ × All_local_env Q Γ.
  Proof.
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
      All_local_env (lift_typing (fun Σ Γ t A => P Σ Γ t A × Q Σ Γ t A) Σ) Δ ->
      All_local_env (lift_typing P Σ) Δ × All_local_env (lift_typing Q Σ) Δ.
  Proof.
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
