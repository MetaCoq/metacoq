(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils Universes BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICReflect
                          PCUICLiftSubst PCUICUnivSubst PCUICEquality.

From MetaCoq Require Export LibHypsNaming.

Require Import String.
Require Import Wf Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

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

Definition subst_context s k (Γ : context) : context :=
  fold_context (fun k' => subst s (k' + k)) Γ.

Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
Proof.
  induction Γ as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
Qed.

Fixpoint smash_context (Γ Γ' : context) : context :=
  match Γ' with
  | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
  | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d])%list Γ'
  | [] => Γ
  end.

Lemma smash_context_length Γ Γ' : #|smash_context Γ Γ'| = #|Γ| + context_assumptions Γ'.
Proof.
  induction Γ' as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - now rewrite IHtl subst_context_length.
  - rewrite IHtl app_length. simpl. lia.
Qed.

(** ** Environment lookup *)

Definition global_decl_ident d :=
  match d with
  | ConstantDecl id _ => id
  | InductiveDecl id _ => id
  end.

Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (global_decl_ident hd) then Some hd
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_env) (id : ident) decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl id decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl mind decl).

Definition declared_inductive Σ mdecl ind decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
  declared_inductive Σ mdecl (fst cstr) idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

Definition declared_projection Σ mdecl idecl (proj : projection) pdecl : Prop :=
  declared_inductive Σ mdecl (fst (fst proj)) idecl /\
  List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl /\
  mdecl.(ind_npars) = snd (fst proj).

(* TODO fix lookup env *)
Lemma lookup_env_cst_inv {Σ c k cst} :
  lookup_env Σ c = Some (ConstantDecl k cst) -> c = k.
Proof.
  induction Σ. simpl. discriminate.
  simpl. destruct AstUtils.ident_eq eqn:Heq. intros [= ->]. simpl in Heq.
  now destruct (AstUtils.ident_eq_spec c k). auto.
Qed.

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
  | Some d =>
    if isLambda d.(dbody) then
      Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
    else None (* We don't unfold ill-formed fixpoints, which would
                 render confluence unprovable, creating an infinite
                 number of critical pairs between unfoldings of fixpoints.
                 e.g. [fix f := f] is not allowed. *)
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

Definition tDummy := tVar "".

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

Notation on_Trel_eq R f g :=
  (fun x y => (R (f x) (f y) * (g x = g y)))%type.

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
| case_red_brs ind p c brs brs' : OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs brs' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

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

       (forall (Γ : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args : list term)
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

       (forall (Γ : context) (c : ident) (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : universe_instance, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance_constr u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (k : nat) (u : universe_instance)
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

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.


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

Definition instantiate_params params pars ty :=
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
Definition build_branches_type ind mdecl idecl params u p :=
  let inds := inds (inductive_mind ind) u mdecl.(ind_bodies) in
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
  = let inds := inds (inductive_mind ind) u mdecl.(ind_bodies) in
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

(* [params], [p], [pty] and output already instanciated by [u] *)
Definition types_of_case ind mdecl idecl params u p pty :=
  let brtys := build_branches_type ind mdecl idecl params u p in
  match instantiate_params (subst_instance_context u mdecl.(ind_params)) params (subst_instance_constr u idecl.(ind_type)) with
  | Some ity =>
    match
      destArity [] ity,
      destArity [] pty,
      map_option_out brtys
    with
    | Some (args, s), Some (args', s'), Some brtys =>
      Some (args, args', s', brtys)
    | _, _, _ => None
    end
  | None => None
  end.

Lemma types_of_case_spec ind mdecl idecl pars u p pty indctx pctx ps btys :
  types_of_case ind mdecl idecl pars u p pty
  = Some (indctx, pctx, ps, btys)
  <~> ∑ s', option_map (destArity [])
                     (instantiate_params (subst_instance_context u (ind_params mdecl)) pars (subst_instance_constr u (ind_type idecl)))
          = Some (Some (indctx, s'))
          /\ destArity [] pty = Some (pctx, ps)
          /\ map_option_out (build_branches_type ind mdecl idecl pars u p)
            = Some btys.
Proof.
  unfold types_of_case.
  repeat (destruct ?; cbn).
  all: split; [try discriminate; inversion 1; subst; eexists; repeat split|].
  all: intros [s' [HH1 [HH2 HH3]]]; inversion HH1; inversion HH2; now inversion HH3.
Qed.

Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl  _ cb => F cb.(cst_universes)
  | InductiveDecl _ mb => F mb.(ind_universes)
  end.

Definition monomorphic_udecl_decl := on_udecl_decl monomorphic_udecl.

Definition monomorphic_levels_decl := fst ∘ monomorphic_udecl_decl.

Definition monomorphic_constraints_decl := snd ∘ monomorphic_udecl_decl.

Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

(* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

Definition LevelSet_pair x y
  := LevelSet.add y (LevelSet.singleton x).

Lemma LevelSet_pair_In x y z :
  LevelSet.In x (LevelSet_pair y z) -> x = y \/ x = z.
Proof.
  intro H. apply LevelSetFact.add_iff in H.
  destruct H; [intuition|].
  apply LevelSetFact.singleton_1 in H; intuition.
Qed.

Definition global_levels (Σ : global_env) : LevelSet.t
  := fold_right (fun decl lvls => LevelSet.union (monomorphic_levels_decl decl) lvls)
                (LevelSet_pair Level.lSet Level.lProp) Σ.

Lemma global_levels_Set Σ :
  LevelSet.mem Level.lSet (global_levels Σ) = true.
Proof.
  induction Σ; simpl. reflexivity.
  apply LevelSet.mem_spec, LevelSet.union_spec; right.
  now apply LevelSet.mem_spec in IHΣ.
Qed.

Lemma global_levels_Prop Σ :
  LevelSet.mem Level.lProp (global_levels Σ) = true.
Proof.
  induction Σ; simpl. reflexivity.
  apply LevelSet.mem_spec, LevelSet.union_spec; right.
  now apply LevelSet.mem_spec in IHΣ.
Qed.

(** One can compute the constraints associated to a global environment or its
    extension by folding over its constituent definitions.

    We make *only* the second of these computations an implicit coercion
    for more readability. Note that [fst_ctx] is also a coercion which goes
    from a [global_env_ext] to a [global_env]: coercion coherence would *not*
    be ensured if we added [global_constraints] as well as a coercion, as it
    would forget the extension's constraints. *)

Definition global_constraints (Σ : global_env) : constraints
  := fold_right (fun decl ctrs => ConstraintSet.union
                                (monomorphic_constraints_decl decl) ctrs)
               ConstraintSet.empty Σ.

Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t
  := LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1).

Definition global_ext_constraints (Σ : global_env_ext) : constraints
  := ConstraintSet.union (constraints_of_udecl (snd Σ))
                         (global_constraints Σ.1).
Coercion global_ext_constraints : global_env_ext >-> constraints.

Lemma prop_global_ext_levels Σ : LevelSet.In Level.prop (global_ext_levels Σ).
Proof.
  destruct Σ as [Σ φ]; cbn.
  apply LevelSetFact.union_3. cbn -[global_levels]; clear φ.
  induction Σ.
  - cbn. now apply LevelSetFact.add_1.
  - simpl. now apply LevelSetFact.union_3.
Qed.


(** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : constraints) uctx (u : universe_instance) :=
  match uctx with
  | Monomorphic_ctx c => List.length u = 0
  | Polymorphic_ctx c
  | Cumulative_ctx (c, _) => (* FIXME Cumulative *)
    (* no prop levels in instances *)
    forallb (negb ∘ Level.is_prop) u /\
    (* levels of the instance already declared *)
    forallb (fun l => LevelSet.mem l lvs) u /\
    List.length u = List.length c.1 /\
    valid_constraints φ (subst_instance_cstrs u c.2)
  end.

Definition consistent_instance_ext `{checker_flags} Σ
  := consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).


Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

(** *** Conversion

   Defined as cumulativity in both directions.
 *)

Definition conv `{checker_flags} Σ Γ T U : Type :=
  (Σ ;;; Γ |- T <= U) * (Σ ;;; Γ |- U <= T).

Notation " Σ ;;; Γ |- t = u " := (conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.

Definition check_correct_arity `{checker_flags} φ decl ind u ctx pars pctx :=
  let inddecl :=
      {| decl_name := nNamed decl.(ind_name);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|ctx|) pars ++ to_extended_list ctx) |}
  in eq_context φ (inddecl :: ctx) pctx.

(** ** Typing relation *)

Section TypeLocal.
  Context (typing : forall (Γ : context), term -> option term -> Type).

  Inductive All_local_env : context -> Type :=
  | localenv_nil :
      All_local_env []

  | localenv_cons_abs Γ na t :
      All_local_env Γ ->
      typing Γ t None ->
      All_local_env (Γ ,, vass na t)

  | localenv_cons_def Γ na b t :
      All_local_env Γ ->
      typing Γ t None ->
      typing Γ b (Some t) ->
      All_local_env (Γ ,, vdef na b t).
End TypeLocal.

Arguments localenv_nil {_}.
Arguments localenv_cons_def {_ _ _ _ _} _ _.
Arguments localenv_cons_abs {_ _ _ _} _ _.

(** Well-formedness of local environments embeds a sorting for each variable *)

Definition lift_typing (P : global_env_ext -> context -> term -> term -> Type) :
  (global_env_ext -> context -> term -> option term -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : universe & P Σ Γ t (tSort s) }
    end.

Definition on_local_decl (P : context -> term -> option term -> Type) Γ d :=
  match d.(decl_body) with
  | Some b => P Γ b (Some d.(decl_type))
  | None => P Γ d.(decl_type) None
  end.

Section TypeLocalOver.
  Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
  Context (property : forall (Σ : global_env_ext) (Γ : context),
              All_local_env (lift_typing typing Σ) Γ ->
              forall (t T : term), typing Σ Γ t T -> Type).

  Inductive All_local_env_over (Σ : global_env_ext) :
    forall (Γ : context), All_local_env (lift_typing typing Σ) Γ -> Type :=
  | localenv_over_nil :
      All_local_env_over Σ [] localenv_nil

  | localenv_over_cons_abs Γ na t
      (all : All_local_env (lift_typing typing Σ) Γ) :
      All_local_env_over Σ Γ all ->
      forall (tu : lift_typing typing Σ Γ t None),
        property Σ Γ all _ _ (projT2 tu) ->
        All_local_env_over Σ (Γ ,, vass na t)
                           (localenv_cons_abs all tu)

  | localenv_over_cons_def Γ na b t
      (all : All_local_env (lift_typing typing Σ) Γ) (tb : typing Σ Γ b t) :
      All_local_env_over Σ Γ all ->
      property Σ Γ all _ _ tb ->
      forall (tu : lift_typing typing Σ Γ t None),
        property Σ Γ all _ _ (projT2 tu) ->
        All_local_env_over Σ (Γ ,, vdef na b t)
                           (localenv_cons_def all tu tb).
End TypeLocalOver.

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

Axiom ind_guard : mutual_inductive_body -> bool.

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

| type_Case ind u npar p c brs args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys) ->
    check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx ->
    existsb (leb_sort_family (universe_family ps)) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    All2 (fun x y => (fst x = fst y) * (Σ ;;; Γ |- snd x : snd y) * (Σ ;;; Γ |- snd y : tSort ps)) brs btys ->
    Σ ;;; Γ |- tCase (ind, npar) p c brs : mkApps p (List.skipn npar args ++ [c])

| type_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance_constr u ty)

| type_Fix mfix n decl :
    let types := fix_context mfix in
    fix_guard mfix ->
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) (Γ ,,, types) ->
    All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))
    * (isLambda d.(dbody) = true)%type) mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    allow_cofix ->
    let types := fix_context mfix in
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) (Γ ,,, types) ->
    All (fun d => Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype)) mfix ->
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

Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
  { s : _ & Σ ;;; Γ |- t : tSort s }.

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

(** *** Typing of inductive declarations *)

Section GlobalMaps.
  Context {cf: checker_flags}.
  Context (P : global_env_ext -> context -> term -> option term -> Type).

  Section TypeCtx.

    (** For well-formedness of inductive declarations we need a way to check that a given
        context is typable in [Prop]. *)
    Context (Σ : global_env_ext) (Γ : context).

    Fixpoint type_local_ctx (Δ : context) (u : universe) : Type :=
      match Δ with
      | [] => u = Universe.type0m
      | {| decl_body := None; decl_type := t |} :: Δ => (type_local_ctx Δ u * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some _ |} :: Δ => type_local_ctx Δ u
      end.
  End TypeCtx.

  Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

  Definition on_type Σ Γ T := P Σ Γ T None.

  Record constructor_shape mdecl i idecl cdecl :=
    { cshape_args : context;
      (* Arguments (with lets) *)
      cshape_args_univ : universe;
      (* The argument's context must be well-typed in some universe. *)
      cshape_concl_head := tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|cshape_args|);
      (* Conclusion head: reference to the current inductive in the block *)
      cshape_indices : list term;
      (* Indices of the constructor, whose length should be the real arguments length of the inductive *)
      cshape_eq : snd (fst cdecl) =
                  it_mkProd_or_LetIn mdecl.(ind_params)
                 (it_mkProd_or_LetIn cshape_args
                  (mkApps cshape_concl_head (to_extended_list_k mdecl.(ind_params) #|cshape_args| ++ cshape_indices)))
      (* The type of the constructor canonically has this shape: parameters, real arguments ending
         with a reference to the inductive applied to the (non-lets) parameters and arguments *)
    }.
  Arguments cshape_args {mdecl i idecl cdecl}.
  Arguments cshape_args_univ {mdecl i idecl cdecl}.

  Definition on_constructor (Σ : global_env_ext) (mind : kername)
             (mdecl : mutual_inductive_body)
             (i : nat) (idecl : one_inductive_body)
             (c : nat) (cdecl : ident * term * nat) : Type :=
    let constructor_type := snd (fst cdecl) in
    on_type Σ (arities_context mdecl.(ind_bodies)) constructor_type *
    { cs : constructor_shape mdecl i idecl cdecl &
           type_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                          cs.(cshape_args) cs.(cshape_args_univ) }.

  Definition on_constructors (Σ : global_env_ext) mind mdecl i idecl l :=
    Alli (on_constructor Σ mind mdecl i idecl) 0 l.

  (** Projections have their parameter context smashed to avoid costly computations
      during type-checking. *)

  Definition on_projection (Σ : global_env_ext) mind mdecl (i : nat) (idecl : one_inductive_body)
             (k : nat) (p : ident * term) :=
    let ctx := smash_context [] mdecl.(ind_params) in
    let Γ := ctx,, vass (nNamed idecl.(ind_name))
                (mkApps (tInd (mkInd mind i) (polymorphic_instance mdecl.(ind_universes)))
                        (to_extended_list ctx))
    in on_type Σ Γ (snd p).

  Record on_projections (Σ : global_env_ext) mind mdecl i idecl (ictx : context) (l : list (ident * term)) : Type :=
    { on_projs_record : #|idecl.(ind_ctors)| = 1;
      (** The inductive must be a record *)
      on_projs_noidx : #|ictx| = 0;
      (** The inductive cannot have indices *)
      on_projs_elim : List.Exists (fun sf => sf = InType) idecl.(ind_kelim);
      (** This ensures that all projections are definable *)
      on_projs : Alli (on_projection Σ mind mdecl i idecl) 0 l }.

  Definition is_prop_elim l :=
    match l with
    | [InProp] => true
    | _ => false
    end.

  Definition is_all_elim l :=
    match l with
    | [InProp;InSet;InType] => true
    | _ => false
    end.

  Section CheckSmaller.
    Context {Σ : global_env_ext} {mind : kername} {mdecl : mutual_inductive_body}
            {i : nat} {idecl : one_inductive_body} (indu : universe).

    Fixpoint check_constructors_smaller {k cstrs}
             (onConstructors : Alli (on_constructor Σ mind mdecl i idecl) k cstrs) : Prop :=
      match onConstructors with
      | Alli_nil => True
      | Alli_cons cstr l onc cstrs =>
        (* The constructor's arguments bounding universe. *)
        let cstru := cshape_args_univ (snd onc).π1 in
        (* Just check it is smaller and continue *)
        leq_universe (global_ext_constraints Σ) cstru indu /\ check_constructors_smaller cstrs
      end.
  End CheckSmaller.


  (** This ensures that all sorts in kelim are lower
      or equal to the top elimination sort, if set.
      For inductives in Type we do not check [kelim] currently. *)

  Definition check_ind_sorts {Σ mind mdecl i idecl cstrs}
             (onConstructors : on_constructors Σ mind mdecl i idecl cstrs) u : Prop :=
    match universe_family u with
    | InProp =>
      (** The inductive is declared in the impredicative sort Prop *)
      let topsort :=
          match onConstructors with
          | Alli_nil => (* Empty inductive proposition: *) InType
          | Alli_cons cstr nil onc Alli_nil =>
            match universe_family (cshape_args_univ (snd onc).π1) with
            | InProp => (* Not squashed: all arguments are in Prop *) InType
            | _ => (* Squashed: some arguments are higher than Prop, restrict to Prop *) InProp
            end
          | _ => (* Squashed: at least 2 constructors *) InProp
          end
      in
      (** No universe-checking to do: any size of constructor argument is allowed,
          however elimination restrictions apply. *)
      forall x, In x idecl.(ind_kelim) -> leb_sort_family x topsort
    | _ =>
      (** The inductive is predicative: check that all constructors arguments are
          smaller than the declared universe. *)
      check_constructors_smaller u onConstructors
    end.

  Record on_ind_body
         (Σ : global_env_ext) (mind : kername) mdecl (i : nat) idecl :=
    { (** The type of the inductive must be an arity, sharing the same params
          as the rest of the block, and maybe having a contexxt of indices. *)
      ind_indices : context; ind_sort : universe;
      ind_arity_eq : idecl.(ind_type) = it_mkProd_or_LetIn mdecl.(ind_params)
                                       (it_mkProd_or_LetIn ind_indices (tSort ind_sort));
      (** It must be well-typed in the empty context. *)
      onArity : on_type Σ [] idecl.(ind_type);
      (** Constructors are well-typed *)
      onConstructors : on_constructors Σ mind mdecl i idecl idecl.(ind_ctors);
      (** Projections, if any, are well-typed *)
      onProjections : idecl.(ind_projs) <> [] -> on_projections Σ mind mdecl i idecl ind_indices idecl.(ind_projs);
      (** The universes and elimination sorts must be correct w.r.t.
          the universe of the inductive and the universes in its constructors, which
          are declared in [on_constructors]. *)
      ind_sorts : check_ind_sorts onConstructors ind_sort;
    }.

  Definition on_context Σ ctx :=
    All_local_env (P Σ) ctx.

  (** We allow empty blocks for simplicity (no well-typed reference to them can be made). *)

  Record on_inductive Σ ind mdecl :=
    { onInductives : Alli (on_ind_body Σ ind mdecl) 0 mdecl.(ind_bodies);
      (** We check that the context of parameters is well-formed and that
          the size annotation counts assumptions only (no let-ins). *)
      onParams : on_context Σ mdecl.(ind_params);
      onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
      onGuard : ind_guard mdecl
    }.

  (** *** Typing of constant declarations *)

  Definition on_constant_decl Σ d :=
    match d.(cst_body) with
    | Some trm => P Σ [] trm (Some d.(cst_type))
    | None => on_type Σ [] d.(cst_type)
    end.

  Definition on_global_decl Σ decl :=
    match decl with
    | ConstantDecl id d => on_constant_decl Σ d
    | InductiveDecl ind inds => on_inductive Σ ind inds
    end.

  (** *** Typing of global environment

      All declarations should be typeable and the global
      set of universe constraints should be consistent. *)

  (** Well-formed global environments have no name clash. *)

  Definition fresh_global (s : string) : global_env -> Prop :=
    Forall (fun g => global_decl_ident g <> s).

  Definition satisfiable_udecl `{checker_flags} Σ φ
    := consistent (global_ext_constraints (Σ, φ)).

  (* Check that: *)
  (*   - declared levels are fresh *)
  (*   - all levels used in constraints are declared *)
  (*   - level used in monomorphic contexts are only monomorphic *)
  Definition on_udecl `{checker_flags} Σ (udecl : universes_decl)
    := let levels := levels_of_udecl udecl in
       let global_levels := global_levels Σ in
       let all_levels := LevelSet.union levels global_levels in
       LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
       /\ ConstraintSet.For_all (fun '(l1,_,l2) => LevelSet.In l1 all_levels
                                               /\ LevelSet.In l2 all_levels)
                               (constraints_of_udecl udecl)
       /\ match udecl with
         | Monomorphic_ctx ctx =>  LevelSet.for_all (negb ∘ Level.is_var) ctx.1
         | _ => True
         end
       /\ satisfiable_udecl Σ udecl.


  Inductive on_global_env `{checker_flags} : global_env -> Type :=
  | globenv_nil : on_global_env []
  | globenv_decl Σ d :
      on_global_env Σ ->
      fresh_global (global_decl_ident d) Σ ->
      let udecl := universes_decl_of_decl d in
      on_udecl Σ udecl ->
      on_global_decl (Σ, udecl) d ->
      on_global_env (Σ ,, d).

  Definition on_global_env_ext `{checker_flags} (g : global_env_ext) :=
    on_global_env (fst g) × on_udecl (fst g) (snd g).

End GlobalMaps.

Arguments cshape_args {mdecl i idecl cdecl}.
Arguments cshape_args_univ {mdecl i idecl cdecl}.
Arguments ind_indices {_ P Σ mind mdecl i idecl}.
Arguments ind_sort {_ P Σ mind mdecl i idecl}.
Arguments ind_arity_eq {_ P Σ mind mdecl i idecl}.
Arguments onArity {_ P Σ mind mdecl i idecl}.
Arguments onConstructors {_ P Σ mind mdecl i idecl}.
Arguments onProjections {_ P Σ mind mdecl i idecl}.
Arguments ind_sorts {_ P Σ mind mdecl i idecl}.

Lemma All_local_env_impl (P Q : context -> term -> option term -> Type) l :
  All_local_env P l ->
  (forall Γ t T, P Γ t T -> Q Γ t T) ->
  All_local_env Q l.
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

Lemma All_local_env_skipn P Γ : All_local_env P Γ -> forall n, All_local_env P (skipn n Γ).
Proof.
  induction 1; simpl; intros; destruct n; simpl; try econstructor; eauto.
Qed.
Hint Resolve All_local_env_skipn : wf.

Lemma Alli_impl_trans : forall (A : Type) (P Q : nat -> A -> Type) (l : list A) (n : nat),
Alli P n l -> (forall (n0 : nat) (x : A), P n0 x -> Q n0 x) -> Alli Q n l.
Proof.
  intros. induction X; simpl; constructor; auto.
Defined.

Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> term -> option term -> Type) Σ Γ Δ u :
  type_local_ctx P Σ Γ Δ u ->
  (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
  type_local_ctx Q Σ Γ Δ u.
Proof.
  intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  intros. intuition auto.
Qed.

(** This predicate enforces that there exists typing derivations for every typable term in env. *)

Definition Forall_decls_typing `{checker_flags}
           (P : global_env_ext -> context -> term -> term -> Type)
  := on_global_env (lift_typing P).

(** *** Typing of local environments *)

Definition type_local_decl `{checker_flags} Σ Γ d :=
  match d.(decl_body) with
  | None => isType Σ Γ d.(decl_type)
  | Some body => Σ ;;; Γ |- body : d.(decl_type)
  end.

(** ** Induction principle for typing up-to a global environment *)

Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
Proof. now intros Ht ->. Qed.

Section wf_local.
  Context `{checker_flags}.

  Definition wf_local_rel Σ Γ Γ'
    := (All_local_env (lift_typing (fun Σ0 Γ0 t T => Σ0 ;;; Γ ,,, Γ0 |- t : T) Σ) Γ').

  Definition wf_local_rel_nil {Σ Γ} : wf_local_rel Σ Γ []
    := localenv_nil.

  Definition wf_local_rel_abs {Σ Γ Γ' A na} :
    wf_local_rel Σ Γ Γ' -> {u & Σ ;;; Γ ,,, Γ' |- A : tSort u }
    -> wf_local_rel Σ Γ (Γ',, vass na A)
    := localenv_cons_abs.

  Definition wf_local_rel_def {Σ Γ Γ' t A na} :
    wf_local_rel Σ Γ Γ'
    -> isType Σ (Γ ,,, Γ') A
    -> Σ ;;; Γ ,,, Γ' |- t : A
    -> wf_local_rel Σ Γ (Γ',, vdef na t A)
    := localenv_cons_def.

  Lemma wf_local_rel_local Σ Γ :
    wf_local Σ Γ -> wf_local_rel Σ [] Γ.
  Proof.
    intro X. eapply All_local_env_impl. exact X.
    intros Γ0 t [] X0; cbn; rewrite app_context_nil_l; assumption.
  Defined.

  Lemma wf_local_local_rel Σ Γ :
    wf_local_rel Σ [] Γ -> wf_local Σ Γ.
  Proof.
    intro X. eapply All_local_env_impl. exact X.
    intros Γ0 t [] XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
  Defined.

End wf_local.

Section wf_local_size.
  Context `{checker_flags} (Σ : global_env_ext).
  Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), typing Σ Γ t T -> size).

  Fixpoint wf_local_size Γ (w : wf_local Σ Γ) : size :=
    match w with
    | localenv_nil => 0

    | localenv_cons_abs Γ na t wfΓ tty =>
      (fn _ _ t _ (projT2 tty) + wf_local_size _ wfΓ)%nat

    | localenv_cons_def Γ na b t wfΓ tty tty' =>
      (fn _ _ t _ (projT2 tty) + fn _ _ b t tty' + wf_local_size _ wfΓ)%nat
    end.
End wf_local_size.

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
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (Nat.max d1 (Nat.max d2
                                (all2_size _ (fun x y p => Nat.max (typing_size Σ Γ (snd x) (snd y) (snd (fst p))) (typing_size _ _ _ _ (snd p))) a)))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ (fst p)) a0))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ p) a0))).
  destruct s. red in i.
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

Hint Resolve wf_ext_wf.

Lemma wf_ext_consistent {cf:checker_flags} Σ :
  wf_ext Σ -> consistent Σ.
Proof.
  intros [? [? [? [? ?]]]]; assumption.
Qed.

Hint Resolve wf_ext_consistent.


Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) :=
  forall Σ (wfΣ : wf Σ.1) Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T ->
    Forall_decls_typing P Σ.1 * P Σ Γ t T.

Lemma env_prop_typing `{checker_flags} P : env_prop P ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma type_Prop `{checker_flags} Σ : Σ ;;; [] |- tSort Universe.type0m : tSort Universe.type1.
  repeat constructor.
  apply prop_global_ext_levels.
Defined.

Lemma env_prop_sigma `{checker_flags} P : env_prop P ->
  forall Σ (wfΣ : wf Σ), Forall_decls_typing P Σ.
Proof.
  intros. red in X. eapply (X (empty_ext Σ)).
  apply wfΣ. constructor.
  apply type_Prop.
Defined.

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

Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
  wf_local_size Σ (@typing_size _) _ (wf_local_app _ _ _ Hwf) <=
  wf_local_size Σ (@typing_size _) _ Hwf.
Proof.
  induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
  depelim Hwf. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ Hwf). lia.
  specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. simpl. lia.
Qed.

Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  wf_local_size Σ (@typing_size _) _ (typing_wf_local d) < typing_size d.
Proof.
  induction d; simpl; try lia.
  pose proof (size_wf_local_app _ _ a).
  eapply Nat.le_lt_trans. eauto. subst types. lia.
  pose proof (size_wf_local_app _ _ a).
  eapply Nat.le_lt_trans. eauto. subst types. lia.
  destruct s as [s | [u Hu]]; try lia.
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
    simpl. lia.
  - intros [=]. subst d Γ0.
    exists w. simpl. simpl in l. destruct l as [u h].
    simpl in l0.
    exists u, l0, h. simpl.
    pose (typing_size_pos h).
    pose (typing_size_pos l0).
    lia.
Qed.


(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T),
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        P Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : universe),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term)
            (s1 : universe) (bty : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b b_ty b' : term)
            (s1 : universe) (b'_ty : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u,
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tProd na A B -> P Σ Γ t (tProd na A B) ->
        Σ ;;; Γ |- u : A -> P Σ Γ u A ->
        P Σ Γ (tApp t u) (B{0 := u})) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : ident) u (decl : constant_body),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing P Σ.1 -> All_local_env_over typing Pdecl Σ Γ wfΓ ->
        ind_npars mdecl = npar ->
        let pars := firstn npar args in
        forall (pty : term), Σ ;;; Γ |- p : pty ->
        forall indctx pctx ps btys,
        types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys) ->
        check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx ->
        existsb (leb_sort_family (universe_family ps)) (ind_kelim idecl) ->
        P Σ Γ p pty ->
        Σ;;; Γ |- c : mkApps (tInd ind u) args ->
        P Σ Γ c (mkApps (tInd ind u) args) ->
        All2 (fun x y : nat * term =>
                (fst x = fst y) *
                (Σ;;; Γ |- snd x : snd y) *
                P Σ Γ (snd x) (snd y) *
                (Σ ;;; Γ |- snd y : tSort ps) *
                P Σ Γ (snd y) (tSort ps)
        )%type brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
        Forall_decls_typing P Σ.1 -> All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        fix_guard mfix ->
        All_local_env (lift_typing (fun Σ Γ b ty =>
                         (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ) (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
                   (isLambda d.(dbody) = true)%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        All_local_env (lift_typing (fun Σ Γ b ty => (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ) (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        allow_cofix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        (isWfArity_prop typing Pdecl Σ Γ B + {s & (Σ ;;; Γ |- B : tSort s) * P Σ Γ B (tSort s)})%type ->
        Σ ;;; Γ |- A <= B ->
        P Σ Γ t B) ->

       env_prop P.
Proof.
  intros P Pdecl; unfold env_prop.
  intros X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ wfΓ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
   otherwise it takes forever to execure the "pose", for some reason *)
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & { wfΓ : wf_local Σ Γ &
                          { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}})) as p0.
  specialize (p0 (lexprod (MR lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => MR lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 (projT2 x))))))))) as p.
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ wfΓ (existT _ t (existT _ _ H))))) : { Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & { wfΓ & { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}}).
  change Σ with (projT1 foo).
  change Γ with (projT1 (projT2 (projT2 foo))).
  change t with (projT1 (projT2 (projT2 (projT2 (projT2 foo))))).
  change T with (projT1 (projT2 (projT2 (projT2 (projT2 (projT2 foo)))))).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_lexprod; intros; apply measure_wf; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ wfΓ t T H.
  intros (Σ & wfΣ & Γ & wfΓ & t & t0 & H). simpl.
  intros IH. unfold MR in IH. simpl in IH.
  split.
  destruct Σ as [Σ φ]. destruct Σ.
  constructor.
  cbn in wfΣ; inversion_clear wfΣ. auto.
  inv wfΣ.
  rename X14 into Xg.
  constructor; auto. unfold Forall_decls_typing in IH.
  - simple refine (let IH' := IH ((Σ, udecl); (X13; []; _; (tSort Universe.type0m ); _; _)) in _).
    constructor. shelve. apply type_Prop.
    cbn in IH'; forward IH'. constructor 1; cbn. lia.
    apply IH'; auto.
  - simpl. simpl in *.
    destruct g; simpl.
    + destruct c; simpl in *.
      destruct cst_body; simpl in *.
      simpl.
      intros. red in Xg. simpl in Xg.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Xg))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia.
      apply IH.
      red. simpl. red in Xg; simpl in Xg.
      destruct Xg as [s Hs]. red. simpl.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Hs))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia. exists s. eapply IH.
    + red in Xg.
      destruct Xg as [onI onP onnp]; constructor; eauto.
      eapply Alli_impl; eauto. clear onI onP onnp; intros n x Xg.
      unshelve eexists (ind_indices Xg) (ind_sort Xg) _.
      ++ apply onConstructors in Xg.
         eapply Alli_impl_trans; eauto. intros.
         red in X14 |- *. destruct X14 as [[s Hs] [cs Hargsu]]. split; auto.
         pose proof (typing_wf_local (Σ:= (Σ, udecl)) Hs). simpl in Hs.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. red. simpl. exists s. simpl. apply IH; constructor 1; simpl; auto with arith.
         exists cs.
         eapply type_local_ctx_impl; eauto. simpl. intros. red in X14.
         destruct T.
         pose proof (typing_wf_local X14).
         specialize (IH ((Σ, udecl); (X13; _; X17; _; _; X14))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
         destruct X14 as [u Hu]. exists u.
         pose proof (typing_wf_local Hu).
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hu))))))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
      ++ apply (ind_arity_eq Xg).
      ++ apply onArity in Xg. destruct Xg as [s Hs]. exists s; auto.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. simpl. apply IH; constructor 1; simpl; lia.
      ++ intros Hprojs; pose proof (onProjections Xg Hprojs); auto. simpl in *.
         destruct X14; constructor; auto. eapply Alli_impl; eauto. clear on_projs0. intros.
         red in X14 |- *. unfold on_type in *; intuition eauto. simpl in *.
         destruct X14 as [s Hs]. exists s.
         pose proof (typing_wf_local (Σ:= (Σ, udecl)) Hs).
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. apply IH; constructor 1; simpl; lia.
      ++ destruct Xg. simpl. unfold check_ind_sorts in *. destruct universe_family; auto.
         +++ simpl. unfold Alli_impl_trans. clear -ind_sorts0. revert onConstructors0 ind_sorts0.
             generalize (ind_ctors x).
             intros ? onConstructors0. depelim onConstructors0; simpl; auto.
             depelim onConstructors0; simpl; auto. red in o. destruct o as [[s Hs] [cshape Hcs]]; simpl; auto.
         +++ simpl. revert onConstructors0 ind_sorts0.
             generalize (ind_ctors x).
             intros ? onConstructors0. clear. red in onConstructors0.
             unfold Alli_impl_trans. simpl. induction onConstructors0; simpl; intuition auto.
             destruct p as [[? ?] [? ?]]. simpl in *. auto.
         +++ simpl. revert onConstructors0 ind_sorts0.
             generalize (ind_ctors x).
             intros ? onConstructors0. clear. red in onConstructors0.
             unfold Alli_impl_trans. simpl. induction onConstructors0; simpl; intuition auto.
             destruct p as [[? ?] [? ?]]. simpl in *. auto.
      ++ red in onP |- *.
         eapply All_local_env_impl; eauto.
         intros. destruct T; simpl in X14.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ, udecl)) X14)
                                                                           (existT _ _ (existT _ _ X14))))))).
         simpl in IH. apply IH. constructor 1. simpl. lia.
         destruct X14 as [u Hu].
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ, udecl)) Hu)
                                                                           (existT _ _ (existT _ _ Hu))))))).
         simpl in IH. simpl. exists u. apply IH. constructor 1. simpl. lia.

  - assert (forall Γ (wfΓ : wf_local Σ Γ) t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               Forall_decls_typing P Σ.1 * P Σ Γ t T).
    intros.
    specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ wfΓ0 (existT _ _ (existT _ _ Hty))))))).
    simpl in IH.
    forward IH.
    constructor 2. simpl. apply H0.
    apply IH. clear IH.
    rename X13 into X14.

    assert (All_local_env_over typing Pdecl Σ Γ (typing_wf_local H)).
    { clear -Pdecl wfΓ wfΣ X14.
      pose proof (typing_wf_local_size H). clear wfΓ.
      set (foo := typing_wf_local H) in *.
      clearbody foo.
      revert foo H0. generalize Γ at 1 2 4.
      induction foo; simpl in *; try destruct t2 as [u Hu]; simpl in *; constructor.
      - simpl in *. apply IHfoo. lia.
      - red. eapply (X14 _ foo _ _ Hu). lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ foo _ _ t3). lia.
      - red. apply (X14 _ foo _ _ Hu). lia. }

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
       end; eauto;
         unshelve eapply X14; simpl; auto with arith.
       econstructor; simpl; eauto.

    -- match reverse goal with
         H : _ |- _ => eapply H
       end.
       all: eauto.
       ++ unshelve eapply X14. all: eauto. simpl. lia.
       ++ unshelve eapply X14. all: eauto. simpl. lia.
       ++ unshelve eapply X14. all: eauto.
          ** econstructor ; eauto. eexists ; eauto.
          ** simpl. lia.

    -- eapply X5; eauto. simpl in X14.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X6; eauto. simpl in X14.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X7; eauto.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X8; eauto.
       eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith.
       eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith. simpl in *.
       eapply (X14 _ wfΓ _ _ H0); eauto. lia.
       clear X13. revert a wfΓ X14. simpl. clear. intros.
       induction a; simpl in *. constructor.
       destruct r as [[? ?] ?]. constructor. intuition eauto.
       eapply (X14 _ wfΓ _ _ t); eauto. simpl; auto with arith.
       lia.
       eapply (X14 _ wfΓ _ _ t0); eauto. simpl; auto with arith.
       lia.
       apply IHa. auto. intros.
       eapply (X14 _ wfΓ0 _ _ Hty). lia.

    -- eapply X9; eauto.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. pose (typing_size_pos H). lia. apply X14.
       unshelve eapply X14; eauto.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
       eapply X10; eauto; clear X10. simpl in *. subst types.
       remember (Γ ,,, fix_context mfix) as Γ'.
       assert( forall Γ : context,
                 wf_local Σ Γ ->
                 forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S ((wf_local_size Σ
                       (fun x (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                          typing_size x3) Γ' a)) ->
                   Forall_decls_typing P Σ.1 * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 a0.
       clear HeqΓ'. clear X13. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); simpl; eauto. lia.
       --- simpl. destruct t0. exists x. split; eauto.
           eapply (X _ a _ _ t0); eauto. simpl. lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- simpl. destruct t0 as [u t0].
           exists u. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                wf_local Σ Γ0 ->
               forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                typing_size Hty <
                      S
                        (all_size (fun x : def term => (Σ;;; Γ ,,, fix_context mfix |- dbody x : lift0 #|types| (dtype x))%type
                                                        * (isLambda (dbody x) = true)%type)%type
                                   (fun (x : def term) p => typing_size (fst p)) a0) ->
                       Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
           subst types. intros. eapply (X14 _ X _ _ Hty); eauto. lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl X13. clear i.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ (fst p)). simpl. lia.
       ++ eapply IHa0. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12 X13.
       eapply X11; eauto; clear X11. simpl in *. subst types.
       remember (Γ ,,, fix_context mfix) as Γ'.
       assert( forall Γ : context,
                 wf_local Σ Γ ->
                 forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S
                     (
                       (wf_local_size Σ
                                      (fun x (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                                         typing_size x3) Γ' a)) ->

                   Forall_decls_typing P Σ.1 * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 a0.
       clear HeqΓ'. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); simpl; eauto. lia.
       --- destruct t0. exists x. split; eauto.
           eapply (X _ a _ _ t0); eauto. simpl; lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- simpl. destruct t0 as [u t0].
           exists u. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                     wf_local Σ Γ0 ->
                     forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                       typing_size Hty <
                       S (all_size (fun x : def term => Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x)))
                                   (fun (x : def term) (p : Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x))) => typing_size p) a0) ->
                       Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
           intros. eapply (X14 _ X _ _ Hty); eauto. subst types; lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ p). simpl. lia.
       ++ eapply IHa0. intros.
         eapply (X _ X0 _ _ Hty). simpl; lia.
    -- eapply X12; eauto.
       ++ eapply (X14 _ wfΓ _ _ H); simpl. destruct s as [s | [u Hu]]; lia.
       ++ simpl in X14, X13.
          destruct s as [s | [u Hu]].
          ** left.
             red. exists s. red in s. revert X14.
             generalize (snd (projT2 (projT2 s))).
             induction a; simpl in *; intros X14 *; constructor.
             --- apply IHa. intros. eapply (X14 _ wfΓ0 _ _ Hty). lia.
             --- red. eapply (X14 _ a _ _ (projT2 t1)). lia.
             --- apply IHa. intros. eapply (X14 _ wfΓ0 _ _ Hty). lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
          ** auto. right.
             exists u. intuition.
Qed.


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


From Equations Require Import Equations.
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
    { Σ' & { wfΣ' : on_global_env P Σ'.1 & on_global_decl P Σ' decl } }.
  Proof.
    induction 1; simpl. congruence.
    destruct ident_eq. intros [= ->].
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
    wf_local_rel Σ Γ1 (Γ2 ,,, Γ3)
    -> wf_local_rel Σ Γ1 Γ2 * wf_local_rel Σ (Γ1 ,,, Γ2) Γ3.
  Proof.
    intros HH; apply All_local_env_app in HH.
    destruct HH as [H1 H2].
    split. exact H1. eapply All_local_env_impl. exact H2.
    intros Γ t [] X; cbn in *; now rewrite <- app_context_assoc.
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
    intros H1 H2. eapply All_local_env_app_inv.
    split. assumption.
    eapply All_local_env_impl. eassumption.
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
    | Some b => P b (Some d.(decl_type))
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
      + exists wfΓ. injection eq; intros <-. apply t1.
      + apply IHwfΓ. apply eq.
  Defined.

  Definition on_wf_local_decl {Σ Γ}
             (P : forall Σ Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T -> Type)
             (wfΓ : wf_local Σ Γ) {d} (H : on_local_decl_glob (lift_typing typing Σ Γ) d) :=
    match d as d' return (on_local_decl_glob (lift_typing typing Σ Γ) d') -> Type with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |} => fun H => P Σ Γ wfΓ b ty H
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
