(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast AstUtils univ Induction LiftSubst UnivSubst.
From Template Require Loader.
Require Import String.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.


(** * Typing derivations

  *WIP*

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)

(** ** Environment lookup *)

Definition global_decl_ident d :=
  match d with
  | ConstantDecl id _ => id
  | InductiveDecl id _ => id
  end.

Fixpoint lookup_env (Σ : global_declarations) (id : ident) : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (global_decl_ident hd) then Some hd
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_declarations) (id : ident) decl : Prop :=
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
  List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl.

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
  | Some a =>
    match a with
    | tConstruct _ _ _ => true
    | tApp (tConstruct _ _ _) _ => true
    | _ => false
    end
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

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).

(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Inductive red1 (Σ : global_declarations) (Γ : context) : term -> term -> Prop :=
(** Reductions *)
(** Beta *)
| red_beta na t b a l :
    red1 Σ Γ (tApp (tLambda na t b) (a :: l)) (mkApps (subst10 a b) l)

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
    red1 Σ Γ (tApp (tFix mfix idx) args) (tApp fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip (mkApps fn args) p brs)

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

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' : OnOne2 (fun x y => red1 Σ Γ (snd x) (snd y)) brs brs' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2)
| app_red_r M2 N2 M1 : OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na na' M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na' N1 M2)
| prod_red_r na na' M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na' M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)
| cast_red M1 k M2 : red1 Σ Γ (tCast M1 k M2) M1.

Lemma red1_ind_all :
  forall (Σ : global_declarations) (P : context -> term -> term -> Prop),
       (forall (Γ : context) (na : name) (t b a : term) (l : list term),
        P Γ (tApp (tLambda na t b) (a :: l)) (mkApps (b {0 := a}) l)) ->
       (forall (Γ : context) (na : name) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->
       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->
       (forall (Γ : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args : list term)
          (p : term) (brs : list (nat * term)),
        P Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs) (iota_red pars c args brs)) ->
       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (tApp (tFix mfix idx) args) (tApp fn args)) ->
       (forall (Γ : context) (ip : inductive * nat) (p : term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (nat * term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip (mkApps fn args) p brs)) ->
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
       (forall (Γ : context) (ind : inductive * nat) (p c c' : term) (brs : list (nat * term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->
       (forall (Γ : context) (ind : inductive * nat) (p c : term) (brs brs' : list (nat * term)),
           OnOne2 (fun x y : nat * term => red1 Σ Γ (snd x) (snd y) /\ P Γ (snd x) (snd y)) brs brs' ->
           P Γ (tCase ind p c brs) (tCase ind p c brs')) ->
       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' -> P Γ (tProj p c) (tProj p c')) ->
       (forall (Γ : context) (M1 N1 : term) (M2 : list term), red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tApp M1 M2) (mkApps N1 M2)) ->
       (forall (Γ : context) (M2 N2 : list term) (M1 : term), OnOne2 (fun x y => red1 Σ Γ x y /\ P Γ x y) M2 N2 -> P Γ (tApp M1 M2) (tApp M1 N2)) ->
       (forall (Γ : context) (na na' : name) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na' N1 M2)) ->
       (forall (Γ : context) (na na' : name) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na' M1 N2)) ->
       (forall (Γ : context) (ev : nat) (l l' : list term), OnOne2 (fun x y => red1 Σ Γ x y /\ P Γ x y) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->
       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tCast M1 k M2) (tCast N1 k M2)) ->
       (forall (Γ : context) (M2 : term) (k : cast_kind) (N2 M1 : term),
        red1 Σ Γ M2 N2 -> P Γ M2 N2 -> P Γ (tCast M1 k M2) (tCast M1 k N2)) ->
       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 : term),
        P Γ (tCast M1 k M2) M1) ->
       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros. revert Γ t t0 H24.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1; match goal with
              | |- P _ (tApp (tFix _ _) _) _ => idtac
              | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
              | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
              | H : _ |- _ => eapply H; eauto
              end.
  eapply H3; eauto.
  eapply H4; eauto.
  eapply H5; eauto.

  - revert brs brs' H24.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - revert M2 N2 H24.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - revert l l' H24.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.
Defined.

(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Prop :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

(** ** Term equality and cumulativity *)

Definition eq_string s s' :=
  if string_compare s s' is Eq then true else false.

Definition eq_ind i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eq_string i i' && Nat.eqb n n'.

Definition eq_constant := eq_string.

Definition eq_nat := Nat.eqb.
Definition eq_evar := eq_nat.
Definition eq_projection p p' :=
  let '(ind, pars, arg) := p in
  let '(ind', pars', arg') := p' in
  eq_ind ind ind' && eq_nat pars pars' && eq_nat arg arg'.

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

(** *** Universe comparisons *)

(** We try syntactic equality before checking the graph. *)

Definition eq_universe `{checker_flags} φ s s' :=
  if univ.Universe.equal s s' then true
  else uGraph.check_leq φ s s' && uGraph.check_leq φ s' s.

Definition leq_universe `{checker_flags} φ s s' :=
  if univ.Universe.equal s s' then true
  else uGraph.check_leq φ s s'.

Definition eq_universe_instance `{checker_flags} φ u v :=
  univ.Instance.equal_upto (uGraph.check_eq_level φ) u v.

(* ** Syntactic equality up-to universes

  We shouldn't look at printing annotations nor casts.
  It is however not possible to write a structurally recursive definition
  for syntactic equality up-to casts due to the [tApp (tCast f _ _) args] case.
  We hence implement first an equality which considers casts and do a stripping
  phase of casts before checking equality. *)

Fixpoint eq_term `{checker_flags} (φ : uGraph.t) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tMeta n, tMeta n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_evar ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => eq_universe φ s s'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tConst c u, tConst c' u' => eq_constant c c' && eq_universe_instance φ u u'
  | tInd i u, tInd i' u' => eq_ind i i' && eq_universe_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
                                                    && eq_universe_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && eq_term φ c c'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_ind ind ind' && eq_nat par par' &&
    eq_term φ p p' && eq_term φ c c' && forallb2 (fun '(a, b) '(a', b') => eq_term φ b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.

(* ** Syntactic cumulativity up-to universes

  We shouldn't look at printing annotations *)

Fixpoint leq_term `{checker_flags} (φ : uGraph.t) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tMeta n, tMeta n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_nat ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => leq_universe φ s s'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tConst c u, tConst c' u' => eq_constant c c' && eq_universe_instance φ u u'
  | tInd i u, tInd i' u' => eq_ind i i' && eq_universe_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k' &&
                                                    eq_universe_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && leq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && leq_term φ c c'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_ind ind ind' && eq_nat par par' &&
    eq_term φ p p' && eq_term φ c c' && forallb2 (fun '(a, b) '(a', b') => eq_term φ b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | _, _ => false
  end.

Fixpoint strip_casts t :=
  match t with
  | tEvar ev args => tEvar ev (List.map strip_casts args)
  | tLambda na T M => tLambda na (strip_casts T) (strip_casts M)
  | tApp u v => mkApps (strip_casts u) (List.map (strip_casts) v)
  | tProd na A B => tProd na (strip_casts A) (strip_casts B)
  | tCast c kind t => strip_casts c
  | tLetIn na b t b' => tLetIn na (strip_casts b) (strip_casts t) (strip_casts b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (strip_casts)) brs in
    tCase ind (strip_casts p) (strip_casts c) brs'
  | tProj p c => tProj p (strip_casts c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tCoFix mfix' idx
  | tRel _ | tVar _ | tMeta _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => t
  end.

Definition eq_term_nocast `{checker_flags} (φ : uGraph.t) (t u : term) :=
  eq_term φ (strip_casts t) (strip_casts u).

Definition leq_term_nocast `{checker_flags} (φ : uGraph.t) (t u : term) :=
  leq_term φ (strip_casts t) (strip_casts u).

(** ** Utilities for typing *)

(** Decompose an arity into a context and a sort *)

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst params pars s ty :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), strip_outer_cast ty with
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

Definition build_branches_type ind mdecl idecl params u p :=
  let inds := inds (inductive_mind ind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params mdecl.(ind_params) params ty with
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

Definition types_of_case ind mdecl idecl params u p pty :=
  let brtys := build_branches_type ind mdecl idecl params u p in
  match destArity [] idecl.(ind_type), destArity [] pty, map_option_out brtys with
  | Some (args, s), Some (args', s'), Some brtys =>
    Some (args, args', s', brtys)
  | _, _, _ => None
  end.

(** Family of a universe [u]. *)

Definition universe_family u :=
  match u with
  | [(Level.lProp, false)] => InProp
  | [(Level.lSet, false)] => InSet
  | _ => InType
  end.

(** Check that [uctx] instantiated at [u] is consistent with the current universe graph. *)

Definition consistent_universe_context_instance (Σ : global_context) uctx u :=
  match uctx with
  | Monomorphic_ctx c => True
  | Polymorphic_ctx c =>
    let '(inst, cstrs) := UContext.dest c in
    List.length inst = List.length u /\
    check_constraints (snd Σ) (subst_instance_cstrs u cstrs) = true
  end.

(* Definition allowed_elim u (f : sort_family) := *)
(*   match f with *)
(*   | InProp => Universe.equal Universe.type0m u *)
(*   | InSet => Universe.equal Universe.type0 u *)
(*   | InType => true *)
(*   end. *)

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Prop :=
| cumul_refl t u : leq_term (snd Σ) t u = true -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 (fst Σ) Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (@cumul _ Σ Γ t u) : type_scope.

(** *** Conversion

   Defined as cumulativity in both directions.
 *)

Definition conv `{checker_flags} Σ Γ T U :=
  Σ ;;; Γ |- T <= U /\ Σ ;;; Γ |- U <= T.

Notation " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.

Axiom conv_refl : forall `{checker_flags} Σ Γ t, Σ ;;; Γ |- t = t.
Axiom cumul_refl' : forall `{checker_flags} Σ Γ t, Σ ;;; Γ |- t <= t. (* easy *)
Axiom cumul_trans : forall `{checker_flags} Σ Γ t u v, Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.

Hint Resolve conv_refl cumul_refl' : typecheck.

Conjecture congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
    cumul Σ Γ M1 N1 ->
    cumul Σ (Γ ,, vass na M1) M2 N2 ->
    cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2).

Definition eq_opt_term `{checker_flags} φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term φ t u
  | None, None => true
  | _, _ => false
  end.

Definition eq_decl `{checker_flags} φ (d d' : context_decl) :=
  eq_opt_term φ d.(decl_body) d'.(decl_body) && eq_term φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} φ (Γ Δ : context) :=
  forallb2 (eq_decl φ) Γ Δ.

Definition check_correct_arity `{checker_flags} φ decl ind u ctx pars pctx :=
  let inddecl :=
      {| decl_name := nNamed decl.(ind_name);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|ctx|) pars ++ to_extended_list ctx) |}
  in eq_context φ (inddecl :: ctx) pctx.

Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.

(** ** Typing relation *)

Section TypeLocal.
  Context (typing : forall (Σ : global_context) (Γ : context), term -> term -> Type).

  Inductive All_local_env (Σ : global_context) : context -> Type :=
  | localenv_nil : All_local_env Σ []
  | localenv_cons_abs Γ na t u : All_local_env Σ Γ ->
      typing Σ Γ t (tSort u) -> All_local_env Σ (Γ ,, vass na t)
  | localenv_cons_def Γ na b t : All_local_env Σ Γ ->
      typing Σ Γ b t ->  All_local_env Σ (Γ ,, vdef na b t).
End TypeLocal.

Inductive typing `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    All_local_env typing Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- (tRel n) : lift0 (S n) decl.(decl_type)

| type_Sort l :
    All_local_env typing Σ Γ ->
    Σ ;;; Γ |- (tSort (Universe.make l)) : tSort (Universe.super l)

| type_Cast c k t s :
    Σ ;;; Γ |- t : tSort s ->
    Σ ;;; Γ |- c : t ->
    Σ ;;; Γ |- (tCast c k t) : t

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : tSort s2 ->
    Σ ;;; Γ |- (tProd n t b) : tSort (Universe.sort_of_product s1 s2)

| type_Lambda n n' t b s1 bty :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : bty ->
    Σ ;;; Γ |- (tLambda n t b) : tProd n' t bty

| type_LetIn n b b_ty b' s1 b'_ty :
    Σ ;;; Γ |- b_ty : tSort s1 ->
    Σ ;;; Γ |- b : b_ty ->
    Σ ;;; Γ ,, vdef n b b_ty |- b' : b'_ty ->
    Σ ;;; Γ |- (tLetIn n b b_ty b') : tLetIn n b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ;;; Γ |- t : t_ty ->
    ~ (isApp t = true) -> l <> [] -> (* Well-formed application *)
    typing_spine Σ Γ t_ty l t' ->
    Σ ;;; Γ |- (tApp t l) : t'

| type_Const cst u :
    All_local_env typing Σ Γ ->
    forall decl (isdecl : declared_constant (fst Σ) cst decl),
    consistent_universe_context_instance Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance_constr u decl.(cst_type)

| type_Ind ind u :
    All_local_env typing Σ Γ ->
    forall mdecl idecl (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
    consistent_universe_context_instance Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance_constr u idecl.(ind_type)

| type_Construct ind i u :
    All_local_env typing Σ Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor (fst Σ) mdecl idecl (ind, i) cdecl),
    consistent_universe_context_instance Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case ind u npar p c brs args :
    forall mdecl idecl (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys) ->
    check_correct_arity (snd Σ) idecl ind u indctx pars pctx = true ->
    List.Exists (fun sf => universe_family ps = sf) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    Forall2 (fun x y => (fst x = fst y) * (Σ ;;; Γ |- snd x : snd y)) brs btys ->
    Σ ;;; Γ |- tCase (ind, npar) p c brs : mkApps p (List.skipn npar args ++ [c])

| type_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection (fst Σ) mdecl idecl p pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    (** Actually ensured by typing + validity, but necessary for weakening and substitution. *)
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance_constr u ty)

| type_Fix mfix n decl :
    let types := fix_context mfix in
    nth_error mfix n = Some decl ->
    All_local_env typing Σ (Γ ,,, types) ->
    All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype)) * (isLambda d.(dbody) = true)%type) mfix ->
    (** TODO check well-formed fix *)
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    let types := fix_context mfix in
    nth_error mfix n = Some decl ->
    All_local_env typing Σ (Γ ,,, types) ->
    All (fun d => Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype)) mfix ->
    (** TODO check well-formed cofix *)
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Conv t A B s :
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (@typing _ Σ Γ t T) : type_scope

(* Typing of "spines", currently just the arguments of applications *)

with typing_spine `{checker_flags} (Σ : global_context) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_cons hd tl na A B s T B' :
    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- T <= tProd na A B ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

Notation wf_local Σ Γ := (All_local_env typing Σ Γ).

(** ** Typechecking of global environments *)

Definition add_constraints_env u (Σ : global_context)
  := (fst Σ, add_global_constraints u (snd Σ)).

Definition add_global_decl (decl : global_decl) (Σ : global_context) :=
  let univs := match decl with
               | ConstantDecl _ d => d.(cst_universes)
               | InductiveDecl _ d => d.(ind_universes)
               end
  in (decl :: fst Σ, add_global_constraints univs (snd Σ)).

Definition add_global_declarations (Σ : global_declarations) init : global_context
  := List.fold_left (fun Σ d => add_global_decl d Σ) Σ init.

Definition reconstruct_global_context Σ
 := add_global_declarations Σ ([], init_graph).


Definition isType `{checker_flags} (Σ : global_context) (Γ : context) (t : term) :=
  { s : _ & Σ ;;; Γ |- t : tSort s }.

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Fixpoint context_assumptions (Γ : context) :=
  match Γ with
  | [] => 0
  | d :: Γ =>
    match d.(decl_body) with
    | Some _ => context_assumptions Γ
    | None => S (context_assumptions Γ)
    end
  end.

Definition lift_typing (P : global_context -> context -> term -> term -> Type) :
  (global_context -> context -> option term -> term -> Type) :=
  fun Σ Γ t T =>
    match t with
    | Some b => P Σ Γ b T
    | None => { s : universe & P Σ Γ T (tSort s) }
    end.

Definition unlift_opt_pred (P : global_context -> context -> option term -> term -> Type) :
  (global_context -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

(** *** Typing of inductive declarations *)

Section GlobalMaps.
  Context (P : global_context -> context -> option term -> term -> Type).

  Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

  Definition on_type Σ Γ T := P Σ Γ None T.

  Definition on_arity Σ Γ npars indty : Type :=
    on_type Σ Γ indty * has_nparams npars indty.

  Record constructor_shape mdecl i idecl cdecl :=
    { cshape_arity : context;
      (* Arity (with lets) *)
      cshape_concl_head := tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|cshape_arity|);
      (* Conclusion head: reference to the current inductive in the block *)
      cshape_args : list term;
      (* Arguments of the constructor, whose length should be the real arguments length of the inductive *)
      cshape_eq : snd (fst cdecl) = it_mkProd_or_LetIn mdecl.(ind_params)
                         (it_mkProd_or_LetIn cshape_arity
                         (mkApps cshape_concl_head
                                 (to_extended_list_k mdecl.(ind_params) #|cshape_arity| ++ cshape_args)))
      (* The type of the constructor canonically has this shape: parameters, real arguments ending
         with a reference to the inductive applied to the (non-lets) parameters and arguments *)
    }.

  Definition on_constructor (Σ : global_context) (mind : kername)
             (mdecl : mutual_inductive_body)
             (i : nat) (idecl : one_inductive_body)
             (c : nat) (cdecl : ident * term * nat) : Type :=
    let constructor_type := snd (fst cdecl) in
    on_type Σ (arities_context mdecl.(ind_bodies)) constructor_type *
    constructor_shape mdecl i idecl cdecl.

  Definition on_constructors (Σ : global_context) mind mdecl i idecl l :=
    Alli (on_constructor Σ mind mdecl i idecl) 0 l.

  Definition on_projection (Σ : global_context) mind mdecl (i : nat) (idecl : one_inductive_body)
             (k : nat) (p : ident * term) :=
    let '(ctx, _) := decompose_prod_assum [] idecl.(ind_type) in
    let Γ := ctx,, vass (nNamed idecl.(ind_name))
                (mkApps (tInd (mkInd mind i) (polymorphic_instance mdecl.(ind_universes)))
                        (to_extended_list ctx))
    in
    (on_type Σ Γ (snd p) * (#|ctx| = mdecl.(ind_npars)))%type.

  Definition on_projections (Σ : global_context) mind mdecl i idecl (l : list (ident * term)) : Type :=
    Alli (on_projection Σ mind mdecl i idecl) 0 l.

  Record on_ind_body
         (Σ : global_context) (mind : kername) mdecl (i : nat) idecl :=
    { onArity : (** Arity is well-formed *)
        on_arity Σ [] mdecl.(ind_npars) idecl.(ind_type);
      (** Constructors are well-typed *)
      onConstructors : on_constructors Σ mind mdecl i idecl idecl.(ind_ctors);
      (** Projections are well-typed *)
      onProjections :  on_projections Σ mind mdecl i idecl idecl.(ind_projs)
      (** TODO: check kelim *) }.

  Definition on_context Σ ctx :=
    All_local_env (unlift_opt_pred P) Σ ctx.

  Record on_inductive Σ ind inds :=
    { onInductives : Alli (on_ind_body Σ ind inds) 0 inds.(ind_bodies);
      onParams : on_context Σ inds.(ind_params);
      onNpars : context_assumptions inds.(ind_params) = inds.(ind_npars) }.

  (** *** Typing of constant declarations *)

  Definition on_constant_decl Σ d :=
    match d.(cst_body) with
    | Some trm => P Σ [] (Some trm) d.(cst_type)
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

  Definition contains_init_graph φ :=
    LevelSet.In Level.prop (fst φ) /\ LevelSet.In Level.set (fst φ) /\
    ConstraintSet.In (Level.prop, ConstraintType.Le, Level.set) (snd φ).

  Definition wf_graph φ :=
    contains_init_graph φ /\ (no_universe_inconsistency φ = true).

  (** Well-formed global environments have no name clash. *)

  Definition fresh_global (s : string) : global_declarations -> Prop :=
    Forall (fun g => global_decl_ident g <> s).

  Inductive on_global_decls φ : global_declarations -> Type :=
  | globenv_nil : wf_graph φ -> on_global_decls φ []
  | globenv_decl Σ d :
      on_global_decls φ Σ ->
      fresh_global (global_decl_ident d) Σ ->
      on_global_decl (Σ, φ) d ->
      on_global_decls φ (d :: Σ).

  Definition on_global_env (g : global_context) :=
    on_global_decls (snd g) (fst g).

End GlobalMaps.

Definition sort_irrelevant (P : global_context -> context -> option term -> term -> Type) :=
  forall Σ Γ b s s', P Σ Γ b (tSort s) -> P Σ Γ b (tSort s').

Lemma All_local_env_impl `{checker_flags} (P Q : global_context -> context -> term -> term -> Type) Σ l :
  All_local_env P Σ l ->
  (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
  All_local_env Q Σ l.
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

Lemma on_global_decls_mix {Σ P Q} :
  sort_irrelevant Q ->
  on_global_env P Σ -> on_global_env Q Σ -> on_global_env (fun Σ Γ t T => (P Σ Γ t T * Q Σ Γ t T)%type) Σ.
Proof.
  intros HQ ? ?. destruct Σ as [Σ φ]. red in X, X0 |- *.
  simpl in *. induction X in X0 |- *. inv X0. constructor; auto.
  inv X0. constructor; auto.
  clear IHX.
  destruct d; simpl.
  - destruct c; simpl. destruct cst_body; simpl in *.
    red in o, X2 |- *. simpl in *.
    split; auto.
    red in o, X2 |- *. simpl in *.
    split; auto.
  - destruct o, X2. constructor; intuition.
    2:{ red in onParams0, onParams1 |- *.
        revert onParams0 onParams1.
        clear onNpars0 onNpars1.
        induction (ind_params m). constructor.
        intros H1. inv H1.
        intros H2. inv H2.
        econstructor. eauto. red.
        red in X2, X4; intuition eauto.
        intros H1. inv H1.
        econstructor; eauto. red. intuition eauto. }
    clear onParams0 onParams1 onNpars0 onNpars1.
    merge_Forall. eapply Alli_impl; eauto. clear onInductives1.
    intros.
    destruct x; simpl in *.
    destruct X0 as [Xl Xr].
    constructor; red; simpl. simpl in *.
    + apply onArity in Xl; apply onArity in Xr.
      unfold on_arity, on_type in *. intuition.
    + apply onConstructors in Xl; apply onConstructors in Xr. simpl in *.
      red in Xl, Xr.
      unfold on_constructor, on_type in *.
      merge_Forall. eapply Alli_impl; eauto. simpl; intuition eauto.
    + apply onProjections in Xl; apply onProjections in Xr. simpl in *.
      red in Xl, Xr. merge_Forall. eapply Alli_impl; eauto.
      simpl. intuition eauto.
      red in a, b |- *. simpl in *. destruct (decompose_prod_assum [] ind_type).
      intuition. unfold on_type in *. eauto.
Qed.

Lemma on_global_decls_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env P Σ -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env P Σ -> on_global_env Q Σ.
Proof.
  intros. destruct Σ as [Σ φ]. red in X0 |- *.
  simpl in *. induction X0; constructor; auto.
  clear IHX0. destruct d; simpl.
  - destruct c; simpl. destruct cst_body; simpl in *.
    red in o |- *. simpl in *. auto.
    red in o |- *. simpl in *. red in o. red. auto.
  - red in o. simpl in *.
    destruct o as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl; eauto. intros.
       destruct x; simpl in *.
       constructor; red; simpl.
       --- apply onArity in X1. unfold on_arity, on_type in *; simpl in *; intuition.
       --- apply onConstructors in X1. red in X1. unfold on_constructor, on_type in *. eapply Alli_impl; eauto.
           simpl; intuition eauto.
       --- apply onProjections in X1. simpl in *.
           unfold on_projections in *. eapply Alli_impl; intuition eauto. clear X1.
           unfold on_projection in *; simpl in *.
           destruct decompose_prod_assum. unfold on_type in *; eauto.
           intuition eauto.
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. red in X1. red. apply X. auto. auto.
Qed.

Lemma on_global_decls_proj `{checker_flags} {Σ P Q} :
  on_global_env (fun Σ Γ t T => (P Σ Γ t T * Q Σ Γ t T)%type) Σ -> on_global_env P Σ.
Proof.
  intros. eapply on_global_decls_impl. intros. 2:eauto. simpl in X1; intuition.
Qed.

(** This predicate enforces that there exists typing derivations for every typable term in env. *)

Definition type_global_env `{checker_flags} (Σ : global_context) :=
  on_global_env (lift_typing typing) Σ.

(** *** Typing of local environments *)

Definition type_local_decl `{checker_flags} Σ Γ d :=
  match d.(decl_body) with
  | None => isType Σ Γ d.(decl_type)
  | Some body => Σ ;;; Γ |- body : d.(decl_type)
  end.

(** ** Induction principle for typing up-to a global environment *)

(** With this combinator we get for all typeable terms of the global contexts
    a proof that any typing implies P. *)


Definition all_typing `{checker_flags} (P : global_context -> context -> term -> term -> Type) :
  (global_context -> context -> option term -> term -> Type) :=
  let P' := (fun Σ Γ t T => Σ ;;; Γ |- t : T -> P Σ Γ t T) in
  fun Σ Γ t T =>
    match t with
    | Some b => P Σ Γ b T
    | None => forall s, P Σ Γ T s
    end.

Definition Forall_decls_typing `{checker_flags}
           (P : global_context -> context -> term -> term -> Type) : global_context -> Type :=
  on_global_env (lift_typing P).

Lemma on_type_lift_all `{checker_flags} P Σ Γ T :
  on_type (lift_typing typing) Σ Γ T -> on_type (all_typing P) Σ Γ T ->
  on_type (lift_typing P) Σ Γ T.
Proof. intros. red in X, X0. red. red. destruct X. exists x.  apply X0. Qed.

Inductive Forall_typing_spine `{checker_flags} Σ Γ (P : term -> term -> Type) :
  forall (T : term) (t : list term) (U : term), typing_spine Σ Γ T t U -> Type :=
| Forall_type_spine_nil T : Forall_typing_spine Σ Γ P T [] T (type_spine_nil Σ Γ T)
| Forall_type_spine_cons hd tl na A B s T B' tls
   (typrod : Σ ;;; Γ |- tProd na A B : tSort s)
   (cumul : Σ ;;; Γ |- T <= tProd na A B) (ty : Σ ;;; Γ |- hd : A) :
    P (tProd na A B) (tSort s) -> P hd A -> Forall_typing_spine Σ Γ P (B {0 := hd}) tl B' tls ->
    Forall_typing_spine Σ Γ P T (hd :: tl) B'
      (type_spine_cons Σ Γ hd tl na A B s T B' typrod cumul ty tls).

Section wf_local_size.
  Context `{checker_flags} (Σ : global_context).
  Context (fn : forall (Σ : global_context) (Γ : context) (t T : term), typing Σ Γ t T -> size).

  Fixpoint wf_local_size Γ (w : wf_local Σ Γ) : size :=
  match w with
  | localenv_nil => 0
  | localenv_cons_abs Γ na t u wfΓ tty => fn _ _ t (tSort u) tty + wf_local_size _ wfΓ
  | localenv_cons_def Γ na b t wfΓ tty => fn _ _ b t tty + wf_local_size _ wfΓ
  end.
End wf_local_size.

Section Typing_Spine_size.
  Context `{checker_flags}.
  Context (fn : forall (Σ : global_context) (Γ : context) (t T : term), typing Σ Γ t T -> size).
  Context (Σ : global_context) (Γ : context).

  Fixpoint typing_spine_size t T U (s : typing_spine Σ Γ t T U) : size :=
  match s with
  | type_spine_nil _ => 0
  | type_spine_cons hd tl na A B s T B' typrod cumul ty s' => fn _ _ _ _ ty + fn _ _ _ _ typrod +
                                                            typing_spine_size _ _ _ s'
  end.
End Typing_Spine_size.


Definition typing_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix typing_size 5.
  destruct 1 ;
  repeat match goal with
         | H : typing _ _ _ _ |- _ => apply typing_size in H
         end ;
  match goal with
  | H : Forall2 _ _ _ |- _ => idtac
  | H : All_local_env _ _ _ |- _ => idtac
  | H : All _ _ |- _ => idtac
  | H : typing_spine _ _ _ _ _ |- _ => idtac
  | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
  | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
  | H1 : size |- _  => exact (S H1)
  | _ => exact 1
  end.
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (Nat.max d (typing_spine_size typing_size _ _ _ _ _ t0))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (Nat.max d1 (Nat.max d2
                                (all2_size _ (fun x y p => typing_size Σ Γ (snd x) (snd y) (snd p)) f)))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ (fst p)) a0))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ p) a0))).
Defined.

Require Import Lia.

Lemma typing_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; simpl; lia.
Qed.

Fixpoint globenv_size (Σ : global_declarations) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_context, including size of the global declarations in it
    - size of the derivation. *)

Require Import Wf.

(** Define non-dependent lexicographic products *)

Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Arguments lexprod [A B].

Notation wf := type_global_env.

Conjecture wf_graph_prop_set : forall φ (H : wf_graph φ),
    check_lt φ Universe.type0m Universe.type1 = true /\
    check_lt φ Universe.type0 Universe.type1 = true.

Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) :=
  forall Σ (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T ->
    Forall_decls_typing P Σ * P Σ Γ t T.

Lemma env_prop_typing `{checker_flags} P : env_prop P ->
  forall Σ (wf : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma env_prop_sigma `{checker_flags} P : env_prop P ->
  forall Σ (wf : wf Σ), Forall_decls_typing P Σ.
Proof.
  intros. eapply X. apply wf. constructor. apply (type_Sort Σ [] Level.prop). constructor.
Defined.

Lemma wf_local_app `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
Proof.
  induction Γ'. auto.
  simpl. intros H'; inv H'; eauto.
Defined.
Hint Resolve wf_local_app : wf.

Lemma typing_wf_local `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_local Σ Γ.
Proof.
  induction 1; eauto using wf_local_app.
Defined.
Hint Resolve typing_wf_local : wf.

Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (wf : wf_local Σ (Γ ,,, Γ')) :
  wf_local_size Σ (@typing_size _) _ (wf_local_app _ _ _ wf) <=
  wf_local_size Σ (@typing_size _) _ wf.
Proof.
  induction Γ' in Γ, wf |- *; try lia. simpl. lia.
  depelim wf. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ wf). lia.
  specialize (IHΓ' _ wf). simpl. unfold eq_rect_r. simpl. lia.
Qed.

Lemma typing_wf_local_size `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  wf_local_size Σ (@typing_size _) _ (typing_wf_local wfΣ d) < typing_size d.
Proof.
  induction d; simpl; try lia.
  pose proof (size_wf_local_app _ _ a).
  eapply Nat.le_lt_trans. eauto. subst types. lia.
  pose proof (size_wf_local_app _ _ a).
  eapply Nat.le_lt_trans. eauto. subst types. lia.
Qed.

Lemma wf_local_inv `{checker_flags} Σ d Γ (w : wf_local Σ (d :: Γ)) :
  { w' : wf_local Σ Γ &
    match d.(decl_body) with
    | Some b => { ty : Σ ;;; Γ |- b : d.(decl_type) |
                  wf_local_size Σ (@typing_size _) _ w' < wf_local_size _ (@typing_size _) _ w /\
                  typing_size ty <= wf_local_size _ (@typing_size _) _ w }
    | None => { u & { ty : Σ ;;; Γ |- d.(decl_type) : tSort u |
                      wf_local_size Σ (@typing_size _) _ w' < wf_local_size _ (@typing_size _) _ w /\
                      typing_size ty <= wf_local_size _ (@typing_size _) _ w } }
    end }.
Proof.
  remember (d :: Γ) as ctx. revert Heqctx. destruct w. simpl.
  congruence.
  intros [=]. subst d Γ0.
  exists w; simpl. exists u. exists t0. pose (typing_size_pos t0). lia.
  intros [=]. subst d Γ0.
  exists w; simpl. exists t0. pose (typing_size_pos t0). lia.
Qed.

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_context -> context -> term -> term -> Type),
    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        All_local_env typing Σ Γ -> All_local_env P Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        All_local_env typing Σ Γ -> All_local_env P Σ Γ ->
        P Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (c : term) (k : cast_kind)
            (t : term) (s : universe),
        Σ ;;; Γ |- t : tSort s -> P Σ Γ t (tSort s) -> Σ ;;; Γ |- c : t -> P Σ Γ c t -> P Σ Γ (tCast c k t) t) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : universe),
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n n' : name) (t b : term)
            (s1 : universe) (bty : term),
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n' t bty)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b b_ty b' : term)
            (s1 : universe) (b'_ty : term),
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) (l : list term) (t_ty t' : term),
        Σ ;;; Γ |- t : t_ty -> P Σ Γ t t_ty ->
        ~ (isApp t = true) -> l <> [] ->
        forall (s : typing_spine Σ Γ t_ty l t'),
        Forall_typing_spine Σ Γ (fun t T => P Σ Γ t T) t_ty l t' s ->
        P Σ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : ident) u (decl : constant_body),
        declared_constant (fst Σ) cst decl ->
        Forall_decls_typing P Σ ->
        All_local_env typing Σ Γ -> All_local_env P Σ Γ ->
        consistent_universe_context_instance Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing P Σ ->
        All_local_env typing Σ Γ -> All_local_env P Σ Γ ->
        consistent_universe_context_instance Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor (fst Σ) mdecl idecl (ind, i) cdecl),
        Forall_decls_typing P Σ ->
        All_local_env typing Σ Γ -> All_local_env P Σ Γ ->
        consistent_universe_context_instance Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing P Σ ->
        ind_npars mdecl = npar ->
        let pars := firstn npar args in
        forall (pty : term), Σ ;;; Γ |- p : pty -> P Σ Γ p pty ->
        forall indctx pctx ps btys,
        types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys) ->
        check_correct_arity (snd Σ) idecl ind u indctx pars pctx = true ->
        Exists (fun sf : sort_family => universe_family ps = sf) (ind_kelim idecl) ->
        P Σ Γ p pty ->
        Σ;;; Γ |- c : mkApps (tInd ind u) args ->
        P Σ Γ c (mkApps (tInd ind u) args) ->
        Forall2 (fun x y : nat * term => (fst x = fst y) * (Σ;;; Γ |- snd x : snd y)
                                         * P Σ Γ (snd x) (snd y))%type brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl (isdecl : declared_projection (fst Σ) mdecl idecl p pdecl) args,
        Forall_decls_typing P Σ ->
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        All_local_env (fun Σ Γ b ty => (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
                   (isLambda d.(dbody) = true)%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        All_local_env (fun Σ Γ b ty => (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->

        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) (s : universe),
        Σ ;;; Γ |- t : A ->
                       P Σ Γ t A -> Σ ;;; Γ |- B : tSort s -> P Σ Γ B (tSort s) -> Σ ;;; Γ |- A <= B -> P Σ Γ t B) ->

       env_prop P.
Proof.
  unfold env_prop.
  intros P X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ wfΓ t T H.
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ & { Γ : context & { wfΓ : wf_local Σ Γ &
               { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}})
               (lexprod (MR lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => MR lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 (projT2 x))))))))).
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ wfΓ (existT _ t (existT _ _ H))))) : { Σ : _ & { wfΣ : wf Σ & { Γ : context & { wfΓ & { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}}).
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
  constructor; auto. unfold Forall_decls_typing in IH.
  - specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ [] (existT _ (localenv_nil typing (Σ, φ)) (existT _ (tSort Universe.type0m ) (existT _ _ (type_Sort _ _ Level.prop (localenv_nil typing (Σ, φ)))))))))).
    simpl in IH. forward IH. constructor 1. simpl. omega.
    apply IH; auto.
  - simpl. simpl in *.
    (* specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ [] (existT _ (localenv_nil typing (Σ, φ)) (existT _ (tSort Universe.type0m ) (existT _ _ (type_Sort _ _ Level.prop (localenv_nil typing (Σ, φ)))))))))). *)
    (* simpl in IH. forward IH. constructor 1. simpl. omega. *)
    (* unfold Forall_decls_typing in IH. destruct IH. clear p. *)
    (* auto. *)
    destruct g; simpl.
    + destruct c; simpl in *.
      destruct cst_body; simpl in *.
      simpl.
      intros. red in X15. simpl in X15.
      specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ (localenv_nil typing _) (existT _ _ (existT _ _ X15))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; omega.
      apply IH.
      red. simpl. red in X15; simpl in X15.
      destruct X15 as [s Hs]. red. simpl. exists s.
      specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ (localenv_nil typing _) (existT _ _ (existT _ _ Hs))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; omega.
      apply IH.
    + red in X15.
      destruct X15 as [onI onP onnp]; constructor; eauto.
      eapply Alli_impl; eauto. clear onI onP onnp; intros.
      constructor.
      ++ apply onArity in X15. destruct X15 as [[s Hs] Hpars]. split; auto. exists s.
         specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ (localenv_nil typing _) (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. apply IH; constructor 1; simpl; omega.
      ++ apply onConstructors in X15.
         red in X15 |- *. eapply Alli_impl; eauto. intros.
         red in X16 |- *. destruct X16 as [[s Hs] Hpars]. split; auto. exists s.
         pose proof (typing_wf_local (Σ:= (Σ, φ)) X14 Hs).
         specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ X16 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. apply IH; constructor 1; simpl; omega.
      ++ apply onProjections in X15. simpl in *.
         red in X15 |- *. eapply Alli_impl; eauto. clear X15. intros.
         red in X15 |- *. destruct (decompose_prod_assum [] (ind_type x)).
         destruct X15 as [[s Hs] Hpars]. split; auto. exists s.
         pose proof (typing_wf_local (Σ:= (Σ, φ)) X14 Hs).
         specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ X15 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. apply IH; constructor 1; simpl; omega.
      ++ red in onP |- *.
         eapply All_local_env_impl; eauto.
         intros. do 2 red in X15 |- *.
         specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ,φ)) X14 X15)
                                                                           (existT _ _ (existT _ _ X15))))))).
         simpl in IH. apply IH. constructor 1. simpl. lia.

  - assert (forall Γ (wfΓ : wf_local Σ Γ) t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               Forall_decls_typing P Σ * P Σ Γ t T).
    intros.
    specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ wfΓ0 (existT _ _ (existT _ _ Hty))))))).
    simpl in IH.
    forward IH.
    constructor 2. simpl. apply H0.
    apply IH. clear IH.

    assert (All_local_env P Σ Γ).
    { clear -wfΓ wfΣ X14.
      pose proof (typing_wf_local_size wfΣ H). clear wfΓ.
      induction Γ in t, t0, H, H0, X14 |- *. constructor.
      destruct a. destruct decl_body.
      --- destruct (wf_local_inv _ _ _ (typing_wf_local wfΣ H)).
          simpl in y. destruct y as [Hty [sizex sizety]].
          constructor.
          eapply IHΓ with _ _ Hty. eauto. intros. eapply X14 with Hty0; eauto. lia.
          apply typing_wf_local_size.
          unshelve eapply X14; simpl; auto with arith;
            repeat (rewrite Nat.max_comm -Nat.max_assoc; auto with arith); lia.
      --- destruct (wf_local_inv _ _ _ (typing_wf_local wfΣ H)).
          simpl in y. destruct y as [s [Hs [sizex sizety]]].
          econstructor; eauto.
          eapply IHΓ with _ _ Hs. intros. eapply X14 with Hty; eauto. lia.
          apply typing_wf_local_size.
          unshelve eapply X14; simpl; eauto with arith;
            repeat (rewrite Nat.max_comm -Nat.max_assoc; auto with arith). }

    destruct H;
      try solve [  match reverse goal with
                     H : _ |- _ => eapply H
                   end; eauto;
                   unshelve eapply X14; simpl; auto with arith].

    -- match reverse goal with
         H : _ |- _ => eapply H
       end; eauto;
         unshelve eapply X14; simpl; auto with arith.
       econstructor; eauto.

    -- match reverse goal with
         H : _ |- _ => eapply H
       end; eauto;
         unshelve eapply X14; simpl; auto with arith.
       econstructor; eauto.

    -- match reverse goal with
         H : _ |- _ => eapply H
       end; eauto;
         unshelve eapply X14; simpl; auto with arith. lia.
       econstructor; eauto. lia.

    -- clear X X0 X1 X2 X3 X4 X6 X7 X8 X9 X10 X11 X12 X13.
       eapply X5 with t_ty t0; eauto.
       unshelve eapply X14; simpl; auto with arith.
       simpl in X14.
       assert( forall Γ0 : context,
                 wf_local Σ Γ0 ->
              forall (t1 T : term) (Hty : Σ;;; Γ0 |- t1 : T),
                typing_size Hty <
                S
                  ((typing_spine_size
                      (fun (x : global_context) (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                         typing_size x3) Σ Γ t_ty l t' t0)) ->
                Forall_decls_typing P Σ * P Σ Γ0 t1 T).
       intros. unshelve eapply X14; eauto. lia. clear X14. clear n n0 H.
       induction t0; constructor.
       unshelve eapply X; clear X; simpl; auto with arith.
       unshelve eapply X; clear X; simpl; auto with arith.
       eapply IHt0; eauto. intros. eapply (X _ X0 _ _ Hty) ; eauto. simpl. lia.

    -- apply X6; eauto. simpl in X14.
       specialize (X14 [] (localenv_nil _ _) _ _ (type_Sort _ _ Level.prop (localenv_nil _ _))).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X7; eauto.
       specialize (X14 [] (localenv_nil _ _) _ _ (type_Sort _ _ Level.prop (localenv_nil _ _))).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X8; eauto.
       specialize (X14 [] (localenv_nil _ _) _ _ (type_Sort _ _ Level.prop (localenv_nil _ _))).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X9; eauto.
       eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith.
       eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith. simpl in *.
       eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith. simpl in *.
       eapply (X14 _ wfΓ _ _ H0); eauto. simpl; auto with arith. simpl in *.
       induction f; simpl; lia.
       simpl in *.
       revert f wfΓ X14. clear. intros.
       induction f; simpl in *. constructor.
       destruct r. constructor. split; auto.
       eapply (X14 _ wfΓ _ _ t); eauto. simpl; auto with arith.
       lia.
       apply IHf. auto. intros.
       eapply (X14 _ wfΓ0 _ _ Hty). lia.

    -- eapply X10; eauto.
       specialize (X14 [] (localenv_nil _ _) _ _ (type_Sort _ _ Level.prop (localenv_nil _ _))).
       simpl in X14. forward X14; auto. pose (typing_size_pos H). lia. apply X14.
       unshelve eapply X14; eauto.

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
                                      (fun (x : global_context) (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                                         typing_size x3) Γ' a)) ->
                   Forall_decls_typing P Σ * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 a0.
       clear HeqΓ'. clear X15. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); eauto. lia.
       --- split; eauto.
           eapply (X _ a _ _ t0); eauto. lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- split; auto. eapply (X _ a _ _ t0); eauto. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                wf_local Σ Γ0 ->
               forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                typing_size Hty <
                      S
                        (all_size (fun x : def term => (Σ;;; Γ ,,, fix_context mfix |- dbody x : lift0 #|types| (dtype x))%type
                                                        * (isLambda (dbody x) = true)%type)%type
                                   (fun (x : def term) p => typing_size (fst p)) a0) ->
                       Forall_decls_typing P Σ * P Σ Γ0 t T).
           subst types. intros. eapply (X14 _ X _ _ Hty); eauto. lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ (fst p)). simpl. lia.
       ++ eapply IHa0. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X13.
       eapply X12; eauto; clear X12. simpl in *. subst types.
       remember (Γ ,,, fix_context mfix) as Γ'.
       assert( forall Γ : context,
                 wf_local Σ Γ ->
                 forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S
                     (
                       (wf_local_size Σ
                                      (fun (x : global_context) (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                                         typing_size x3) Γ' a)) ->

                   Forall_decls_typing P Σ * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 X15 a0.
       clear HeqΓ'. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); eauto. lia.
       --- split; eauto.
           eapply (X _ a _ _ t0); eauto. lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- split; auto. eapply (X _ a _ _ t0); eauto. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                     wf_local Σ Γ0 ->
                     forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                       typing_size Hty <
                       S (all_size (fun x : def term => Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x)))
                                   (fun (x : def term) (p : Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x))) => typing_size p) a0) ->
                       Forall_decls_typing P Σ * P Σ Γ0 t T).
           intros. eapply (X14 _ X _ _ Hty); eauto. subst types; lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ p). simpl. lia.
       ++ eapply IHa0. intros.
         eapply (X _ X0 _ _ Hty). simpl; lia.
Qed.

(** Example: only well-formed terms are well-typed *)

Lemma wf_mkApps_napp t u : isApp t = false -> Ast.wf (mkApps t u) -> Ast.wf t /\ List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros Happ H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial. discriminate.
Qed.
Hint Resolve wf_mkApps_napp : wf.

Lemma wf_mkApps_inv t u : Ast.wf (mkApps t u) -> List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial.
    simpl. rewrite <- app_assoc. simpl. apply H.
    intuition. inv H.
    apply Forall_app in H3. intuition.
Qed.
Hint Resolve wf_mkApps_inv : wf.
Hint Constructors Ast.wf : wf.

Lemma isLambda_subst s t : isLambda t = true -> isLambda (subst0 s t) = true.
Proof.
  destruct t; simpl; try congruence.
Qed.

Lemma isLambda_isApp t : isLambda t = true -> isApp t = false.
Proof. destruct t; simpl; congruence. Qed.

Lemma unfold_fix_wf:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_fix mfix idx = Some (narg, fn) ->
    Ast.wf (tFix mfix idx) ->
    Ast.wf fn /\ isApp fn <> true.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_fix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_forall eqnth H). simpl in H0.
  injection Hf. intros <- <-.
  destruct H0 as [ _ [ wfd islamd ] ]. apply (isLambda_subst (fix_subst mfix)) in islamd.
  apply isLambda_isApp in islamd. split; try congruence.
  apply wf_subst; auto. clear wfd islamd Hf eqnth.
  assert(forall n, Ast.wf (tFix mfix n)). constructor; auto.
  unfold fix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma unfold_cofix_wf:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_cofix mfix idx = Some (narg, fn) ->
    Ast.wf (tCoFix mfix idx) -> Ast.wf fn.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_cofix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_forall eqnth H). simpl in H0.
  injection Hf. intros <- <-.
  destruct H0 as [ _ wfd ].
  apply wf_subst; auto. clear wfd Hf eqnth.
  assert(forall n, Ast.wf (tCoFix mfix n)). constructor; auto.
  unfold cofix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma wf_subst_instance_constr u c :
  Ast.wf c -> Ast.wf (subst_instance_constr u c).
Proof.
  induction 1 using term_wf_forall_list_ind; simpl; try solve [ constructor; auto using Forall_map ].

  constructor; auto. destruct t; simpl in *; try congruence. destruct l; simpl in *; congruence.
  now apply Forall_map.
  constructor; auto. merge_Forall. apply Forall_map.
  eapply Forall_impl; eauto. intros. simpl in *. red. intuition auto.
  destruct x; simpl in *.
  destruct dbody; simpl in *; congruence.
Qed.

Lemma lookup_on_global_env P Σ c decl :
  on_global_env P Σ ->
  lookup_env (fst Σ) c = Some decl ->
  { Σ' & { wfΣ' : on_global_env P Σ' & on_global_decl P Σ' decl } }.
Proof.
  induction 1; simpl. congruence.
  destruct ident_eq. intros [= ->].
  exists (Σ0, snd Σ). exists X. auto.
  apply IHX.
Qed.

Lemma wf_nth:
  forall (n : nat) (args : list term), Forall Ast.wf args -> Ast.wf (nth n args tDummy).
Proof.
  intros n args H. induction H in n; destruct n; simpl; try constructor; auto.
Qed.
Hint Resolve wf_nth.

Lemma wf_red1 `{CF:checker_flags} Σ Γ M N :
  on_global_env (fun Σ Γ t T => match t with Some b => Ast.wf b /\ Ast.wf T | None => Ast.wf T end) Σ ->
  List.Forall (fun d => match decl_body d with Some b => Ast.wf b | None => True end) Γ ->
  Ast.wf M -> red1 (fst Σ) Γ M N -> Ast.wf N.
Proof.
  intros wfΣ wfΓ wfM H.
  induction H using red1_ind_all in wfM, wfΓ |- *; inv wfM; try solve[ constructor; auto with wf ].

  - inv H1. inv H2.
    eauto with wf.
  - auto with wf.
  - apply wf_lift.
    unfold option_map in H. destruct nth_error eqn:Heq; try discriminate.
    eapply nth_error_forall in wfΓ; eauto. simpl in *. destruct (decl_body c); congruence.
  - unfold iota_red.
    apply wf_mkApps_inv in H0.
    apply wf_mkApps; auto.
    induction brs in c, H1 |- *; destruct c; simpl in *. constructor. constructor.
    inv H1; auto. inv H1; auto.
    induction H0 in pars |- *; destruct pars; try constructor; auto. simpl. auto.
  - apply unfold_fix_wf in H; auto. constructor; intuition auto.
  - constructor; auto. apply wf_mkApps_napp in H1 as [Hcof Hargs]; auto.
    apply unfold_cofix_wf in H; auto.
    apply wf_mkApps; intuition auto.
  - constructor; auto. apply wf_mkApps_napp in H0 as [Hcof Hargs]; auto.
    apply unfold_cofix_wf in H; auto.
    apply wf_mkApps; intuition auto.
  - apply wf_subst_instance_constr.
    unfold declared_constant in H.
    eapply lookup_on_global_env in H as [Σ' [onΣ' prf]]; eauto.
    destruct decl; simpl in *.
    subst cst_body; intuition. red in prf. simpl in prf. easy.
  - apply wf_mkApps_inv in H0.
    eapply nth_error_forall in H0; eauto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. induction H; constructor; inv H2; intuition auto.
  - apply wf_mkApps; auto.
  - constructor; auto. induction H; congruence.
    clear H1. induction H; inv H3; constructor; intuition auto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. induction H; inv H0; constructor; intuition auto.
  - auto.
Qed.

Lemma All_local_env_app `{checker_flags} (P : global_context -> context -> term -> term -> Type) Σ l l' :
  All_local_env P Σ (l ,,, l') -> All_local_env P Σ l * All_local_env (fun Σ Γ t T => P Σ (l ,,, Γ) t T) Σ l'.
Proof.
  induction l'; simpl; split; auto. constructor. intros. unfold app_context in X.
  inv X. intuition auto. auto. apply IHl'. auto.
  inv X. eapply localenv_cons_abs. apply IHl'. apply X0. apply X1.
  eapply localenv_cons_def. apply IHl'. apply X0. apply X1.
Qed.

Definition wf_decl d := match decl_body d with Some b => Ast.wf b | None => True end /\ Ast.wf (decl_type d).

Ltac wf := intuition try (eauto with wf || congruence || solve [constructor]).
Hint Unfold wf_decl vass vdef : wf.
Hint Extern 10 => progress simpl : wf.
Hint Unfold snoc : wf.
Hint Extern 3 => apply wf_lift || apply wf_subst || apply wf_subst_instance_constr : wf.
Hint Extern 10 => constructor : wf.
Hint Resolve Forall_skipn : wf.

Lemma wf_inds mind bodies u : Forall Ast.wf (inds mind u bodies).
Proof.
  unfold inds. generalize #|bodies|. induction n. constructor.
  constructor; auto. wf.
Qed.

Hint Resolve wf_inds : wf.

Ltac specialize_goal :=
  repeat match goal with
  | H : ?P -> _, H' : ?P |- _ => specialize (H H')
  end.

Definition on_local_decl (P : global_context -> context -> term -> term -> Type) Σ Γ d :=
  match d.(decl_body) with
  | Some b => P Σ Γ b d.(decl_type)
  | None => { u & P Σ Γ d.(decl_type) (tSort u) }
  end.

Lemma All_local_env_lookup `{checker_flags} {P Σ Γ n} {decl} :
  All_local_env P Σ Γ ->
  nth_error Γ n = Some decl ->
  on_local_decl P Σ (skipn (S n) Γ) decl.
Proof.
  induction 1 in n, decl |- *. simpl. destruct n; simpl; congruence.
  destruct n. red. simpl. intros [= <-]; now exists u.
  simpl in *. eapply IHX.
  destruct n. simpl. intros [= <-]. auto.
  eapply IHX.
Qed.

Lemma All_local_env_app_inv `{checker_flags} (P : global_context -> context -> term -> term -> Type) Σ l l' :
  All_local_env P Σ l * All_local_env (fun Σ Γ t T => P Σ (l ,,, Γ) t T) Σ l' ->
  All_local_env P Σ (l ,,, l').
Proof.
  induction l'; simpl; auto. intuition.
  intuition. destruct a. destruct decl_body.
  inv b. econstructor; eauto. inv b; econstructor; eauto. Qed.

Lemma map_vass_map_def g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (lift n k) g) l)) =
  (mapi (fun i d => map_decl (lift n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite permute_lift. lia. f_equal; lia.
Qed.

Lemma All_local_env_map `{checker_flags} (P : global_context -> context -> term -> term -> Type) Σ f l :
  (forall u, f (tSort u) = tSort u) ->
  All_local_env (fun Σ Γ t T => P Σ (map (map_decl f) Γ) (f t) (f T)) Σ l -> All_local_env P Σ (map (map_decl f) l).
Proof.
  intros Hf. induction 1; econstructor; eauto.
  simpl. rewrite Hf in t0. eapply t0.
Qed.

Lemma wf_lift_wf n k t : Ast.wf (lift n k t) -> Ast.wf t.
Proof.
  induction t in n, k |- * using term_forall_list_ind; simpl in *;
    intros Hwf; inv Hwf; try constructor; eauto.

  - apply Forall_map_inv in H0. merge_Forall. eapply Forall_impl; eauto.
    simpl ; intros. intuition eauto.
  - destruct t; try discriminate. simpl in *. congruence.
  - destruct l; simpl in *; congruence.
  - apply Forall_map_inv in H3. merge_Forall. eapply Forall_impl; eauto.
    simpl ; intros. intuition eauto.
  - apply Forall_map_inv in H2. merge_Forall. eapply Forall_impl; eauto.
    simpl ; intros. intuition eauto. unfold compose in *.
    destruct x; simpl in *; eauto.
  - apply Forall_map_inv in H0. merge_Forall. eapply Forall_impl; eauto.
    simpl ; intros. unfold compose in *; destruct x; simpl in *; intuition eauto.
    destruct dbody; try discriminate. simpl in H5. destruct Nat.leb; auto.
    reflexivity.
  - apply Forall_map_inv in H0. merge_Forall. eapply Forall_impl; eauto.
    simpl ; intros. unfold compose in *; destruct x; simpl in *; intuition eauto.
Qed.

Lemma typing_wf_gen `{checker_flags} : env_prop (fun Σ Γ t T => Ast.wf t /\ Ast.wf T).
Proof.
  apply typing_ind_env; intros; auto with wf;
    specialize_goal;
    try solve [split; try constructor; intuition auto with wf].

  - split; wf. apply wf_lift.
    apply (All_local_env_lookup H1) in H0.
    red in H0. destruct decl as [na [body|] ty]; simpl in *; intuition auto.
    destruct H0; intuition auto.
  - split. constructor; auto. wf.
    clear H1 H2 X.
    induction X0. wf. constructor. wf.
    apply IHX0. split. wf. apply wf_subst. wf. wf. now inv H0.
    clear H1 H2 X.
    induction X0. wf. apply IHX0. constructor. wf.
    apply wf_subst. wf. wf. now inv H0.
  - split. wf. apply wf_subst_instance_constr. wf.
    red in H0.
    eapply lookup_on_global_env in H0 as [Σ' [wfΣ' prf]]; eauto.
    red in prf. destruct decl; destruct cst_body; red in prf; simpl in *; wf.
    destruct prf. apply a.

  - split. wf. apply wf_subst_instance_constr. wf.
    destruct isdecl as [Hmdecl Hidecl]. red in Hmdecl.
    eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto.
    eapply onArity in Hidecl.
    destruct Hidecl as [[s Hs] Hpars]; wf.
  - split. wf.
    destruct isdecl as [[Hmdecl Hidecl] Hcdecl]. red in Hmdecl.
    eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto. red in prf.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto. simpl in *. intuition.
    apply onConstructors in Hidecl.
    eapply nth_error_alli in Hcdecl; eauto.
    destruct Hcdecl as [[s Hs] Hpars]. unfold type_of_constructor. wf.
  - split. wf. constructor; eauto.
    eapply Forall2_Forall_left; eauto. simpl. intuition auto.
    apply wf_mkApps. wf. apply Forall_app_inv. split. 2:wf.
    inv H6. apply wf_mkApps_inv in H8. now apply Forall_skipn.
  - split. wf. apply wf_subst. constructor. wf. intuition.
    apply wf_mkApps_inv in H3. now apply Forall_rev.
    subst ty. destruct isdecl as [[Hmdecl Hidecl] Hpdecl].
    eapply lookup_on_global_env in Hmdecl as [Σ' [wfΣ' prf]]; eauto. red in prf.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto. intuition.
    eapply onProjections in Hidecl.
    eapply nth_error_alli in Hidecl; eauto. red in Hidecl.
    destruct decompose_prod_assum.
    destruct Hidecl as [[s Hs] Hnpars]. apply wf_subst_instance_constr. apply Hs.
  - subst types.
    apply All_local_env_app in X as [HΓ Hmfix].
    clear Hmfix.
    split.
    + revert X0. generalize (fix_context mfix). intros.
      clear decl H0. constructor. induction mfix. constructor. constructor.
      2:{ apply IHmfix. inv X0. auto. }
      inv X0. intuition. now apply wf_lift_wf in H1.
    + eapply nth_error_all in X0; eauto. simpl in X0. intuition eauto.
      now apply wf_lift_wf in H2.
  - subst types.
    apply All_local_env_app in X as [HΓ Hmfix].
    clear Hmfix.
    split.
    + revert X0. generalize (fix_context mfix). intros.
      clear decl H0. constructor. induction mfix. constructor. constructor.
      2:{ apply IHmfix. inv X0. auto. }
      inv X0. intuition. now apply wf_lift_wf in H1.
    + eapply nth_error_all in X0; eauto. simpl in X0; intuition eauto.
      now apply wf_lift_wf in H2.
Qed.

Lemma typing_all_wf_decl `{checker_flags} Σ (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) :
  Forall wf_decl Γ.
Proof.
  induction wfΓ. constructor. constructor; auto. red. simpl. split; wf.
  apply typing_wf_gen in t0; eauto. apply t0; auto.
  constructor; auto. red; simpl. apply typing_wf_gen in t0; auto. intuition auto.
Qed.
Hint Resolve typing_all_wf_decl : wf.

Lemma typing_wf_sigma `{checker_flags} Σ (wfΣ : wf Σ) :
  on_global_env (fun Σ Γ t T => match t with Some b => Ast.wf b /\ Ast.wf T | None => Ast.wf T end) Σ.
Proof.
  intros.
  pose proof (env_prop_sigma _ typing_wf_gen _ wfΣ). red in X.
  red in X. unfold lift_typing in X. red. do 2 red in wfΣ.
  unshelve eapply (on_global_decls_mix _ wfΣ) in X.
  red. intros. destruct b; intuition auto with wf.
  destruct X0 as [u Hu]. exists u. intuition auto with wf.
  clear wfΣ.
  eapply on_global_decls_impl; eauto; simpl; intros. clear X.
  destruct X1 as [Hty Ht].
  pose proof (on_global_decls_proj X0).
  destruct t. apply Ht. destruct Ht; wf.
Qed.

Lemma typing_wf `{checker_flags} Σ (wfΣ : wf Σ) Γ t T :
  Σ ;;; Γ |- t : T -> Ast.wf t /\ Ast.wf T.
Proof.
  intros. eapply typing_wf_gen in X; intuition eauto with wf.
Qed.
