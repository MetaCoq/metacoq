(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast univ Induction LiftSubst UnivSubst.
From Template Require AstUtils Loader.
Require Import String.
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

Definition is_constant_decl d :=
  match d with
  | InductiveDecl _ _ => false
  | _ => true
  end.

Definition is_minductive_decl d :=
  match d with
  | InductiveDecl _ _ => true
  | _ => false
  end.

Definition is_inductive_decl_for i d :=
  match d with
  | InductiveDecl _ cb => i < List.length cb.(ind_bodies)
  | _ => False
  end.

Definition ident_eq (x y : ident) :=
  if string_dec x y then true else false.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct string_dec; constructor; auto.
Qed.

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

Definition declared_inductive Σ ind univs decl :=
  exists decl', declared_minductive Σ (inductive_mind ind) decl' /\
                univs = decl'.(ind_universes) /\
                List.nth_error decl'.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr univs decl : Prop :=
  let '(ind, k) := cstr in
  exists decl', declared_inductive Σ ind univs decl' /\
                List.nth_error decl'.(ind_ctors) k = Some decl.

Definition declared_projection Σ (proj : projection) decl : Prop :=
  let '(ind, ppars, arg) := proj in
  exists univs decl', declared_inductive Σ ind univs decl' /\
                List.nth_error decl'.(ind_projs) arg = Some decl.

Program
Definition type_of_constant_decl (d : global_decl | is_constant_decl d = true) : term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_type)
  end.

Program
Definition body_of_constant_decl (d : global_decl | is_constant_decl d = true) : option term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_body)
  end.

Program
Definition types_of_minductive_decl (d : global_decl | is_minductive_decl d = true) :
  list one_inductive_body :=
  match d with
  | InductiveDecl _ tys => tys.(ind_bodies)
  | ConstantDecl _ _ => !
  end.

Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Program
Definition type_of_constructor (Σ : global_declarations) (c : inductive * nat) (univs : universe_context) (u : list Level.t) (decl : ident * term * nat)
           (H : declared_constructor Σ c univs decl) :=
  let mind := inductive_mind (fst c) in
  let '(id, trm, args) := decl in
  match lookup_env Σ mind with
  | Some (InductiveDecl _ decl') =>
    substl (inds mind u decl'.(ind_bodies)) (subst_instance_constr u trm)
  | _ => !
  end.

Next Obligation.
  destruct H as [decl [H H']].
  destruct H as [decl' [H'' H''']].
  eapply H0.
  simpl. rewrite H''. reflexivity.
Defined.

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
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
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

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tRel 0))) (List.skipn npar args)).

(** *** One step beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
  TODO: Projections and CoFixpoints
*)

Inductive red1 (Σ : global_declarations) (Γ : context) : term -> term -> Prop :=
(** Reductions *)
(** Beta *)
| red_beta na t b a l :
    red1 Σ Γ (tApp (tLambda na t b) (a :: l)) (mkApps (subst0 a b) l)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst0 b b')

| red_rel i (isdecl : i < List.length Γ) body :
    (safe_nth Γ (exist _ i isdecl)).(decl_body) = Some body ->
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

(** Constant unfolding *) (* TODO Universes *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) body

(* TODO Proj CoFix *)

| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' : redbrs1 Σ Γ brs brs' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (tApp N1 M2)
| app_red_r M2 N2 M1 : reds1 Σ Γ M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na na' M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na' N1 M2)
| prod_red_r na na' M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na' M1 N2)

| evar ev l l' : reds1 Σ Γ l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)

with reds1 (Σ : global_declarations) (Γ : context): list term -> list term -> Prop :=
| reds1_hd hd hd' tl : red1 Σ Γ hd hd' -> reds1 Σ Γ (hd :: tl) (hd' :: tl)
| reds1_tl hd tl tl' : reds1 Σ Γ tl tl' -> reds1 Σ Γ (hd :: tl) (hd :: tl')

with redbrs1 (Σ : global_declarations) (Γ : context) : list (nat * term) -> list (nat * term) -> Prop :=
| redbrs1_hd n hd hd' tl : red1 Σ Γ hd hd' -> redbrs1 Σ Γ ((n, hd) :: tl) ((n, hd') :: tl)
| redbrs1_tl hd tl tl' : redbrs1 Σ Γ tl tl' -> redbrs1 Σ Γ (hd :: tl) (hd :: tl').

(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Prop :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

(** ** Term equality and cumulativity *)

Definition eq_string s s' :=
  if string_dec s s' then true else false.

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

Definition eq_universe φ s s' :=
  let cf := default_checker_flags in
  if univ.Universe.equal s s' then true
  else uGraph.check_leq φ s s' && uGraph.check_leq φ s' s.

Definition leq_universe `{checker_flags} φ s s' :=
  if univ.Universe.equal s s' then true
  else uGraph.check_leq φ s s'.

(* ** Syntactic equality up-to universes

  We shouldn't look at printing annotations *)

Fixpoint eq_term (φ : uGraph.t) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tMeta n, tMeta n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_evar ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => eq_universe φ s s'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tCast t _ v, tCast u _ v' => eq_term φ t u && eq_term φ v v'
  | tConst c u, tConst c' u' => eq_constant c c' (* TODO Universes *)
  | tInd i u, tInd i' u' => eq_ind i i'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && eq_term φ t t'
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
  | tCast t _ v, tCast u _ v' => leq_term φ t u
  | tConst c u, tConst c' u' => eq_constant c c' (* TODO Universes *)
  | tInd i u, tInd i' u' => eq_ind i i'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && leq_term φ t t'
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

(** ** Utilities for typing *)

(** Decompose an arity into a context and a sort *)

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

(** Make a lambda/let-in string of abstractions from a context [Γ], ending with term [t]. *)

Fixpoint it_mkLambda_or_LetIn (l : context) (t : term) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tLambda d.(decl_name) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) b d.(decl_type) acc
       end) l t.

(** Make a list of variables of length [#|Γ|], starting at [acc]. *)

Fixpoint rels_of {A} (Γ : list A) acc : list term :=
  match Γ with
  | _ :: Γ' => tRel acc :: rels_of Γ' (S acc)
  | [] => []
  end.

(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Definition types_of_case pars p pty decl :=
  match destArity [] decl.(ind_type), destArity [] pty with
  | Some (args, s), Some (args', s') =>
    let brs :=
        List.map (fun '(id, t, ar) => (ar, substl (p :: pars) t)) decl.(ind_ctors)
    in Some (args, args', s', brs)
  | _, _ => None
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

Definition eq_opt_term φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term φ t u
  | None, None => true
  | _, _ => false
  end.

Definition eq_decl φ (d d' : context_decl) :=
  eq_opt_term φ d.(decl_body) d'.(decl_body) && eq_term φ d.(decl_type) d'.(decl_type).

Definition eq_context φ (Γ Δ : context) :=
  forallb2 (eq_decl φ) Γ Δ.

Definition check_correct_arity φ decl ind u ctx pars pctx :=
  let inddecl :=
      {| decl_name := nNamed decl.(ind_name);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (pars ++ rels_of ctx 0) |}
  in eq_context φ (inddecl :: subst_instance_context u ctx) pctx.

Inductive Forall2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  Forall2_nil : Forall2 R [] []
| Forall2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').

(** ** Typing relation *)

Inductive typing `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Type :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |- (tRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort l :
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
    typing_spine Σ Γ t_ty l t' ->
    Σ ;;; Γ |- (tApp t l) : t'

| type_Const cst u : (* TODO Universes *)
    forall decl (isdecl : declared_constant (fst Σ) cst decl),
    consistent_universe_context_instance Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance_constr u decl.(cst_type)

| type_Ind ind u :
    forall univs decl (isdecl : declared_inductive (fst Σ) ind univs decl),
    consistent_universe_context_instance Σ univs u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance_constr u decl.(ind_type)

| type_Construct ind i u :
    forall univs decl (isdecl : declared_constructor (fst Σ) (ind, i) univs decl),
    consistent_universe_context_instance Σ univs u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor (fst Σ) (ind, i) univs u decl isdecl

| type_Case ind u npar p c brs args :
    forall decl (isdecl : declared_minductive (fst Σ) (inductive_mind ind) decl),
    forall univs decl' (isdecl' : declared_inductive (fst Σ) ind univs decl'),
    decl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case pars p pty decl' = Some (indctx, pctx, ps, btys) ->
    check_correct_arity (snd Σ) decl' ind u indctx pars pctx = true ->
    List.Exists (fun sf => universe_family ps = sf) decl'.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    Forall2 (fun x y => (fst x = fst y) * (Σ ;;; Γ |- snd x : snd y)) brs btys ->
    Σ ;;; Γ |- tCase (ind, npar) p c brs : tApp p (List.skipn npar args ++ [c])

| type_Proj p c u :
    forall decl (isdecl : declared_projection (fst Σ) p decl) args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    let ty := snd decl in
    Σ ;;; Γ |- tProj p c : substl (c :: rev args) ty

| type_Fix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype) in
    (** TODO check well-formed fix *)
    Σ ;;; Γ |- tFix mfix n : ty

| type_CoFix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype) in
    (** TODO check well-formed cofix *)
    Σ ;;; Γ |- tCoFix mfix n : ty

| type_Conv t A B s :
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (@typing _ Σ Γ t T) : type_scope

(* Typing of "spines", currently just the arguments of applications *)

with typing_spine `{checker_flags} (Σ : global_context) (Γ : context) : term -> list term -> term -> Prop :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_const hd tl na A B T B' :
    Σ ;;; Γ |- tProd na A B <= T ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

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

(** *** Typing of inductive declarations *)

Inductive type_constructors `{checker_flags} (Σ : global_context) (Γ : context) :
  list (ident * term * nat) -> Type :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections `{checker_flags} (Σ : global_context) (Γ : context) :
  list (ident * term) -> Type :=
| type_projs_nil : type_projections Σ Γ []
| type_projs_cons id t l :
    isType Σ Γ t ->
    type_projections Σ Γ l ->
    type_projections Σ Γ ((id, t) :: l).

Definition arities_context (l : list one_inductive_body) :=
  rev_map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

Definition isArity `{checker_flags} Σ Γ T :=
  isType Σ Γ T (* FIXME  /\ decompose_prod_n *).

Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).
Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |").

Inductive type_inddecls `{checker_flags} (Σ : global_context) (pars : context) (Γ : context) :
  list one_inductive_body -> Type :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs kelim l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** Projections are well-typed *)
    type_projections Σ (Γ ,,, pars ,, vass nAnon ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    (** TODO: check kelim*)
    type_inddecls Σ pars Γ (Build_one_inductive_body na ty kelim cstrs projs :: l).

Definition type_inductive `{checker_flags} Σ inds :=
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ [] (arities_context inds) inds.

(** *** Typing of constant declarations *)

Definition type_constant_decl `{checker_flags} Σ d :=
  match d.(cst_body) with
  | Some trm => Σ ;;; [] |- trm : d.(cst_type)
  | None => isType Σ [] d.(cst_type)
  end.

Definition type_global_decl `{checker_flags} Σ decl :=
  match decl with  (* TODO universes *)
  | ConstantDecl id d => type_constant_decl Σ d
  | InductiveDecl ind inds => type_inductive Σ inds.(ind_bodies)
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

Inductive fresh_global (s : string) : global_declarations -> Prop :=
| fresh_global_nil : fresh_global s nil
| fresh_global_cons env g :
    fresh_global s env -> global_decl_ident g <> s ->
    fresh_global s (cons g env).

Inductive type_global_env `{checker_flags} φ : global_declarations -> Type :=
| globenv_nil : wf_graph φ -> type_global_env φ []
| globenv_decl Σ d :
    type_global_env φ Σ ->
    fresh_global (global_decl_ident d) Σ ->
    type_global_decl (Σ, φ) d ->
    type_global_env φ (d :: Σ).

(** *** Typing of local environments *)

Definition type_local_decl `{checker_flags} Σ Γ d :=
  match d.(decl_body) with
  | None => isType Σ Γ d.(decl_type)
  | Some body => Σ ;;; Γ |- body : d.(decl_type)
  end.

Inductive type_local_env `{checker_flags} (Σ : global_context) : context -> Prop :=
| localenv_nil : type_local_env Σ []
| localenv_cons Γ d :
    type_local_env Σ Γ ->
    type_local_decl Σ Γ d ->
    type_local_env Σ (Γ ,, d).

(** *** Typing of programs *)
Definition type_program `{checker_flags} (p : program) (ty : term) : Prop :=
  let Σ := reconstruct_global_context (fst p) in
  squash (Σ ;;; [] |- (snd p) : ty).

(** ** Tests *)

Quote Recursively Definition foo := 0.

Ltac setenv na :=
  match goal with
    |- ?Σ ;;; ?Γ |- _ : _ => set(na := Σ)
  end.

Ltac construct :=
  match goal with
    |- ?Σ ;;; ?Γ |- tConstruct ?c ?i ?u : _ =>
    let H := fresh in let H' := fresh in evar(decl:(ident * term * nat)%type);
                                         evar(univs:universe_context);
    unshelve assert(H:declared_constructor (fst Σ) (c,i) ?univs ?decl) by repeat econstructor;
    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
    clear H; apply H'; try trivial
  end.

Quote Definition natr := nat.

Goal let cf := default_checker_flags in type_program foo natr.
Proof.
  intro cf.
  red.
  simpl. constructor.
  setenv Σ.
  now construct.
Qed.

Quote Recursively Definition foo' := 1.
Goal let cf := default_checker_flags in  type_program foo' natr.
Proof.
  intro cf.
  red.
  simpl. constructor.
  setenv Σ.
  econstructor.
  construct.
  econstructor. apply cumul_refl'.
  construct.
  econstructor.
Qed.


(** ** Induction principle for terms up-to a global environment *)

Definition on_decl P d :=
  match d with
  | ConstantDecl id cst =>
    P cst.(cst_type) /\ match cst.(cst_body) with Some b => P b | None => True end
  | InductiveDecl id ind =>
    Forall (fun ind => P ind.(ind_type)) ind.(ind_bodies)
  end.

Inductive Forall_decls P : global_declarations -> Prop :=
| Forall_decls_nil : Forall_decls P nil
| Forall_decls_cons Σ d :
    Forall_decls P Σ ->
    on_decl (P Σ) d ->
    Forall_decls P (d :: Σ).

Lemma term_env_ind :
  forall P : global_declarations -> term -> Prop,
    (forall Σ n, P Σ (tRel n)) ->
    (forall Σ i, P Σ (tVar i)) ->
    (forall Σ n, P Σ (tMeta n)) ->
    (forall Σ (n : nat) (l : list term), Forall (P Σ) l -> P Σ (tEvar n l)) ->
    (forall Σ s, P Σ (tSort s)) ->
    (forall Σ t, P Σ t -> forall (c : cast_kind) (t0 : term), P Σ t0 -> P Σ (tCast t c t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tProd n t t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tLambda n t t0)) ->
    (forall Σ (n : name) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall t1 : term, P Σ t1 -> P Σ (tLetIn n t t0 t1)) ->
    (forall Σ t, P Σ t -> forall l : list term, Forall (P Σ) l -> P Σ (tApp t l)) ->
    (forall Σ s u, P Σ (tConst s u)) ->
    (forall Σ i u, P Σ (tInd i u)) ->
    (forall Σ (i : inductive) (n : nat) u, P Σ (tConstruct i n u)) ->
    (forall Σ (p : inductive * nat) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Σ) l -> P Σ (tCase p t t0 l)) ->
    (forall Σ (s : projection) (t : term), P Σ t -> P Σ (tProj s t)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tFix m n)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tCoFix m n)) ->
    forall Σ t, P Σ t.
Proof.
  intros until t.
  revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
Defined.

Lemma term_env_ind' :
  forall P : global_declarations -> term -> Prop,
    (forall Σ n, P Σ (tRel n)) ->
    (forall Σ i, P Σ (tVar i)) ->
    (forall Σ n, P Σ (tMeta n)) ->
    (forall Σ (n : nat) (l : list term), Forall (P Σ) l -> P Σ (tEvar n l)) ->
    (forall Σ s, P Σ (tSort s)) ->
    (forall Σ t, P Σ t -> forall (c : cast_kind) (t0 : term), P Σ t0 -> P Σ (tCast t c t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tProd n t t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tLambda n t t0)) ->
    (forall Σ (n : name) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall t1 : term, P Σ t1 -> P Σ (tLetIn n t t0 t1)) ->
    (forall Σ t, P Σ t -> forall l : list term, Forall (P Σ) l -> P Σ (tApp t l)) ->
    (forall Σ s u, P Σ (tConst s u)) ->
    (forall Σ i u, P Σ (tInd i u)) ->
    (forall Σ (i : inductive) (n : nat) u, P Σ (tConstruct i n u)) ->
    (forall Σ (p : inductive * nat) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Σ) l -> P Σ (tCase p t t0 l)) ->
    (forall Σ (s : projection) (t : term), P Σ t -> P Σ (tProj s t)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tFix m n)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tCoFix m n)) ->
    forall Σ, Forall_decls P Σ.
Proof.
  intros until Σ.
  revert Σ.
  fix auxt 1.
  destruct Σ. constructor. constructor.
  apply auxt.
  destruct g.
  simpl. split. apply term_env_ind; auto. destruct cst_body. apply term_env_ind; auto. exact I.
  red.
  induction (ind_bodies m). constructor.
  constructor. apply term_env_ind; auto. apply IHl.
Qed.

(** ** Induction principle for typing up-to a global environment *)


Inductive Forall (A : Set) (P : A -> Type) : list A -> Type :=
    Forall_nil : Forall A P []
  | Forall_cons : forall (x : A) (l : list A),
                  P x -> Forall A P l -> Forall A P (x :: l).
Arguments Forall {A} P l.

Definition on_decl_typing (P : term -> term -> Type) d :=
  match d with
  | ConstantDecl id cst =>
    match cst.(cst_body) with
    | Some b => P b cst.(cst_type)
    | None => forall s, P cst.(cst_type) s
    end
  | InductiveDecl id ind =>
    Forall (fun ind => forall s, P ind.(ind_type) s) ind.(ind_bodies)
  end.

Inductive Forall_decls_typing `{checker_flags} φ (P : global_declarations -> term -> term -> Type) : global_declarations -> Type :=
| Forall_decls_typing_nil : Forall_decls_typing φ P nil
| Forall_decls_typing_cons Σ d :
    Forall_decls_typing φ P Σ ->
    on_decl_typing (fun t T => (Σ, φ) ;;; [] |- t : T -> P Σ t T) d ->
    Forall_decls_typing φ P (d :: Σ).

Definition size := nat.

Section Forall2_size.
  Context {A} (P : A -> A -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint forall2_size {l1 l2 : list A} (f : Forall2 P l1 l2) : size :=
  match f with
  | Forall2_nil => 0
  | Forall2_cons x y l l' rxy rll' => fn _ _ rxy + forall2_size rll'
  end.
End Forall2_size.

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
  | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
  | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
  | H1 : size |- _  => exact (S H1)
  | H : declared_constant _ _ _ |- _ => exact 2%nat
  | _ : declared_inductive _ _ _ |- _  => exact 2%nat
  | _ : declared_constructor _ _ _ |- _  => exact 2%nat
  | _ : declared_projection _ _ _ |- _  => exact 2%nat
  | _ => exact 1
  end.
  exact (S (Nat.max d1 (Nat.max d2
      (forall2_size _ (fun x y p => typing_size Σ Γ (snd x) (snd y) (snd p)) f)))).
Defined.

Fixpoint globenv_size (Σ : global_declarations) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_context, including size of the global declarations in it
    - size of the derivation. *)

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.
Require Import Wf.

(** Define non-dependent lexicographic products *)

Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Arguments lexprod [A B].

Notation wf := (fun Σ => type_global_env (snd Σ) (fst Σ)).

Conjecture wf_graph_prop_set : forall φ (H : wf_graph φ),
    check_lt φ Universe.type0m Universe.type1 = true /\
    check_lt φ Universe.type0 Universe.type1 = true.

Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Set) :=
  forall Σ (wfΣ : wf Σ) Γ t T, Σ ;;; Γ |- t : T ->
    Forall_decls_typing (snd Σ) (fun Σ' t ty => P (Σ', snd Σ) [] t ty) (fst Σ) *
    P Σ Γ t T.

Lemma env_prop_typing `{checker_flags} P : env_prop P ->
  forall Σ (wf : wf Σ) (Γ : context) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma env_prop_sigma `{checker_flags} P : env_prop P ->
  forall Σ (wf : wf Σ),
    Forall_decls_typing (snd Σ) (fun Σ0 (t0 ty : term) => P (Σ0, snd Σ) [] t0 ty) (fst Σ).
Proof. intros. eapply X. apply wf. apply (type_Sort Σ [] Level.prop).
Defined.

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.

 TODO: thread the property on local contexts as well, avoiding to redo work at binding constructs. *)

Require Import Lia.

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_context -> context -> term -> term -> Set),
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : nat) (isdecl : n < #|Γ|),
        P Σ Γ (tRel n)
          (lift0 (S n) (decl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (l : Level.t), P Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (c : term) (k : cast_kind) (t : term) (s : universe),
        Σ ;;; Γ |- t : tSort s -> P Σ Γ t (tSort s) -> Σ ;;; Γ |- c : t -> P Σ Γ c t -> P Σ Γ (tCast c k t) t) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (t b : term) (s1 s2 : universe),
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n n' : name) (t b : term) (s1 : universe) (bty : term),
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n' t bty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (b b_ty b' : term) (s1 : universe) (b'_ty : term),
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (t : term) (l : list term) (t_ty t' : term),
        Σ ;;; Γ |- t : t_ty -> P Σ Γ t t_ty -> typing_spine Σ Γ t_ty l t' -> P Σ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (cst : ident) u (decl : constant_body),
        declared_constant (fst Σ) cst decl ->
        Forall_decls_typing (snd Σ) (fun Σ' t ty => P (Σ', snd Σ) [] t ty) (fst Σ) ->
        P Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

        (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) u univs (decl : one_inductive_body),
        declared_inductive (fst Σ) ind univs decl -> P Σ Γ (tInd ind u) (subst_instance_constr u (ind_type decl))) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) (i : nat) u univs (decl : ident * term * nat)
          (isdecl : declared_constructor (fst Σ) (ind, i) univs decl),
        P Σ Γ (tConstruct ind i u) (type_of_constructor (fst Σ) (ind, i) univs u decl isdecl)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) u (npar : nat) (p c : term) (brs : list (nat * term))
          (args : list term) (decl : mutual_inductive_body),
        declared_minductive (fst Σ) (inductive_mind ind) decl ->
        forall univs ( decl' : one_inductive_body ),
        declared_inductive (fst Σ) ind univs decl' ->
        ind_npars decl = npar ->
        let pars := firstn npar args in
        forall (pty : term), Σ ;;; Γ |- p : pty -> P Σ Γ p pty ->
        forall indctx pctx ps btys,
        types_of_case pars p pty decl' = Some (indctx, pctx, ps, btys) ->
        check_correct_arity (snd Σ) decl' ind u indctx pars pctx = true ->
        Exists (fun sf : sort_family => universe_family ps = sf) (ind_kelim decl') ->
        P Σ Γ p pty ->
        Σ;;; Γ |- c : mkApps (tInd ind u) args ->
        P Σ Γ c (mkApps (tInd ind u) args) ->
        Forall2 (fun x y : nat * term => (fst x = fst y) * (Σ;;; Γ |- snd x : snd y)
                                         * P Σ Γ (snd x) (snd y))%type brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (tApp p (skipn npar args ++ [c]))) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (p : projection) (c : term) u (decl : ident * term),
        declared_projection (fst Σ) p decl ->
        forall args : list term,
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        let ty := snd decl in P Σ Γ (tProj p c) (substl (c :: rev args) ty)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tCoFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (t A B : term) (s : universe),
        Σ ;;; Γ |- t : A ->
                       P Σ Γ t A -> Σ ;;; Γ |- B : tSort s -> P Σ Γ B (tSort s) -> Σ ;;; Γ |- A <= B -> P Σ Γ t B) ->

       env_prop P.
Proof.
  unfold env_prop.
  intros P X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ & { Γ : context & { t : term & { T : term & Σ ;;; Γ |- t : T }}} }})
               (lexprod (MR lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => MR lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 x)))))))).
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ t (existT _ _ H)))) : { Σ : _ & { wfΣ : wf Σ & { Γ : context & { t : term & { T : term & Σ ;;; Γ |- t : T }}} }}).
  change Σ with (projT1 foo).
  change Γ with (projT1 (projT2 (projT2 foo))).
  change t with (projT1 (projT2 (projT2 (projT2 foo)))).
  change T with (projT1 (projT2 (projT2 (projT2 (projT2 foo))))).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_lexprod; intros; apply measure_wf; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ t T H.
  intros (Σ&wfΣ&Γ&t&t0&H). simpl.
  intros IH. unfold MR in IH. simpl in IH.
  split.
  destruct Σ as [Σ φ]. destruct Σ.
  constructor.
  cbn in wfΣ; inversion_clear wfΣ.
  constructor.
  specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ Γ (existT _ (tSort Universe.type0m ) (existT _ _ (type_Sort _ _ Level.prop))))))).
  simpl in IH. forward IH. constructor 1. simpl. omega.
  apply IH.
  destruct g; simpl.
  destruct cst_body.
  simpl.
  intros.
  specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ _ (existT _ _ X16)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH.
  intros.
  specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ _ (existT _ _ X16)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH.
  intros.
  induction (ind_bodies m). constructor.
  constructor; auto.
  intros.
  specialize (IH (existT _ (Σ, φ) (existT _ X14 (existT _ _ (existT _ _ (existT _ _ X16)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH.

  assert (forall Γ t T (Hty : Σ ;;; Γ |- t : T),
             typing_size Hty <
             typing_size H ->
             Forall_decls_typing (snd Σ) (fun Σ' (t ty : term) => P (Σ', snd Σ) [] t ty) (fst Σ) *
             P Σ Γ t T).
  intros.
  specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ _ (existT _ _ Hty)))))).
  simpl in IH.
  forward IH.
  constructor 2. simpl. apply H0.
  apply IH. clear IH.
  destruct H;
try solve [  match reverse goal with
    H : _ |- _ => eapply H
  end; eauto;
             unshelve eapply X14; simpl; auto with arith].
  match reverse goal with
    H : _ |- _ => eapply H
  end; eauto;
  unshelve eapply X14; simpl; auto with arith;
    repeat (rewrite Nat.max_comm, <- Nat.max_assoc; auto with arith).
  apply X6; eauto.
  specialize (X14 [] _ _ (type_Sort _ _ Level.prop)).
  simpl in X14. forward X14; auto. apply X14.
  eapply X9; eauto.
  eapply (X14 _ _ _ H); eauto. simpl; auto with arith.
  eapply (X14 _ _ _ H); eauto. simpl; auto with arith. simpl in *.
  eapply (X14 _ _ _ H0); eauto. simpl; auto with arith. simpl in *.
  induction f; simpl; lia.
  simpl in *.
  revert f X14. clear. intros.
  induction f; simpl in *. constructor.
  destruct r. constructor. split; auto.
  eapply (X14 _ _ _ t); eauto. simpl; auto with arith.
  lia.
  apply IHf. auto. intros.
  eapply (X14 _ _ _ Hty). lia.
Qed.
