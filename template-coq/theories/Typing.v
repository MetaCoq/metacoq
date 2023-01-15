(* Distributed under the terms of the MIT license. *)
(** This defines relation operators in Type *)
From Equations.Type Require Import Relation.
From Equations Require Import Equations.
From Coq Require Import ssreflect Wellfounded Relation_Operators CRelationClasses.
From MetaCoq.Template Require Import config utils Ast AstUtils Environment Primitive
    LiftSubst UnivSubst EnvironmentTyping Reflect ReflectAst TermEquality WfAst.

Import MCMonadNotation.

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)

Definition isSort T :=
  match T with
  | tSort u => true
  | _ => false
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => true
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => false
  end.

Definition type_of_constructor mdecl cdecl (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u cdecl.(cstr_type)).

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

Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.

Definition dummy_branch : branch term := mk_branch [] tDummy.

Definition iota_red npar args bctx br :=
  subst (List.rev (List.skipn npar args)) 0 (expand_lets bctx br.(bbody)).

(** For cases typing *)

Inductive instantiate_params_subst_spec : context -> list term -> list term -> term -> list term -> term -> Prop :=
| instantiate_params_subst_nil s ty : instantiate_params_subst_spec [] [] s ty s ty
| instantiate_params_subst_vass na ty params pari pars s na' ty' pty s' pty' :
  instantiate_params_subst_spec params pars (pari :: s) pty s' pty' ->
  instantiate_params_subst_spec (vass na ty :: params) (pari :: pars) s (tProd na' ty' pty) s' pty'
| instantiate_params_subst_vdef na b ty params pars s na' b' ty' pty s' pty' :
  instantiate_params_subst_spec params pars (subst s 0 b :: s) pty s' pty' ->
  instantiate_params_subst_spec (vdef na b ty :: params) pars s (tLetIn na' b' ty' pty) s' pty'.
Derive Signature for instantiate_params_subst_spec.


(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst
         (params : context)
         (pars s : list term)
         (ty : term) : option (list term × term) :=
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

Lemma instantiate_params_substP params pars s ty s' ty' :
  instantiate_params_subst params pars s ty = Some (s', ty') <->
  instantiate_params_subst_spec params pars s ty s' ty'.
Proof.
  induction params in pars, s, ty |- *.
  - split. destruct pars => /= // => [= -> ->].
    constructor.
    intros. depelim H. reflexivity.
  - split.
    * destruct a as [na [b|] ?] => /=.
      destruct ty => //.
      move/IHparams.
      intros. now constructor.
      destruct ty => //.
      destruct pars => //.
      move/IHparams.
      now constructor.
    * intros H; depelim H; simpl.
      now apply IHparams.
      now apply IHparams.
Qed.

(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

(* NOTE: SPROP: we ignore relevance in the reduction  for now *)
Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
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
| red_iota ci mdecl idecl cdecl c u args p brs br :
    nth_error brs c = Some br ->
    (* In the compact representation, reduction must fetch the
       global declaration of the constructor to gather the let-bindings
       in its argument context. Implementations can be more clever
       in the common case where no let-binding appears to avoid this. *)
    declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
    let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
    #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
    red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args bctx br)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (tApp (tFix mfix idx) args) (mkApps fn args)

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
    red1 Σ Γ (tConst c u) (subst_instance u body)

(** Proj *)
| red_proj p u args arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    red1 Σ Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg


| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred_param ind params params' puinst pcontext preturn c brs :
    OnOne2 (red1 Σ Γ) params params' ->
    red1 Σ Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
             (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)

| case_red_pred_return ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl)
                       params puinst pcontext preturn preturn' c brs :
    let p := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn |} in
    let p' := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn' |} in
    red1 Σ (Γ ,,, case_predicate_context ind.(ci_ind) mdecl idecl p) preturn preturn' ->
    red1 Σ Γ (tCase ind p c brs)
             (tCase ind p' c brs)

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)

| case_red_brs ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs' :
    OnOne2All (fun brctx br br' =>
      on_Trel_eq (red1 Σ (Γ ,,, brctx)) bbody bcontext br br')
      (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2)
| app_red_r M2 N2 M1 : OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)
| cast_red M1 k M2 : red1 Σ Γ (tCast M1 k M2) M1

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
       (forall (Γ : context) (na : aname) (t b a : term) (l : list term),
        P Γ (tApp (tLambda na t b) (a :: l)) (mkApps (b {0 := a}) l)) ->
       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) mdecl idecl cdecl (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
          let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
          #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
                (iota_red ci.(ci_npar) args bctx br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (tApp (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) (ip : case_info) (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t) (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ind : case_info) params params' puinst pcontext preturn c brs,
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) params params' ->
           P Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
               (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)) ->

       (forall (Γ : context) (ci : case_info)
               idecl mdecl (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl)
               params puinst pcontext preturn preturn' c brs,
          let p := (mk_predicate puinst params pcontext preturn) in
           red1 Σ (Γ ,,, case_predicate_context ci.(ci_ind) mdecl idecl p) preturn preturn' ->
           P (Γ ,,, case_predicate_context ci.(ci_ind) mdecl idecl p) preturn preturn' ->
           P Γ (tCase ci p c brs)
               (tCase ci (mk_predicate puinst params pcontext preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs',
          OnOne2All (fun brctx br br' =>
            on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, brctx)) (P (Γ ,,, brctx))) bbody bcontext br br')
              (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
          P Γ (tCase ind p c brs) (tCase ind p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' -> P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : list term), red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tApp M1 M2) (mkApps N1 M2)) ->

       (forall (Γ : context) (M2 N2 : list term) (M1 : term), OnOne2 (fun x y => red1 Σ Γ x y * P Γ x y)%type M2 N2 -> P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term), OnOne2 (fun x y => red1 Σ Γ x y * P Γ x y) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tCast M1 k M2) (tCast N1 k M2)) ->

       (forall (Γ : context) (M2 : term) (k : cast_kind) (N2 M1 : term),
        red1 Σ Γ M2 N2 -> P Γ M2 N2 -> P Γ (tCast M1 k M2) (tCast M1 k N2)) ->

       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 : term),
           P Γ (tCast M1 k M2) M1) ->

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
  intros. rename X30 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1;
    try solve [
          match goal with
          | H : _ |- _ => eapply H; eauto; fail
          end].

  - apply X13.
    revert params params' o.
    fix auxl 3.
    intros params params' [].
    + constructor. split; auto.
    + constructor. auto.

  - eapply X16; eauto.
    revert brs brs' o.
    intros brs.
    generalize (case_branches_contexts (ci_ind ind) mdecl idecl p brs).
    revert brs.
    fix auxl 4.
    intros i l l' Hl. destruct Hl.
    + constructor; intros.
      intuition auto. auto.
    + constructor. eapply auxl. apply Hl.

  - apply X19.
    revert M2 N2 o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto.
    + constructor. auto.

  - apply X22.
    revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - apply X26.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - apply X27.
    revert o. generalize (fix_context mfix0). intros c H28.
    revert mfix0 mfix1 H28; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X28.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X29.
    revert o. generalize (fix_context mfix0). intros c H28.
    revert mfix0 mfix1 H28; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.


(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Type :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

(** ** Term equality and cumulativity *)

(* ** Syntactic equality up-to universes

  We shouldn't look at printing annotations nor casts.
  It is however not possible to write a structurally recursive definition
  for syntactic equality up-to casts due to the [tApp (tCast f _ _) args] case.
  We hence implement first an equality which considers casts and do a stripping
  phase of casts before checking equality. *)

Definition eq_term_nocast `{checker_flags} (Σ : global_env) (φ : ConstraintSet.t) (t u : term) :=
  eq_term Σ φ (strip_casts t) (strip_casts u).

Definition leq_term_nocast `{checker_flags} (Σ : global_env) (φ : ConstraintSet.t) (t u : term) :=
  leq_term Σ φ (strip_casts t) (strip_casts u).

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <=[ pb ] u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity:

  Reduction to terms in the cumulativity relation. In PCUIC we show that
  this is equivalent to the reflexive-transitive closure or reduction + leq_term
  on well-typed terms.
*)

Inductive cumul_gen `{checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
 | cumul_refl t u : compare_term pb Σ (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <=[pb] u
 | cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <=[pb] u -> Σ ;;; Γ |- t <=[pb] u
 | cumul_red_r t u v : Σ ;;; Γ |- t <=[pb] v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <=[pb] u
  where "Σ ;;; Γ |- t <=[ pb ] u " := (cumul_gen Σ Γ pb t u).

(** *** Conversion

  Reduction to terms in the eq_term relation
 *)

Notation " Σ ;;; Γ |- t = u " := (cumul_gen Σ Γ Conv t u) (at level 50, Γ, t, u at next level) : type_scope.
Notation " Σ ;;; Γ |- t <= u " := (cumul_gen Σ Γ Cumul t u) (at level 50, Γ, t, u at next level) : type_scope.

Lemma conv_refl' `{checker_flags} : forall Σ Γ t, Σ ;;; Γ |- t = t.
  intros. constructor. apply eq_term_refl.
Defined.

Lemma cumul_refl' `{checker_flags} : forall Σ Γ t, Σ ;;; Γ |- t <= t.
  intros. constructor. apply leq_term_refl.
Defined.

Definition eq_opt_term `{checker_flags} Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} Σ φ (d d' : context_decl) :=
  eq_opt_term Σ φ d.(decl_body) d'.(decl_body) * eq_term Σ φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} Σ φ (Γ Δ : context) :=
  All2 (eq_decl Σ φ) Γ Δ.

(** ** Typing relation *)

Module TemplateEnvTyping := EnvTyping TemplateTerm Env TemplateTermUtils.
Include TemplateEnvTyping.

Module TemplateConversion := Conversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
Include TemplateConversion.

Module TemplateGlobalMaps := GlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup.
Include TemplateGlobalMaps.

Module TemplateConversionPar <: ConversionParSig TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  Definition cumul_gen := @cumul_gen.
End TemplateConversionPar.


Class GuardChecker :=
{ (* Structural recursion check *)
  fix_guard : global_env_ext -> context -> mfixpoint term -> bool ;
  (* Guarded by destructors check *)
  cofix_guard : global_env_ext -> context -> mfixpoint term -> bool ;

  fix_guard_red1 Σ Γ mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    fix_guard Σ (Γ ,,, Γ') mfix ->
    fix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  fix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    fix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  fix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    fix_guard Σ Γ mfix ->
    fix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  fix_guard_extends Σ Γ mfix (Σ' : global_env_ext) :
    fix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    fix_guard Σ' Γ mfix ;

  cofix_guard_red1 Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    cofix_guard Σ (Γ ,,, Γ') mfix ->
    cofix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  cofix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    cofix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    cofix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  cofix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    cofix_guard Σ Γ mfix ->
    cofix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  cofix_guard_extends Σ Γ mfix (Σ' : global_env_ext) :
    cofix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    cofix_guard Σ' Γ mfix }.

(* AXIOM GUARD CONDITION *)
Axiom guard_checking : GuardChecker.
Global Existing Instance guard_checking.

(*
Definition build_branch_context ind mdecl (cty: term) p : option context :=
  let inds := inds ind.(inductive_mind) p.(puinst) mdecl.(ind_bodies) in
  let ty := subst0 inds (subst_instance p.(puinst) cty) in
  match instantiate_params (subst_instance p.(puinst) mdecl.(ind_params)) p.(pparams) ty with
  | Some ty =>
    let '(sign, ccl) := decompose_prod_assum [] ty in
    Some sign
  | None => None
  end.

(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat * context * term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance u t) in
    match instantiate_params (subst_instance u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
      Some (ar, sign, mkApps (lift0 nargs p) args)
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
         (ar, sign, (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed.
*)
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

Definition check_recursivity_kind (Σ : global_env) ind r :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mib) => eqb mib.(ind_finite) r
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
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive fixpoints are all on the same mututal
        inductive block *)
    forallb (eqb ind) inds &&
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
    forallb (eqb ind) inds &&
    check_recursivity_kind Σ ind CoFinite
  | _ => false
  end.

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort s :
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Cast c k t s :
    Σ ;;; Γ |- t : tSort s ->
    Σ ;;; Γ |- c : t ->
    Σ ;;; Γ |- tCast c k t : t

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : tSort s2 ->
    Σ ;;; Γ |- tProd n t b : tSort (Universe.sort_of_product s1 s2)

| type_Lambda n t b s1 bty :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : bty ->
    Σ ;;; Γ |- tLambda n t b : tProd n t bty

| type_LetIn n b b_ty b' s1 b'_ty :
    Σ ;;; Γ |- b_ty : tSort s1 ->
    Σ ;;; Γ |- b : b_ty ->
    Σ ;;; Γ ,, vdef n b b_ty |- b' : b'_ty ->
    Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ;;; Γ |- t : t_ty ->
    isApp t = false -> l <> [] -> (* Well-formed application *)
    typing_spine Σ Γ t_ty l t' ->
    Σ ;;; Γ |- tApp t l : t'

| type_Const cst u :
    wf_local Σ Γ ->
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance u decl.(cst_type)

| type_Ind ind u :
    wf_local Σ Γ ->
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance u idecl.(ind_type)

| type_Construct ind i u :
    wf_local Σ Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case (ci : case_info) p c brs indices ps :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
    mdecl.(ind_npars) = ci.(ci_npar) ->
    wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
    context_assumptions mdecl.(ind_params) = #|p.(pparams)| ->
    consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    ctx_inst typing Σ Γ (p.(pparams) ++ indices)
      (List.rev (ind_params mdecl ,,, ind_indices idecl)@[p.(puinst)]) ->
    Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    is_allowed_elimination Σ idecl.(ind_kelim) ps ->
    Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    isCoFinite mdecl.(ind_finite) = false ->
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    All2i (fun i cdecl br =>
      let brctxty := case_branch_type ci.(ci_ind) mdecl p ptm i cdecl br in
      (wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl)) *
      (Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) *
      (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps))
      0 idecl.(ind_ctors) brs ->
    Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj p c u :
    forall mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| type_Fix mfix n decl :
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ mfix ->
      Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Int p prim_ty cdecl :
    wf_local Σ Γ ->
    primitive_constant Σ primInt = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants cdecl ->
    Σ ;;; Γ |- tInt p : tConst prim_ty []

| type_Float p prim_ty cdecl :
    wf_local Σ Γ ->
    primitive_constant Σ primFloat = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants cdecl ->
    Σ ;;; Γ |- tFloat p : tConst prim_ty []

| type_Conv t A B s :
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T) : type_scope
  and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ) : type_scope

(* Typing of "spines", currently just the arguments of applications *)

with typing_spine `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_cons hd tl na A B s T B' :
    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- T <= tProd na A B ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

Derive Signature for typing typing_spine.

(** ** Typechecking of global environments *)

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

Definition infer_sorting {cf: checker_flags} Σ Γ T := { s : Universe.t & typing Σ Γ T (tSort s) }.

Module TemplateTyping <: Typing TemplateTerm Env TemplateTermUtils TemplateEnvTyping
  TemplateConversion TemplateConversionPar.

  Definition typing := @typing.
  Definition infer_sorting := @infer_sorting.

End TemplateTyping.

Module TemplateDeclarationTyping :=
  DeclarationTyping
    TemplateTerm
    Env
    TemplateTermUtils
    TemplateEnvTyping
    TemplateConversion
    TemplateConversionPar
    TemplateTyping
    TemplateLookup
    TemplateGlobalMaps.
Include TemplateDeclarationTyping.


Section Typing_Spine_size.
  Context `{checker_flags}.
  Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), typing Σ Γ t T -> size).
  Context (Σ : global_env_ext) (Γ : context).

  Fixpoint typing_spine_size t T U (s : typing_spine Σ Γ t T U) : size :=
  match s with
  | type_spine_nil _ => 0
  | type_spine_cons hd tl na A B s T B' typrod cumul ty s' =>
    (fn _ _ _ _ ty + fn _ _ _ _ typrod + typing_spine_size _ _ _ s')%nat
  end.
End Typing_Spine_size.

Section CtxInstSize.
  Context (typing : global_env_ext -> context -> term -> term -> Type)
  (typing_size : forall {Σ Γ t T}, typing Σ Γ t T -> size).

  Fixpoint ctx_inst_size {Σ Γ args Δ} (c : ctx_inst typing Σ Γ args Δ) : size :=
  match c with
  | ctx_inst_nil => 0
  | ctx_inst_ass na t i inst Δ ty ctxi => ((typing_size _ _ _ _ ty) + (ctx_inst_size ctxi))%nat
  | ctx_inst_def na b t inst Δ ctxi => S (ctx_inst_size ctxi)
  end.

End CtxInstSize.

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
    | H : All2i _ _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H : Alli _ _ _ |- _ => idtac
    | H : typing_spine _ _ _ _ _ |- _ => idtac
    | H : _ + _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
  - exact (S (All_local_env_size typing_size _ _ a)).
  - exact (S (All_local_env_size typing_size _ _ a)).
  - exact (S (Nat.max d (typing_spine_size typing_size _ _ _ _ _ t0))).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (S (All_local_env_size typing_size _ _ a))).
  - exact (S (Nat.max d1 (Nat.max d2
    (Nat.max (ctx_inst_size _ typing_size c1)
      (all2i_size _ (fun _ x y p => Nat.max (typing_size _ _ _ _ p.1.2) (typing_size _ _ _ _ p.2)) a0))))).
  - exact (S (Nat.max (Nat.max (All_local_env_size typing_size _ _ a) (all_size _ (fun x p => infer_sort_size (typing_sort_size typing_size) Σ _ _ p) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ p) a1))).
  - exact (S (Nat.max (Nat.max (All_local_env_size typing_size _ _ a) (all_size _ (fun x p => infer_sort_size (typing_sort_size typing_size) Σ _ _ p) a0)) (all_size _ (fun x p => typing_size Σ _ _ _ p) a1))).
  - exact (S (All_local_env_size typing_size _ _ a)).
  - exact (S (All_local_env_size typing_size _ _ a)).
Defined.

Lemma typing_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; simpl; try lia.
Qed.

Fixpoint globdecls_size (Σ : global_declarations) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globdecls_size Σ)
  end.

Definition globenv_size (Σ : global_env) : size :=
  globdecls_size Σ.(declarations).


(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} Σ := on_global_env cumul_gen (lift_typing typing) Σ.
Definition wf_ext `{checker_flags} := on_global_env_ext cumul_gen (lift_typing typing).

Lemma typing_wf_local `{checker_flags} {Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_local Σ Γ.
Proof.
  induction 1; eauto.
Defined.
#[global] Hint Resolve typing_wf_local : wf.

Lemma type_Prop `{checker_flags} Σ :
  Σ ;;; [] |- tSort Universe.lProp : tSort Universe.type1.
  change (  Σ ;;; [] |- tSort (Universe.lProp) : tSort Universe.type1);
  constructor;auto. constructor. constructor.
Defined.

Lemma type_Prop_wf `{checker_flags} Σ Γ :
  wf_local Σ Γ ->
  Σ ;;; Γ |- tSort Universe.lProp : tSort Universe.type1.
Proof.
  constructor;auto. constructor.
Defined.

Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) (PΓ : forall Σ Γ (wfΓ : wf_local Σ Γ), Type):=
  forall (Σ : global_env_ext) (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) t T (ty : Σ ;;; Γ |- t : T),
    on_global_env cumul_gen (lift_typing P) Σ * (PΓ Σ Γ (typing_wf_local ty) * P Σ Γ t T).

Lemma env_prop_typing `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma env_prop_wf_local `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ), PΓ Σ Γ wfΓ.
Proof. intros. red in X. now apply (X _ wfΣ _ wfΓ _ _ (type_Prop_wf Σ Γ wfΓ)). Qed.

Lemma env_prop_sigma `{checker_flags} {P PΓ} : env_prop P PΓ ->
  forall Σ (wfΣ : wf Σ), on_global_env cumul_gen (lift_typing P) Σ.
Proof.
  intros. eapply (X (empty_ext Σ)).
  apply wfΣ. constructor.
  apply type_Prop.
Defined.

Lemma wf_local_app_l `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
Proof.
  induction Γ'. auto.
  simpl. intros H'; inv H'; eauto.
Defined.
#[global] Hint Immediate wf_local_app_l : wf.

Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  All_local_env_size (@typing_size _) _ _ (typing_wf_local d) < typing_size d.
Proof.
  induction d; simpl;
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
    and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Inductive Forall_typing_spine `{checker_flags} Σ Γ (P : term -> term -> Type) :
  forall (T : term) (t : list term) (U : term), typing_spine Σ Γ T t U -> Type :=
| Forall_type_spine_nil T : Forall_typing_spine Σ Γ P T [] T (type_spine_nil Σ Γ T)
| Forall_type_spine_cons hd tl na A B s T B' tls
   (typrod : Σ ;;; Γ |- tProd na A B : tSort s)
   (cumul : Σ ;;; Γ |- T <= tProd na A B) (ty : Σ ;;; Γ |- hd : A) :
    P (tProd na A B) (tSort s) -> P hd A -> Forall_typing_spine Σ Γ P (B {0 := hd}) tl B' tls ->
    Forall_typing_spine Σ Γ P T (hd :: tl) B'
      (type_spine_cons Σ Γ hd tl na A B s T B' typrod cumul ty tls).

Implicit Types (Σ : global_env_ext).

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : forall Σ Γ, wf_local Σ Γ -> Type),

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
      All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ wfΓ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (u : Universe.t),
      PΓ Σ Γ wfΓ ->
      wf_universe Σ u ->
      P Σ Γ (tSort u) (tSort (Universe.super u))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (c : term) (k : cast_kind)
            (t : term) (s : Universe.t),
        Σ ;;; Γ |- t : tSort s -> P Σ Γ t (tSort s) -> Σ ;;; Γ |- c : t -> P Σ Γ c t -> P Σ Γ (tCast c k t) t) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term)
            (s1 : Universe.t) (bty : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (b b_ty b' : term)
            (s1 : Universe.t) (b'_ty : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) (l : list term) (t_ty t' : term),
        Σ ;;; Γ |- t : t_ty -> P Σ Γ t t_ty ->
        isApp t = false -> l <> [] ->
        forall (s : typing_spine Σ Γ t_ty l t'),
        Forall_typing_spine Σ Γ (fun t T => P Σ Γ t T) t_ty l t' s ->
        P Σ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
        on_global_env cumul_gen (lift_typing P) Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        on_global_env cumul_gen (lift_typing P) Σ.1 ->
        PΓ Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        on_global_env cumul_gen (lift_typing P) Σ.1 ->
        PΓ Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

     (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
      forall (ci : case_info) p c brs indices ps mdecl idecl
        (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
        on_global_env cumul_gen (lift_typing P) Σ.1 ->
        PΓ Σ Γ wfΓ ->
        mdecl.(ind_npars) = ci.(ci_npar) ->
        wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
        context_assumptions mdecl.(ind_params) = #|p.(pparams)| ->
        consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        ctx_inst (Prop_conj typing P) Σ Γ (p.(pparams) ++ indices)
        (List.rev (ind_params mdecl ,,, ind_indices idecl)@[p.(puinst)]) ->
        forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
        P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
        PΓ Σ (Γ ,,, predctx) (typing_wf_local pret) ->
        is_allowed_elimination Σ idecl.(ind_kelim) ps ->
        Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
        P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
        isCoFinite mdecl.(ind_finite) = false ->
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        All2i (fun i cdecl br =>
          let brctxty := case_branch_type ci.(ci_ind) mdecl p ptm i cdecl br in
          wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl) *
          Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2 *
          Prop_conj typing P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))
          0 idecl.(ind_ctors) brs ->
        P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        on_global_env cumul_gen (lift_typing P) Σ.1 ->
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ Γ wfΓ ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_fixpoint Σ.1 mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ Γ wfΓ ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_cofixpoint Σ.1 mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) p prim_ty cdecl,
        PΓ Σ Γ wfΓ ->
        primitive_constant Σ primInt = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants cdecl ->
        P Σ Γ (tInt p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) p prim_ty cdecl,
        PΓ Σ Γ wfΓ ->
        primitive_constant Σ primFloat = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants cdecl ->
        P Σ Γ (tFloat p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |- B : tSort s ->
        P Σ Γ B (tSort s) ->
        Σ ;;; Γ |- A <= B ->
        P Σ Γ t B) ->

       env_prop P PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_prop.
  intros XΓ.
  intros X X0 Xcast X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 Xint Xfloat X12 Σ wfΣ Γ wfΓ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
   otherwise it takes forever to execure the "pose", for some reason *)
  pose (@Fix_F ({ Σ : global_env_ext & { wfΣ : wf Σ & { Γ & { t & { T & Σ ;;; Γ |- t : T }}}}})) as p0.
  specialize (p0 (lexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
        (fun Σ => precompose lt (fun x => typing_size x.π2.π2.π2.π2)))) as p.
  set (foo := (Σ; wfΣ; Γ; t; _; H) : { Σ : global_env_ext & { wfΣ : wf Σ & { Γ & { t & { T & Σ ;;; Γ |- t : T }}}}}).
  change Σ with foo.π1.
  change Γ with foo.π2.π2.π1.
  change t with foo.π2.π2.π2.π1.
  change T with foo.π2.π2.π2.π2.π1.
  change H with foo.π2.π2.π2.π2.π2.
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_lexprod; intros; apply wf_precompose; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ wfΓ t T H.
  intros (Σ & wfΣ & Γ & t & t0 & H). simpl.
  intros IH. simpl in IH.
  split.
  destruct Σ as [Σ φ].
  red. cbn. do 2 red in wfΣ. cbn in wfΣ.
  destruct Σ as [univs Σ]; cbn in *.
  set (Σg:= {| universes := univs; declarations := Σ |}) in *.
  destruct wfΣ; split => //.
  rename o into ongu. rename o0 into o.
  destruct o. { constructor. }
  rename o0 into Xg. set (wfΣ := (ongu, o) : on_global_env cumul_gen (lift_typing typing) {| universes := univs; declarations := Σ |}).
  set (Σ':= {| universes := univs; declarations := Σ |}) in *.
  destruct Xg. rename udecl0 into udecl.
  rename on_global_decl_d0 into Xg.
  constructor; auto; try constructor; auto.
  - unshelve eset (IH' := IH ((Σ', udecl); wfΣ; []; tSort Universe.lProp; _; _)).
    shelve. simpl. apply type_Prop.
    forward IH'. constructor 1; cbn. lia.
    apply IH'; auto.
  - simpl. simpl in *.
    destruct d.
    + destruct c; simpl in *.
      destruct cst_body0; apply lift_typing_impl with (1 := Xg); intros ? Hs.
      all: specialize (IH ((Σ', udecl); wfΣ; _; _; _; Hs)).
      all: forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
      all: apply IH.
    + red in Xg.
      destruct Xg as [onI onP onnp]; constructor; eauto.
      * unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
        constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
        clear IH; rename IH' into IH.
        eapply Alli_impl; eauto. cbn in IH. clear onI onP onnp. intros n x Xg.
        refine {| ind_arity_eq := Xg.(ind_arity_eq);
                  ind_cunivs := Xg.(ind_cunivs) |}.
        -- apply onArity in Xg.
           apply lift_typing_impl with (1 := Xg); intros ? Hs.
           apply (IH (_; _; _; Hs)).
        -- pose proof Xg.(onConstructors) as Xg'.
           eapply All2_impl; eauto. intros.
           destruct X13 as [cass tyeq onctyp oncargs oncind].
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
        -- pose proof (onProjections Xg); auto.
        -- destruct Xg. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop; auto.
           destruct Universe.is_sprop; auto.
           split. apply ind_sorts0. destruct indices_matter; auto.
           eapply type_local_ctx_impl. eapply ind_sorts0. intros ??? HT.
           apply lift_typing_impl with (1 := HT); intros ? Hs.
           apply (IH (_; _; _; Hs)).
        -- apply (onIndices Xg).
      * red in onP |- *.
        apply All_local_env_impl with (1 := onP); intros ??? HT.
        apply lift_typing_impl with (1 := HT); intros ? Hs.
        apply (IH ((Σ', udecl); (wfΣ; _; _; _; Hs))).
        constructor 1. simpl. subst Σ' Σg; cbn; lia.

    + cut ((forall (m : module_implementation), on_module_impl cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) m
            -> on_module_impl cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) m)
        × (forall (p : structure_field), on_structure_field cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) p
            -> on_structure_field cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) p)
        × (forall (s : structure_body), on_structure_body cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) s
            -> on_structure_body cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) s)).
      * intros md_sf_sb. constructor; apply md_sf_sb; apply Xg.
      (** start of mutual induction *)
      * apply on_mi_sf_sb_mutrect; try now constructor.
        -- constructor. destruct c; simpl in *.
          destruct cst_body0; apply lift_typing_impl with (1 := o0); intros ? Hs.
          all: specialize (IH ((Σ', udecl); wfΣ; _; _; _; Hs)).
          all: forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
          all: apply IH.
        -- intros kn0 inds o0.
          apply on_sfmind with (kn:=kn0). destruct o0 as [onI onP onnp]; constructor; eauto.
          --- unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
            constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
            clear IH; rename IH' into IH.
            eapply Alli_impl; eauto. cbn in IH. clear onI onP onnp Xg. intros n x Xg.
            refine {| ind_arity_eq := Xg.(ind_arity_eq);
                      ind_cunivs := Xg.(ind_cunivs) |}.
            ** apply onArity in Xg.
              apply lift_typing_impl with (1 := Xg); intros ? Hs.
              apply (IH (_; _; _; Hs)).
            ** pose proof Xg.(onConstructors) as Xg'.
              eapply All2_impl; eauto. intros.
              destruct X13 as [cass tyeq onctyp oncargs oncind].
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
            ** pose proof (onProjections Xg); auto.
            ** destruct Xg. simpl. unfold check_ind_sorts in *.
              destruct Universe.is_prop; auto.
              destruct Universe.is_sprop; auto.
              split. apply ind_sorts0. destruct indices_matter; auto.
              eapply type_local_ctx_impl. eapply ind_sorts0. intros ??? HT.
              apply lift_typing_impl with (1 := HT); intros ? Hs.
              apply (IH (_; _; _; Hs)).
            ** apply (onIndices Xg).
          --- red in onP |- *.
            apply All_local_env_impl with (1 := onP); intros ??? HT.
            apply lift_typing_impl with (1 := HT); intros ? Hs.
            apply (IH ((Σ', udecl); (wfΣ; _; _; _; Hs))).
            constructor 1. simpl. subst Σ' Σg; cbn; lia.

    + cut ((forall (m : module_implementation), on_module_impl cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) m
            -> on_module_impl cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) m)
        × (forall (p : structure_field), on_structure_field cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) p
            -> on_structure_field cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) p)
        × (forall (s : structure_body), on_structure_body cumul_gen (lift_typing typing) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) s
            -> on_structure_body cumul_gen (lift_typing P) ({| universes := univs; declarations := Σ; retroknowledge := retroknowledge0 |}, Monomorphic_ctx) s)).
      * intros md_sf_sb. apply md_sf_sb; apply Xg.
      (** start of mutual induction *)
      * apply on_mi_sf_sb_mutrect; try now constructor.
        -- intros. apply on_sfconst.
          destruct c; simpl in *.
          destruct cst_body0; apply lift_typing_impl with (1 := o0); intros ? Hs.
          all: specialize (IH ((Σ', udecl); wfΣ; _; _; _; Hs)).
          all: forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
          all: apply IH.
        -- intros kn0 inds o0. apply on_sfmind with (kn:=kn0).
          destruct o0 as [onI onP onnp]; constructor; eauto.
          --- unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
            constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
            clear IH; rename IH' into IH.
            eapply Alli_impl; eauto. cbn in IH. clear onI onP onnp Xg. intros n x Xg.
            refine {| ind_arity_eq := Xg.(ind_arity_eq);
                      ind_cunivs := Xg.(ind_cunivs) |}.
            ** apply onArity in Xg.
              apply lift_typing_impl with (1 := Xg); intros ? Hs.
              apply (IH (_; _; _; Hs)).
            ** pose proof Xg.(onConstructors) as Xg'.
              eapply All2_impl; eauto. intros.
              destruct X13 as [cass tyeq onctyp oncargs oncind].
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
            ** pose proof (onProjections Xg); auto.
            ** destruct Xg. simpl. unfold check_ind_sorts in *.
              destruct Universe.is_prop; auto.
              destruct Universe.is_sprop; auto.
              split. apply ind_sorts0. destruct indices_matter; auto.
              eapply type_local_ctx_impl. eapply ind_sorts0. intros ??? HT.
              apply lift_typing_impl with (1 := HT); intros ? Hs.
              apply (IH (_; _; _; Hs)).
            ** apply (onIndices Xg).
          --- red in onP |- *.
            apply All_local_env_impl with (1 := onP); intros ??? HT.
            apply lift_typing_impl with (1 := HT); intros ? Hs.
            apply (IH ((Σ', udecl); (wfΣ; _; _; _; Hs))).
            constructor 1. simpl. subst Σ' Σg; cbn; lia.

  - assert (forall Γ t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ t T).
    { intros.
      specialize (IH (Σ; wfΣ; _; _; _; Hty)).
      simpl in IH.
      forward IH.
      constructor 2. simpl. apply H0.
      intuition. }

    rename X13 into X14.

    assert (forall Γ' t T (Hty : Σ ;;; Γ' |- t : T),
      typing_size Hty <= typing_size H ->
      PΓ Σ Γ' (typing_wf_local Hty)).
    { intros. apply XΓ; auto.
      clear -Pdecl wfΣ X14 H0.
      pose proof (typing_wf_local_size Hty).
      set (foo := typing_wf_local Hty) in *.
      clearbody foo. assert (All_local_env_size (@typing_size cf) Σ Γ' foo < typing_size H) by lia.
      clear H1 H0 Hty.
      revert foo H2.
      induction foo; simpl in *; try destruct t3 as [u Hu]; cbn in *; constructor.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ _ _ Hu). lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ _ _ t4). lia.
      - red. simpl. apply (X14 _ _ _ Hu). lia. }

    clear IH.
    assert (pΓ : PΓ Σ Γ (typing_wf_local H)).
    { apply (X13 _ _ _ H). lia. }
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

    -- clear X X0 Xcast X1 X2 X3 X5 X6 X7 X8 X9 X10 X11 X12 X13.
       eapply X4 with t_ty t0; eauto. clear X4.
       unshelve eapply X14; simpl; auto with arith.
       simpl in X14.
       assert(X: forall Γ0 : context,
                 wf_local Σ Γ0 ->
              forall (t1 T : term) (Hty : Σ;;; Γ0 |- t1 : T),
                typing_size Hty <
                S
                  ((typing_spine_size
                      (fun x (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                         typing_size x3) Σ Γ t_ty l t' t0)) ->
                on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ0 t1 T). {
       intros. unshelve eapply X14; eauto. lia. }
       clear X14. simpl in pΓ. clear n e H pΓ.
       induction t0; constructor.
       unshelve eapply X; clear X; simpl; auto with arith.
       unshelve eapply X; clear X; simpl; auto with arith.
       eapply IHt0; eauto. intros. eapply (X _ X0 _ _ Hty) ; eauto. simpl. lia.

    -- eapply X5; eauto.
       specialize (X14 [] _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. unfold All_local_env_size at 1, All_local_env_size_gen. lia. apply X14.

    -- eapply X6; eauto.
       specialize (X14 [] _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. unfold All_local_env_size at 1, All_local_env_size_gen. lia. apply X14.

    -- eapply X7; eauto.
       specialize (X14 [] _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. unfold All_local_env_size at 1, All_local_env_size_gen. lia. apply X14.

    -- simpl in pΓ.
       eapply (X8 Σ wfΣ Γ (typing_wf_local H0) ci); eauto.
       ++ eapply (X14 _ _ _ H0); eauto. simpl; auto with arith. lia.
       ++ clear -c1 X14.
        assert (forall (Γ' : context) (t T : term) (Hty : Σ;;; Γ' |- t : T),
           typing_size Hty <= ctx_inst_size _ (@typing_size _) c1 ->
         P Σ Γ' t T).
       { intros. eapply (X14 _ _ _ Hty). simpl.
         change (fun (x : global_env_ext) (x0 : context) (x1 x2 : term)
         (x3 : x;;; x0 |- x1 : x2) => typing_size x3) with (@typing_size cf).
         lia. }
       clear -X c1.
       revert c1 X.
       generalize (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl))).
       generalize (pparams p ++ indices).
       intros l c ctxi IH; induction ctxi; constructor; eauto.
       * split; tas. eapply (IH _ _ _ t0); simpl; auto. lia.
       * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.
       * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.

       ++ simpl in X13. simpl in pΓ. auto. eapply (X14 _ _ _ H); eauto. simpl; auto with arith.
       ++ simpl in *.
         eapply (X13 _ _ _ H); eauto. simpl. subst predctx. lia.
       ++ eapply (X14 _ _ _ H0); simpl. lia.
       ++ clear X13. revert a X14. clear. intros.
          subst ptm predctx.
          Opaque case_branch_type.
          simpl in X14.
          Transparent case_branch_type.
          induction a0; simpl in *.
          ** constructor.
          ** destruct r0 as [[? ?] ?]. constructor.
              --- intuition eauto.
                  +++ eapply (X14 _ _ _ t); eauto. clear -X14. simpl; auto with arith.
                      lia.
                  +++ eapply (X14 _ _ _ t0); eauto. simpl; auto with arith.
                      lia.
              --- apply IHa0. auto. intros.
                  eapply (X14 _ _ _ Hty). lia.

    -- eapply X9; eauto.
       specialize (X14 [] _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. pose (typing_size_pos H). unfold All_local_env_size at 1, All_local_env_size_gen. lia. apply X14.
       unshelve eapply X14; eauto.

    -- clear X X0 Xcast X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
       eapply X10; eauto; clear X10. simpl in *.
       * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S (all_size (fun x : def term =>
                   ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                    (fun (x : def term) '(existT s d) => typing_size d) a0) ->
                  on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ t T).
        intros; eauto. eapply (X14 _ _ _ Hty); eauto. unfold infer_sort. lia.
        clear X13 X14 a pΓ.
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
                        (all_size (fun x : def term => (Σ;;; Γ ,,, fix_context mfix |- dbody x : lift0 #|fix_context mfix| (dtype x))%type
                                                       )%type
                                   (fun (x : def term) p => typing_size p) a1) ->
                       on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ0 t T).
        {intros. eapply (X14 _ _ _ Hty); eauto. lia. }
        clear X14 X13.
        clear e decl i a0 i0 pΓ.
        remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.

        induction a1; econstructor; eauto.
        ++ split; auto.
          eapply (X _ (typing_wf_local p) _ _ p). simpl. lia.
        ++ eapply IHa1. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.

      -- clear X X0 Xcast X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12.
         eapply X11; eauto; clear X11. simpl in *.
         * assert(forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                      typing_size Hty <
                      S (all_size (fun x : def term =>
                      ∑ s : Universe.t, Σ;;; Γ |- dtype x : tSort s)
                       (fun (x : def term) '(existT s d) => typing_size d) a0) ->
                     on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ t T).
           intros; eauto. eapply (X14 _ _ _ Hty); eauto. unfold infer_sort. lia.
           clear X13 X14 a pΓ.
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
                          on_global_env cumul_gen (lift_typing P) Σ.1 * P Σ Γ0 t T).
           { intros. eapply (X14 _ _ _ Hty); eauto. lia. }
           clear X14 X13.
           clear e decl a0 i i0 pΓ.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.

           induction a1; econstructor; eauto.
           ++ split; auto.
             eapply (X _ (typing_wf_local p) _ _ p). simpl. lia.
           ++ eapply IHa1. intros.
             eapply (X _ X0 _ _ Hty). simpl; lia.
Qed.

(** * Lemmas about All_local_env *)

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

Arguments on_global_env {cf} Pcmp P !g.

Lemma lookup_on_global_env `{checker_flags} {Pcmp P} {Σ : global_env} {c decl} :
  on_global_env Pcmp P Σ ->
  lookup_env Σ c = Some decl ->
  { Σ' : global_env_ext & on_global_env Pcmp P Σ' × extends_decls Σ' Σ × on_global_decl Pcmp P Σ' c decl }.
Proof.
  unfold on_global_env.
  destruct Σ as [univs Σ retro]; cbn. intros [cu ond].
  induction ond; cbn in * => //.
  destruct o. rename udecl0 into udecl.
  case: eqb_specT => [-> [= <-]| ne].
  - exists ({| universes := univs; declarations := Σ; retroknowledge := retro |}, udecl).
    split; try constructor; tas.
    cbn. split => //=. now exists [(kn, d)].
  - intros hl.
    destruct (IHond hl) as [[Σ' udecl'] [ong [[equ ext extretro] ond']]].
    exists (Σ', udecl'). cbn in equ |- *. subst univs. split; cbn; auto; try apply ong.
    split; cbn; auto. split; cbn; auto.
    cbn in ext. destruct ext as [Σ'' ->]. cbn in *.
    now exists ((kn, d) :: Σ'').
Qed.

Lemma All_local_env_app_inv
      (P : context -> term -> typ_or_sort -> Type) l l' :
  All_local_env P (l ,,, l') ->
  All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l'.
Proof.
  induction l'; simpl; split; auto.
  - constructor.
  - intros. unfold app_context in X.
    inv X.
    + intuition auto.
    + auto. apply IHl'. auto.
  - inv X.
    + eapply localenv_cons_abs.
      * apply IHl'. apply X0.
      * apply X1.
    + eapply localenv_cons_def.
      * apply IHl'. apply X0.
      * apply X1.
      * eapply X2.
Qed.

Lemma All_local_env_lookup {P Γ n} {decl} :
  All_local_env P Γ ->
  nth_error Γ n = Some decl ->
  on_local_decl P (skipn (S n) Γ) decl.
Proof.
  induction 1 in n, decl |- *.
  - simpl. destruct n; simpl; congruence.
  - destruct n.
    + red. simpl. intro HH; apply some_inj in HH; rewrite <- HH; tas.
    + apply IHX.
  - destruct n.
    + red. simpl. intro HH; apply some_inj in HH; rewrite <- HH; tas.
    + apply IHX.
Qed.

Lemma All_local_env_app `{checker_flags} (P : context -> term -> typ_or_sort -> Type) l l' :
  All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l' ->
  All_local_env P (l ,,, l').
Proof.
  induction l'; simpl; auto. intuition.
  intuition. destruct a. destruct decl_body.
  inv b. econstructor; eauto. inv b; econstructor; eauto. Qed.

Lemma All_local_env_map `{checker_flags} (P : context -> term -> typ_or_sort -> Type) f l :
  (forall u, f (tSort u) = tSort u) ->
  All_local_env (fun Γ t T => P (map (map_decl f) Γ) (f t) (typ_or_sort_map f T)) l -> All_local_env P (map (map_decl f) l).
Proof.
  intros Hf. induction 1; econstructor; eauto.
Qed.

Definition property `{checker_flags} :=
  forall (Σ : global_env_ext) (Γ : context),
    wf_local Σ Γ -> forall t T : term, typing Σ Γ t T -> Type.

Definition lookup_wf_local {Γ P} (wfΓ : All_local_env P Γ) (n : nat) (isdecl : n < #|Γ|) :
  All_local_env P (skipn (S n) Γ).
Proof.
  induction wfΓ in n, isdecl |- *; simpl. constructor.
  cbn -[skipn] in *. destruct n.
  simpl. exact wfΓ.
  apply IHwfΓ. auto with arith.
  destruct n. exact wfΓ.
  apply IHwfΓ. auto with arith.
Defined.

Definition lookup_wf_local_decl {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
           {decl} (eq : nth_error Γ n = Some decl) :
  ∑ Pskip : All_local_env P (skipn (S n) Γ),
    on_local_decl P (skipn (S n) Γ) decl.
Proof.
  induction wfΓ in n, decl, eq |- *; simpl.
  - elimtype False. destruct n; inversion eq.
  - destruct n.
    + simpl. exists wfΓ. injection eq; intros <-. apply t0.
    + apply IHwfΓ. auto with arith.
  - destruct n.
    + exists wfΓ. injection eq; intros <-. apply t1.
    + apply IHwfΓ. apply eq.
Defined.

Definition on_wf_local_decl `{checker_flags} {Σ Γ}
           (P : forall Σ Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T -> Type)
           (wfΓ : wf_local Σ Γ) {d}
           (H : on_local_decl (lift_typing typing Σ) Γ d) :=
  match d as d' return (on_local_decl (lift_typing typing Σ) Γ d') -> Type with
  | {| decl_name := na; decl_body := Some b; decl_type := ty |}
    => fun H => P Σ Γ wfΓ b ty H
  | {| decl_name := na; decl_body := None; decl_type := ty |}
    => fun H => P Σ Γ wfΓ _ _ (projT2 H)
   end H.


Lemma nth_error_All_local_env_over `{checker_flags} {P Σ Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : wf_local Σ Γ} :
  All_local_env_over typing P Σ Γ wfΓ ->
  let Γ' := skipn (S n) Γ in
  let p := lookup_wf_local_decl wfΓ n eq in
  (All_local_env_over typing P Σ Γ' (projT1 p) * on_wf_local_decl P (projT1 p) (projT2 p))%type.
Proof.
  induction 1 in n, decl, eq |- *. simpl.
  - destruct n; simpl; elimtype False; discriminate eq.
  - destruct n; simpl.
    + cbn [skipn]. simpl in *. split; tas.
      destruct (f_equal (fun e => match e with
                               | Some c => c
                               | None => {| decl_name := na;
                                           decl_body := None; decl_type := t |}
                               end) eq).
      assumption.
    + apply IHX.
  - destruct n.
    + cbn [skipn]. simpl in *. split; tas.
      destruct (f_equal (fun e => match e with
                               | Some c => c
                               | None => {| decl_name := na;
                                           decl_body := Some b; decl_type := t |}
                               end) eq).
      assumption.
    + apply IHX.
Defined.

Definition wf_ext_wf `{checker_flags} Σ : wf_ext Σ -> wf Σ := fst.

#[global]
Hint Immediate wf_ext_wf : core.
