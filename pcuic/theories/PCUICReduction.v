(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICInduction PCUICCases.

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Inductive rtrans_clos {A} (R : A -> A -> Type) (x : A) : A -> Type :=
| rtrans_clos_refl : rtrans_clos R x x
| rtrans_clos_trans :
    forall y z,
      rtrans_clos R x y ->
      R y z ->
      rtrans_clos R x z.

Lemma All2_many_OnOne2 :
  forall A (R : A -> A -> Type) l l',
    All2 R l l' ->
    rtrans_clos (OnOne2 R) l l'.
Proof.
  intros A R l l' h.
  induction h.
  - constructor.
  - econstructor ; revgoals.
    + constructor. eassumption.
    + clear - IHh. rename IHh into h.
      induction h.
      * constructor.
      * econstructor.
        -- eassumption.
        -- econstructor. assumption.
Qed.

Definition tDummy := tVar String.EmptyString.
Definition dummy_branch : branch term := mkbranch [] tDummy.

Definition iota_red npar args bctx br :=
  subst (List.skipn npar args) 0 (expand_lets bctx (bbody br)).

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


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

Definition set_preturn (p : predicate term) (pret' : term) : predicate term :=
  {| pparams := p.(pparams);
      puinst := p.(puinst);
      pcontext := p.(pcontext);
      preturn := pret' |}.

Definition set_pparams (p : predicate term) (pars' : list term) : predicate term :=
  {| pparams := pars';
     puinst := p.(puinst);
     pcontext := p.(pcontext);
     preturn := p.(preturn) |}.
    
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
| red_iota ci mdecl idecl cdecl c u args p brs br
    (isdecl : declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl) :
    nth_error brs c = Some br ->
    wf_predicate mdecl idecl p -> 
    wf_branch cdecl br ->
    let brctx := case_branch_context ci.(ci_ind) mdecl p br.(bcontext) cdecl in
    #|skipn (ci_npar ci) args| = context_assumptions brctx ->
    red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args brctx br)

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
| red_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg


| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_param ci p params' c brs :
    OnOne2 (red1 Σ Γ) p.(pparams) params' ->
    red1 Σ Γ (tCase ci p c brs)
             (tCase ci (set_pparams p params') c brs)

| case_red_return ci mdecl idecl p preturn' c brs 
  (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl) :
  let pctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  wf_predicate mdecl idecl p -> 
  red1 Σ (Γ ,,, pctx) p.(preturn) preturn' ->
  red1 Σ Γ (tCase ci p c brs)
          (tCase ci (set_preturn p preturn') c brs)
    
| case_red_discr ci p c c' brs :
  red1 Σ Γ c c' -> 
  red1 Σ Γ (tCase ci p c brs) (tCase ci p c' brs)

| case_red_brs ci mdecl idecl p c brs brs' 
    (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl) :
    wf_predicate mdecl idecl p -> 
    wf_branches idecl brs ->  
    OnOne2All (fun cdecl br br' =>
      let brctx := case_branch_context ci.(ci_ind) mdecl p br.(bcontext) cdecl in
      on_Trel_eq (red1 Σ (Γ ,,, brctx)) bbody bcontext br br') idecl.(ind_ctors) brs brs' ->
    red1 Σ Γ (tCase ci p c brs) (tCase ci p c brs')

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

       (forall (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) mdecl idecl cdecl (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br
          (isdecl : declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl),
          nth_error brs c = Some br ->
          let brctx := case_branch_context ci.(ci_ind) mdecl p br.(bcontext) cdecl in
          wf_predicate mdecl idecl p ->
          wf_branch cdecl br ->
          #|skipn (ci_npar ci) args| = context_assumptions brctx ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) args brctx br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance_constr u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

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

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) mdecl idecl p preturn' c brs
          (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl),
          let pctx := case_predicate_context ci.(ci_ind) mdecl idecl p in       
          wf_predicate mdecl idecl p ->
          red1 Σ (Γ ,,, pctx) p.(preturn) preturn' ->
          P (Γ ,,, pctx) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->
       
       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci mdecl idecl p c brs brs' 
          (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl),
          wf_predicate mdecl idecl p ->
          wf_branches idecl brs ->
          OnOne2All (fun cdecl br br' =>
          let brctx := case_branch_context ci.(ci_ind) mdecl p br.(bcontext) cdecl in
          on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, brctx)) (P (Γ ,,, brctx))) 
            bbody bcontext br br') idecl.(ind_ctors) brs brs' ->
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
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros. rename X27 into Xlast. revert Γ t t0 Xlast.
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

  - revert params' o.
    generalize (pparams p).
    fix auxl 3.
    intros params params' [].
    + constructor. split; auto.
    + constructor. auto.
      
  - revert brs' o. clear w0.
    generalize (ind_ctors idecl).
    revert brs.
    fix auxl 4.
    intros i l l' Hl. destruct Hl.
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
Defined.

Hint Constructors red1 : pcuic.

Definition red Σ Γ := clos_refl_trans (red1 Σ Γ).

Lemma refl_red Σ Γ t : red Σ Γ t t.
Proof.
  reflexivity.
Defined.

Lemma trans_red Σ Γ M P N : red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.
Proof.
  etransitivity; tea. now constructor.
Defined.

Definition red_rect' Σ Γ M (P : term -> Type) :
  P M ->
  (forall P0 N, red Σ Γ M P0 -> P P0 -> red1 Σ Γ P0 N -> P N) ->
  forall (t : term) (r : red Σ Γ M t), P t.
Proof.
  intros X X0 t r. apply clos_rt_rtn1_iff in r.
  induction r; eauto.
  eapply X0; tea. now apply clos_rt_rtn1_iff.
Defined.

Definition red_rect_n1 := red_rect'.
Definition red_rect_1n Σ Γ (P : term -> term -> Type) :
  (forall x, P x x) ->
  (forall x y z, red1 Σ Γ x y -> red Σ Γ y z -> P y z -> P x z) ->
  forall x y, red Σ Γ x y -> P x y.
Proof.
  intros Hrefl Hstep x y r.
  apply clos_rt_rt1n_iff in r.
  induction r; eauto.
  eapply Hstep; eauto.
  now apply clos_rt_rt1n_iff.
Defined.

(** Simple lemmas about reduction *)

Lemma red1_red Σ Γ t u : red1 Σ Γ t u -> red Σ Γ t u.
Proof.
  econstructor; eauto.
Qed.

Hint Resolve red1_red refl_red : core pcuic.

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  etransitivity; tea. now constructor.
Qed.

Lemma red_trans Σ Γ t u v : red Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  etransitivity; tea.
Defined.


(** For this notion of reductions, theses are the atoms that reduce to themselves:

 *)

Definition atom t :=
  match t with
  | tRel _
  | tVar _
  | tSort _
  | tConst _ _
  | tInd _ _
  | tConstruct _ _ _ => true
  | _ => false
  end.

(** Generic method to show that a relation is closed by congruence using
    a notion of one-hole context. *)


Section ReductionCongruence.
  Context {Σ : global_env}.

  Inductive term_context :=
  | tCtxHole : term_context
  | tCtxEvar      : nat -> list_context -> term_context
  | tCtxProd_l      : aname -> term_context (* the type *) -> term -> term_context
  | tCtxProd_r      : aname -> term (* the type *) -> term_context -> term_context
  | tCtxLambda_l    : aname -> term_context (* the type *) -> term -> term_context
  | tCtxLambda_r    : aname -> term (* the type *) -> term_context -> term_context
  | tCtxLetIn_l     : aname -> term_context (* the term *) -> term (* the type *) ->
                    term -> term_context
  | tCtxLetIn_b     : aname -> term (* the term *) -> term_context (* the type *) ->
                    term -> term_context
  | tCtxLetIn_r     : aname -> term (* the term *) -> term (* the type *) ->
                    term_context -> term_context
  | tCtxApp_l       : term_context -> term -> term_context
  | tCtxApp_r       : term -> term_context -> term_context
  | tCtxCase_pars   : case_info -> list_context (* params *)
                      -> Instance.t -> list aname -> term -> (* predicate *)
                         term (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_pred   : case_info -> list term (* params *) -> Instance.t -> 
        list aname -> context -> (* context of predicate *)
        term_context (* type info *)
                         -> term (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_discr      : case_info -> predicate term (* type info *)
                 -> term_context (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_branch      : case_info -> predicate term (* type info *)
                           -> term (* discriminee *) -> branch_context (* branches *) -> term_context
  | tCtxProj      : projection -> term_context -> term_context
  (* | tCtxFix       : mfixpoint_context -> nat -> term_context harder because types of fixpoints are necessary *)
  (* | tCtxCoFix     : mfixpoint_context -> nat -> term_context *)

  with list_context :=
   | tCtxHead : term_context -> list term -> list_context
   | tCtxTail : term -> list_context -> list_context

  with branch_context :=
   | tCtxHead_nat : (list aname * context * term_context) -> list (branch term) -> branch_context
   | tCtxTail_nat : (branch term) -> branch_context -> branch_context.

  (* with mfixpoint_context := *)
  (*  | tCtxHead_mfix : def_context -> list (def term) -> mfixpoint_context *)
  (*  | tCtxTail_mfix : def term -> mfixpoint_context -> mfixpoint_context *)

  (* with def_context := *)
  (*  | tCtxType : name -> term_context -> term -> nat -> def_context *)
  (*  | tCtxDef : name -> term -> term_context -> nat -> def_context. *)

  Fixpoint branch_contexts (b : branch_context) : list (list aname) :=
    match b with
    | tCtxHead_nat (ctx, _, _) tl => ctx :: map bcontext tl
    | tCtxTail_nat b tl => bcontext b :: branch_contexts tl
    end.

  Section FillContext.
    Context (t : term).

    Equations fill_context (ctx : term_context) : term by struct ctx := {
    | tCtxHole => t;
    | tCtxEvar n l => tEvar n (fill_list_context l);
    | tCtxProd_l na ctx b => tProd na (fill_context ctx) b;
    | tCtxProd_r na ty ctx => tProd na ty (fill_context ctx);
    | tCtxLambda_l na ty b => tLambda na (fill_context ty) b;
    | tCtxLambda_r na ty b => tLambda na ty (fill_context b);
    | tCtxLetIn_l na b ty b' => tLetIn na (fill_context b) ty b';
    | tCtxLetIn_b na b ty b' => tLetIn na b (fill_context ty) b';
    | tCtxLetIn_r na b ty b' => tLetIn na b ty (fill_context b');
    | tCtxApp_l f a => tApp (fill_context f) a;
    | tCtxApp_r f a => tApp f (fill_context a);
    | tCtxCase_pars ci pars puinst pctx pret c brs =>
      tCase ci {| pparams := fill_list_context pars; 
                  puinst := puinst;
                  pcontext := pctx;
                  preturn := pret |} c brs ;
    | tCtxCase_pred ci pars puinst pctx pfullctx p c brs => 
      tCase ci {| pparams := pars;
                  puinst := puinst;
                  pcontext := pctx;
                  preturn := fill_context p |} c brs ;
    | tCtxCase_discr ci p c brs => tCase ci p (fill_context c) brs;
    | tCtxCase_branch ci p c brs => tCase ci p c (fill_branch_context brs);
    | tCtxProj p c => tProj p (fill_context c) }
    (* | tCtxFix mfix n => tFix (fill_mfix_context mfix) n; *)
    (* | tCtxCoFix mfix n => tCoFix (fill_mfix_context mfix) n } *)

    with fill_list_context (l : list_context) : list term by struct l :=
    { fill_list_context (tCtxHead ctx l) => (fill_context ctx) :: l;
      fill_list_context (tCtxTail hd ctx) => hd :: fill_list_context ctx }

    with fill_branch_context (l : branch_context) : list (branch term) by struct l :=
    { fill_branch_context (tCtxHead_nat (bctx, fullctx, ctx) l) => 
      {| bcontext := bctx;
         bbody := fill_context ctx |} :: l;
      fill_branch_context (tCtxTail_nat hd ctx) => hd :: fill_branch_context ctx }.

    (* with fill_mfix_context (l : mfixpoint_context) : mfixpoint term by struct l := *)
    (* { fill_mfix_context (tCtxHead_mfix (tCtxType na ty def rarg) l) => *)
    (*     {| dname := na; dtype := fill_context ty; dbody := def; rarg := rarg |} :: l; *)
    (*   fill_mfix_context (tCtxHead_mfix (tCtxDef na ty def rarg) l) => *)
    (*     {| dname := na; dtype := ty; dbody := fill_context def; rarg := rarg |} :: l; *)
    (*   fill_mfix_context (tCtxTail_mfix hd ctx) => hd :: fill_mfix_context ctx }. *)
    Global Transparent fill_context fill_list_context fill_branch_context.

    Equations hole_context (ctx : term_context) (Γ : context) : context by struct ctx := {
    | tCtxHole | Γ => Γ;
    | tCtxEvar n l | Γ => hole_list_context l Γ;
    | tCtxProd_l na ctx b | Γ => hole_context ctx Γ;
    | tCtxProd_r na ty ctx | Γ => hole_context ctx (Γ ,, vass na ty);
    | tCtxLambda_l na ty b | Γ => hole_context ty Γ;
    | tCtxLambda_r na ty b | Γ => hole_context b (Γ ,, vass na ty);
    | tCtxLetIn_l na b ty b' | Γ => hole_context b Γ;
    | tCtxLetIn_b na b ty b' | Γ => hole_context ty Γ;
    | tCtxLetIn_r na b ty b' | Γ => hole_context b' (Γ ,, vdef na b ty);
    | tCtxApp_l f a | Γ => hole_context f Γ;
    | tCtxApp_r f a | Γ => hole_context a Γ;
    | tCtxCase_pars ci params puinst pctx pret c brs | Γ => hole_list_context params Γ;
    | tCtxCase_pred ci params puinst _ pctx pret c brs | Γ => hole_context pret (Γ ,,, pctx);
    | tCtxCase_discr ci p c brs | Γ => hole_context c Γ;
    | tCtxCase_branch ci p c brs | Γ => hole_branch_context brs Γ;
    | tCtxProj p c | Γ => hole_context c Γ }
    (* | tCtxFix mfix n | Γ => hole_mfix_context mfix Γ ; *)
    (* | tCtxCoFix mfix n | Γ => hole_mfix_context mfix Γ } *)

    with hole_list_context (l : list_context) (Γ : context) : context by struct l :=
    { hole_list_context (tCtxHead ctx l) Γ => hole_context ctx Γ;
      hole_list_context (tCtxTail hd ctx) Γ => hole_list_context ctx Γ }

    with hole_branch_context (l : branch_context) (Γ : context) : context by struct l :=
    { hole_branch_context (tCtxHead_nat (bctx, bfullctx, ctx) l) Γ => hole_context ctx (Γ ,,, bfullctx);
      hole_branch_context (tCtxTail_nat hd ctx) Γ => hole_branch_context ctx Γ }.

    (* with hole_mfix_context (l : mfixpoint_context) (Γ : context) : context by struct l := *)
    (* { hole_mfix_context (tCtxHead_mfix (tCtxType na ctx def rarg) _) Γ => hole_context ctx Γ; *)
    (*   hole_mfix_context (tCtxHead_mfix (tCtxDef na ty ctx rarg) _) Γ => hole_context ctx; *)
    (*   hole_mfix_context (tCtxTail_mfix hd ctx) Γ => hole_mfix_context ctx tys Γ }. *)
    Global Transparent hole_context hole_list_context hole_branch_context.

  End FillContext.

  Universe wf_context_i.
  Equations(noeqns noind) wf_context (ctx : term_context) : Type@{wf_context_i} by struct ctx := {
    | tCtxHole => True;
    | tCtxEvar n l => wf_list_context l;
    | tCtxProd_l na ctx b => (wf_context ctx);
    | tCtxProd_r na ty ctx => (wf_context ctx);
    | tCtxLambda_l na ty b => (wf_context ty);
    | tCtxLambda_r na ty b => (wf_context b);
    | tCtxLetIn_l na b ty b' => (wf_context b);
    | tCtxLetIn_b na b ty b' => (wf_context ty);
    | tCtxLetIn_r na b ty b' => (wf_context b');
    | tCtxApp_l f a => (wf_context f);
    | tCtxApp_r f a => (wf_context a);
    | tCtxCase_pars ci pars puinst pctx pret c brs =>
        wf_list_context pars;
    | tCtxCase_pred ci pars puinst names pctx p c brs => 
      (∑ mdecl idecl, 
        declared_inductive Σ ci.(ci_ind) mdecl idecl *
        (pctx = case_predicate_context_gen ci.(ci_ind) mdecl idecl pars puinst names) * 
        wf_predicate_gen mdecl idecl pars names) *
        wf_context p;
    | tCtxCase_discr ci p c brs =>
        wf_context c;
    | tCtxCase_branch ci p c brs => 
      (∑ mdecl idecl,
        declared_inductive Σ ci.(ci_ind) mdecl idecl *
        wf_predicate mdecl idecl p *
        wf_branch_context (ci.(ci_ind), mdecl, idecl, p) idecl.(ind_ctors) brs);
    | tCtxProj p c => (wf_context c) }
    (* | tCtxFix mfix n => tFix (fill_mfix_context mfix) n; *)
    (* | tCtxCoFix mfix n => tCoFix (fill_mfix_context mfix) n } *)

    with wf_list_context (l : list_context) : Type@{wf_context_i} by struct l :=
    { | (tCtxHead ctx l) => (wf_context ctx);
      | (tCtxTail hd ctx) => wf_list_context ctx }

    with wf_branch_context (info : inductive * mutual_inductive_body * one_inductive_body * predicate term) (brsctx : list constructor_body) (l : branch_context) : Type@{wf_context_i} by struct l :=
    { | p | [] | tCtxHead_nat _ _ => False ;
      | p | [] | tCtxTail_nat _ _ => False ;
      | (ind, mdecl, idecl, p) | cdecl :: cdecls | (tCtxHead_nat (bctx, bfullctx, ctx) l) => 
        Forall2 wf_branch cdecls l *
        wf_predicate mdecl idecl p *
        (case_branch_context ind mdecl p bctx cdecl = bfullctx) *
        wf_branch_gen cdecl bctx *
        wf_context ctx;
      | p | cdecl :: cdecls | (tCtxTail_nat hd ctx) =>
        wf_branch cdecl hd * wf_branch_context p cdecls ctx }.

  Inductive contextual_closure (red : forall Γ, term -> term -> Type) : context -> term -> term -> Type@{wf_context_i} :=
  | ctxclos_atom Γ t : atom t -> contextual_closure red Γ t t
  | ctxclos_ctx Γ (ctx : term_context) (u u' : term) :
      wf_context ctx ->
      red (hole_context ctx Γ) u u' -> contextual_closure red Γ (fill_context u ctx) (fill_context u' ctx).

  Lemma red_contextual_closure Γ t u : red Σ Γ t u -> contextual_closure (red Σ) Γ t u.
  Proof.
    intros Hred.
    apply (ctxclos_ctx (red Σ) Γ tCtxHole t u I Hred).
  Qed.

  Arguments fill_list_context : simpl never.

  Lemma wf_branch_context_branches p ctors x b : 
    wf_branch_context p ctors b ->
    Forall2 wf_branch ctors (fill_branch_context x b).
  Proof.
    induction ctors in b |- *; destruct b; simpl; auto;
     destruct p as [[[? ?] ?] ?].
    - destruct p0 as [[? ?] ?].
      simpl. intros [[[[] ?] ?] ?].
      constructor; auto.
    - intros []. constructor; auto.
  Qed.

  Lemma contextual_closure_red Γ t u : 
    contextual_closure (red Σ) Γ t u -> red Σ Γ t u.
  Proof.
    induction 1; trea.
    apply clos_rt_rt1n in r. induction r; trea.
    apply clos_rt_rt1n_iff in r0.
    etransitivity; tea. constructor.
    clear -r w.
    set (P := fun ctx t => 
      wf_context ctx ->
      forall Γ y, red1 Σ (hole_context ctx Γ) x y ->
                  red1 Σ Γ t (fill_context y ctx)).
    set (P' := fun l fill_l =>
      wf_list_context l ->
      forall Γ y,
                   red1 Σ (hole_list_context l Γ) x y ->
                   OnOne2 (red1 Σ Γ) fill_l (fill_list_context y l)).
    set (P'' := fun l fill_l =>
      forall p brctx, wf_branch_context p brctx l ->
                 forall Γ y,
                   wf_predicate p.1.1.2 p.1.2 p.2 ->
                   red1 Σ (hole_branch_context l Γ) x y ->
                   OnOne2All (fun cdecl br br' => 
                    let brctx := case_branch_context p.1.1.1 p.1.1.2 p.2 br.(bcontext) cdecl in
                    on_Trel_eq (red1 Σ (Γ ,,, brctx)) bbody bcontext br br')
                    brctx fill_l (fill_branch_context y l)).
    (* set (Pfix := fun l fixc fill_l => *)
    (*              forall Γ y, *)
    (*                red1 Σ (hole_mfix_context l fixc Γ) x y -> *)
    (*                (OnOne2 (on_Trel_eq (red1 (fst Σ) Γ) dtype (fun d => (dname d, dbody d, rarg d))) *)
    (*                       fill_l (fill_mfix_context y l fixc)) + *)
    (*                (OnOne2 (on_Trel_eq (red1 (fst Σ) (Γ ,,, fix_context fill_l)) dbody (fun d => (dname d, dtype d, rarg d))) *)
    (*                       fill_l (fill_mfix_context y l fixc))). *)
    revert w Γ y r.
    eapply (fill_context_elim x P P' P''); subst P P' P''; cbv beta;
      intros **; simp fill_context; cbn in *; auto; try solve [constructor; eauto].
    - destruct X0 as [[mdecl [idecl [[decli ->] wfp]]] wf].
      specialize (X wf (Γ ,,, _) _ X1).
      econstructor; eauto.
    - simp wf_context in X0.
      destruct X0 as [mdecl [idecl [[decli wfp] wf]]].
      specialize (X _ _ wf _ _ wfp X1).
      econstructor. all:eauto.
      now apply (wf_branch_context_branches _ _ x) in wf.
    - destruct p as [[[ind mdecl] idecl] p].
      destruct brctx; simpl in X0 => //.
      destruct X0 as [[[[eql wfp] <-] wfb] wf].
      specialize (X wf _ _ X1).
      constructor; intuition auto.
      red in wfb. now rewrite -(Forall2_length eql).
    - destruct p as [[[ind mdecl] idecl] p].
      destruct brctx; simpl in X0 => //.
      destruct X0 as [wfb wfbc].
      specialize (X _ _ wfbc _ _ H X1).
      constructor. auto.
  Qed.

  Theorem red_contextual_closure_equiv Γ t u : red Σ Γ t u <~> contextual_closure (red Σ) Γ t u.
  Proof.
    split.
    - apply red_contextual_closure.
    - apply contextual_closure_red.
  Qed.

  Lemma red_ctx {Γ} {M M'} ctx :
    wf_context ctx ->
    red Σ (hole_context ctx Γ) M M' ->
    red Σ Γ (fill_context M ctx) (fill_context M' ctx).
  Proof.
    intros.
    apply red_contextual_closure_equiv.
    now apply (ctxclos_ctx _ _ ctx).
  Qed.

  Section Congruences.

    Notation red1_one_term Γ :=
      (@OnOne2 (term × _) (Trel_conj (on_Trel (red1 Σ Γ) fst) (on_Trel eq snd))).
    Notation red_one_term Γ := 
      (@OnOne2 (term × _) (Trel_conj (on_Trel (red Σ Γ) fst) (on_Trel eq snd))).
    Notation red1_one_branch Γ ind mdecl p := 
      (@OnOne2All (term × _) _ (fun cdecl br br' =>
        let ctx := case_branch_context ind mdecl p (snd br) cdecl in
        Trel_conj (on_Trel (red1 Σ (Γ ,,, ctx)) fst) (on_Trel eq snd) br br')).
    Notation red_one_branch Γ ind mdecl p := 
      (@OnOne2All (term × _) _ (fun cdecl br br' => 
        let ctx := case_branch_context ind mdecl p (snd br) cdecl in
        Trel_conj (on_Trel (red Σ (Γ ,,, ctx)) fst) (on_Trel eq snd) br br')).

    Inductive redl {A} {P} l : list (term × A) -> Type :=
    | refl_redl : redl l l
    | trans_redl :
        forall l1 l2,
          redl l l1 ->
          P l1 l2 ->
          redl l l2.
    Derive Signature for redl.

    Lemma redl_preserve {A P} (l l' : list (term × A)) : 
      (forall (x y : list (term × A)), P x y -> map snd x = map snd y) ->
      @redl _ P l l' -> map snd l = map snd l'.
    Proof.
      intros HP. induction 1; auto.
      rewrite IHX. now apply HP.
    Qed.

    Definition redl_term {A} Γ := @redl A (red1_one_term Γ).
    Definition redl_branch Γ ind mdecl p l := @redl _ (red1_one_branch Γ ind mdecl p l).
      
    Lemma OnOne2_red_redl :
      forall Γ A (l l' : list (term × A)),
        red_one_term Γ l l' ->
        redl_term Γ l l'.
    Proof.
      intros Γ A l l' h.
      induction h.
      - destruct p as [p1 p2].
        unfold on_Trel in p1, p2.
        destruct hd as [t a], hd' as [t' a']. simpl in *. subst.
        induction p1 using red_rect'.
        + constructor.
        + econstructor.
          * eapply IHp1.
          * constructor. split ; eauto.
            reflexivity.
      - clear h. rename IHh into h.
        induction h.
        + constructor.
        + econstructor ; eauto. constructor ; eauto.
    Qed.

    Lemma OnOne2All_red_redl :
      forall Γ ind mdecl p lΔ (l l' : list (term × list aname)),
        red_one_branch Γ ind mdecl p lΔ l l' ->
        redl_branch Γ ind mdecl p lΔ l l'.
    Proof.
      intros Γ ind mdecl p lΔ l l' h.
      induction h.
      - destruct p0 as [p1 p2].
        unfold on_Trel in p1, p2.
        destruct hd as [t a], hd' as [t' a']. simpl in *; subst.
        induction p1 using red_rect'.
        + constructor.
        + econstructor.
          * eapply IHp1.
          * constructor; intuition eauto.
            depelim IHp1.
            ++ split; auto. split; auto.
            ++ split; auto. split; auto.
      - clear h. rename IHh into h.
        induction h.
        + constructor.
        + econstructor ; eauto. constructor ; eauto.
    Qed.

    Lemma OnOne2_on_Trel_eq_unit :
      forall A (R : A -> A -> Type) l l',
        OnOne2 R l l' ->
        OnOne2 (on_Trel_eq R (fun x => x) (fun x => tt)) l l'.
    Proof.
      intros A R l l' h.
      eapply OnOne2_impl ; eauto.
    Qed.

    Lemma OnOne2_on_Trel_eq_red_redl :
      forall Γ A B (f : A -> term) (g : A -> B) l l',
        OnOne2 (on_Trel_eq (red Σ Γ) f g) l l' ->
        redl_term Γ (map (fun x => (f x, g x)) l) (map (fun x => (f x, g x)) l').
    Proof.
      intros Γ A B f g l l' h.
      eapply OnOne2_red_redl.
      eapply OnOne2_map. eapply OnOne2_impl ; eauto.
    Qed.

    Lemma OnOne2All_on_Trel_eq_red_redl :
      forall Γ ind mdecl p (lΔ : list constructor_body) l l',
        OnOne2All (fun cdecl br br' =>
        let ctx := case_branch_context ind mdecl p (bcontext br) cdecl in
        on_Trel_eq (red Σ (Γ ,,, ctx)) bbody bcontext br br') lΔ l l' ->
        redl_branch Γ ind mdecl p lΔ (map (fun x => (bbody x, bcontext x)) l) 
          (map (fun x => (bbody x, bcontext x)) l').
    Proof.
      intros Γ ind mdecl p lΔ l l' h.
      eapply OnOne2All_red_redl.
      eapply OnOne2All_map. eapply OnOne2All_impl ; eauto.
    Qed.

    Lemma OnOne2_prod_inv :
      forall A (P : A -> A -> Type) Q l l',
        OnOne2 (Trel_conj P Q) l l' ->
        OnOne2 P l l' × OnOne2 Q l l'.
    Proof.
      intros A P Q l l' h.
      induction h.
      - destruct p.
        split ; constructor ; auto.
      - destruct IHh.
        split ; constructor ; auto.
    Qed.

    Lemma OnOne2_prod_inv_refl_r :
      forall A (P Q : A -> A -> Type) l l',
        (forall x, Q x x) ->
        OnOne2 (Trel_conj P Q) l l' ->
        OnOne2 P l l' × All2 Q l l'.
    Proof.
      intros A P Q l l' hQ h.
      induction h.
      - destruct p. split.
        + constructor. assumption.
        + constructor.
          * assumption.
          * eapply All_All2.
            -- instantiate (1 := fun x => True). eapply Forall_All.
               eapply Forall_True. intro. auto.
            -- intros x _. eapply hQ.
      - destruct IHh. split.
        + constructor. assumption.
        + constructor ; eauto.
    Qed.

    Lemma All2_eq :
      forall A (l l' : list A),
        All2 eq l l' ->
        l = l'.
    Proof.
      intros A l l' h.
      induction h ; eauto. subst. reflexivity.
    Qed.

    Lemma list_split_eq :
      forall A B (l l' : list (A × B)),
        map fst l = map fst l' ->
        map snd l = map snd l' ->
        l = l'.
    Proof.
      intros A B l l' e1 e2.
      induction l in l', e1, e2 |- *.
      - destruct l' ; try discriminate. reflexivity.
      - destruct l' ; try discriminate.
        simpl in *. inversion e1. inversion e2.
        f_equal ; eauto.
        destruct a, p. simpl in *. subst. reflexivity.
    Qed.

    Notation decomp_branch := (fun x : branch term => (bbody x, bcontext x)).
    Notation recomp_branch := (fun x : term * list aname => {| bbody := x.1; bcontext := x.2 |}).

    Lemma list_map_swap_eq :
      forall l l',
        map decomp_branch l = map decomp_branch l' ->
        l = l'.
    Proof.
      intros l l' h.
      induction l in l', h |- *.
      - destruct l' ; try discriminate. reflexivity.
      - destruct l' ; try discriminate.
        cbn in h. inversion h.
        f_equal ; eauto.
        destruct a, b. cbn in *. subst. reflexivity.
    Qed.

    Lemma map_recomp_decomp :
      forall l, l = map decomp_branch (map recomp_branch l).
    Proof.
      induction l.
      - reflexivity.
      - cbn. destruct a. rewrite <- IHl. reflexivity.
    Qed.

    Lemma map_decomp_recomp :
      forall l, l = map recomp_branch (map decomp_branch l).
    Proof.
      induction l.
      - reflexivity.
      - cbn. destruct a. rewrite <- IHl. reflexivity.
    Qed.

    Lemma map_inj :
      forall A B (f : A -> B) l l',
        (forall x y, f x = f y -> x = y) ->
        map f l = map f l' ->
        l = l'.
    Proof.
      intros A B f l l' h e.
      induction l in l', e |- *.
      - destruct l' ; try discriminate. reflexivity.
      - destruct l' ; try discriminate. inversion e.
        f_equal ; eauto.
    Qed.

    Context {Γ : context}.

    Lemma red_abs na M M' N N' :
      red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N'
      -> red Σ Γ (tLambda na M N) (tLambda na M' N').
    Proof.
      intros. transitivity (tLambda na M' N).
      - now apply (red_ctx (tCtxLambda_l _ tCtxHole _)).
      - now eapply (red_ctx (tCtxLambda_r _ _ tCtxHole)).
    Qed.

    Lemma red_app_r u v1 v2 :
        red Σ Γ v1 v2 ->
        red Σ Γ (tApp u v1) (tApp u v2).
    Proof.
      intro h. rst_induction h; eauto with pcuic.
    Qed.

    Lemma red_app M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      red Σ Γ N0 N1 ->
      red Σ Γ (tApp M0 N0) (tApp M1 N1).
    Proof.
      intros; transitivity (tApp M1 N0).
      - now apply (red_ctx (tCtxApp_l tCtxHole _)).
      - now eapply (red_ctx (tCtxApp_r _ tCtxHole)).
    Qed.

    Fixpoint mkApps_context l :=
      match l with
      | [] => tCtxHole
      | hd :: tl => tCtxApp_l (mkApps_context tl) hd
      end.

    Lemma mkApps_context_hole l Γ' : hole_context (mkApps_context (List.rev l)) Γ' = Γ'.
    Proof. generalize (List.rev l) as l'; induction l'; simpl; auto. Qed.

    Lemma fill_mkApps_context M l : fill_context M (mkApps_context (List.rev l)) = mkApps M l.
    Proof.
      rewrite -{2}(rev_involutive l).
      generalize (List.rev l) as l'; induction l'; simpl; auto.
      rewrite <- mkApps_nested. now rewrite <- IHl'.
    Qed.

    Lemma red1_mkApps_f :
      forall t u l,
        red1 Σ Γ t u ->
        red1 Σ Γ (mkApps t l) (mkApps u l).
    Proof.
      intros t u l h.
      revert t u h.
      induction l ; intros t u h.
      - assumption.
      - cbn. apply IHl. constructor. assumption.
    Qed.

    Corollary red_mkApps_f :
      forall t u l,
        red Σ Γ t u ->
        red Σ Γ (mkApps t l) (mkApps u l).
    Proof.
      intros t u π h. rst_induction h; eauto with pcuic.
      eapply red1_mkApps_f. assumption.
    Qed.

    Lemma red_mkApps M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      All2 (red Σ Γ) N0 N1 ->
      red Σ Γ (mkApps M0 N0) (mkApps M1 N1).
    Proof.
      intros.
      induction X0 in M0, M1, X |- *. 1: auto.
      simpl. eapply IHX0. now eapply red_app.
    Qed.

    Lemma red_letin na d0 d1 t0 t1 b0 b1 :
      red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d1 t1) b0 b1 ->
      red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
    Proof.
      intros; transitivity (tLetIn na d1 t0 b0).
      - now apply (red_ctx (tCtxLetIn_l _ tCtxHole _ _)).
      - transitivity (tLetIn na d1 t1 b0).
        + now eapply (red_ctx (tCtxLetIn_b _ _ tCtxHole _)).
        + now eapply (red_ctx (tCtxLetIn_r _ _ _ tCtxHole)).
    Qed.
        
    Lemma red_one_param :
      forall ci p c brs pars',
        OnOne2 (red Σ Γ) p.(pparams) pars' ->
        red Σ Γ (tCase ci p c brs) (tCase ci (set_pparams p pars') c brs).
    Proof.
      intros ci p c l l' h.
      apply OnOne2_on_Trel_eq_unit in h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (p.(pparams) = l').
        { eapply map_inj ; eauto.
          intros y z e. cbn in e. inversion e. eauto.
        } subst.
        destruct p; reflexivity.
      - set (f := fun x : term => (x, tt)) in *.
        set (g := (fun '(x, _) => x) : term × unit -> term).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a, u. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh; tas. symmetry. apply el.
        + change (set_pparams p l') with (set_pparams (set_pparams p (map g l1)) l').
          econstructor. rewrite (el' l').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? []] [? []] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *.
          unfold on_Trel. cbn. assumption.
    Qed.

    Lemma red_case_pars :
      forall ci p c brs pars',
        All2 (red Σ Γ) p.(pparams) pars' ->
        red Σ Γ (tCase ci p c brs) (tCase ci (set_pparams p pars') c brs).
    Proof.
      intros ci p c brs pars' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - destruct p; reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + assert (set_pparams p z = set_pparams (set_pparams p y) z) as ->.
          { now destruct p. }
          eapply red_one_param; eassumption.
    Qed.

    Coercion ci_ind : case_info >-> inductive.

    Lemma red_case_p :
      forall ci mdecl idecl p c brs pret',
        declared_inductive Σ ci.(ci_ind) mdecl idecl ->
        wf_predicate mdecl idecl p -> 
        red Σ (Γ ,,, case_predicate_context ci mdecl idecl p) p.(preturn) pret' ->
        red Σ Γ (tCase ci p c brs) 
          (tCase ci (set_preturn p pret') c brs).
    Proof.
      intros ci mdecl idecl p c brs p' decli wfp h.
      unshelve epose proof 
        (red_ctx (tCtxCase_pred ci p.(pparams) p.(puinst) p.(pcontext) _ tCtxHole c brs) _ h).
      { simpl. split; auto. exists mdecl, idecl; intuition auto. }
      simp fill_context in X.
      destruct p; auto.
    Qed.

    Lemma red_case_c :
      forall ci p c brs c',
        red Σ Γ c c' ->
        red Σ Γ (tCase ci p c brs) (tCase ci p c' brs).
    Proof.
      intros ci p c brs c' h.
      rst_induction h; eauto with pcuic.
    Qed.
    
    Lemma map_bcontext_redl {l l' : list (term * list aname)} {ind mdecl p brs} :  
      @redl _ (red1_one_branch Γ ind mdecl p brs) l l' -> map snd l = map snd l'.
    Proof.
      induction 1; auto. rewrite IHX.
      clear -p0. 
      induction p0; simpl. 
      - destruct p0 as [? ?]. congruence.
      - now f_equal.
    Qed.

    Lemma wf_branches_to_gen idecl brs :
      wf_branches idecl brs <->
      wf_branches_gen idecl.(ind_ctors) (map bcontext brs).
    Proof.
      split.
      - induction 1; constructor; auto.
      - unfold wf_branches_gen.
        rewrite -(map_id (ind_ctors idecl)).
        intros H; eapply Forall2_map_inv in H. red.
        solve_all.
    Qed.

    Lemma red_case_one_brs :
      forall (ci : case_info) mdecl idecl p c brs brs',
        declared_inductive Σ ci mdecl idecl ->
        wf_predicate mdecl idecl p ->
        wf_branches idecl brs ->
        OnOne2All (fun cdecl br br' => 
          let brctx := case_branch_context ci.(ci_ind) mdecl p br.(bcontext) cdecl in
          on_Trel_eq (red Σ (Γ ,,, brctx)) bbody bcontext br br') 
          idecl.(ind_ctors) brs brs' ->
        red Σ Γ (tCase ci p c brs) (tCase ci p c brs').
    Proof.
      intros ci mdecl idecl p c brs brs' isdecl wfp wfbrs h.
      apply OnOne2All_on_Trel_eq_red_redl in h.
      dependent induction h.
      - apply list_map_swap_eq in H. now subst.
      - etransitivity.
        + eapply IHh; eauto. rewrite <- map_recomp_decomp. reflexivity.
        + constructor. econstructor; eauto.
          * assert (map snd l1 = map bcontext brs).
            { apply redl_preserve in h. 
              * rewrite -h map_map_compose. now simpl.
              * clear; intros.
                induction X; simpl; auto. 
                + now destruct p0 as [_ ->].
                + now rewrite IHX. }
            apply wf_branches_to_gen in wfbrs.
            rewrite -H in wfbrs.
            apply wf_branches_to_gen.
            now rewrite map_map_compose.
          * rewrite (map_decomp_recomp brs').
            eapply OnOne2All_map.
            eapply OnOne2All_impl ; eauto.
    Qed.

    Lemma All3_length {A B C} {R : A -> B -> C -> Type} l l' l'' :
      All3 R l l' l'' -> #|l| = #|l'| /\ #|l'| = #|l''|.
    Proof. induction 1; simpl; intuition auto. Qed.

    Lemma All3_many_OnOne2All :
      forall B A (R : B -> A -> A -> Type) lΔ l l',
        All3 R lΔ l l' ->
        rtrans_clos (OnOne2All R lΔ) l l'.
    Proof.
      intros B A R lΔ l l' h.
      induction h.
      - constructor.
      - econstructor ; revgoals.
        + constructor; [eassumption|].
          eapply All3_length in h; intuition eauto. now transitivity #|l'|.
        + clear - IHh. rename IHh into h.
          induction h.
          * constructor.
          * econstructor.
            -- eassumption.
            -- econstructor. assumption.
    Qed.
    (* Lemma All2_many_OnOne2All :
      forall B A (R : B -> A -> A -> Type) lΔ l l',
        All2 (R  l l' ->
        rtrans_clos (OnOne2All R lΔ) l l'.
    Proof.
      intros A R l l' h.
      induction h.
      - constructor.
      - econstructor ; revgoals.
        + constructor. eassumption.
        + clear - IHh. rename IHh into h.
          induction h.
          * constructor.
          * econstructor.
            -- eassumption.
            -- econstructor. assumption.
    Qed. *)

    Definition red_brs Γ ind mdecl idecl p brs brs' :=
      All3 (fun cdecl br br' => 
      let ctx := case_branch_context ind mdecl p br.(bcontext) cdecl in
      on_Trel_eq (red Σ (Γ ,,, ctx)) bbody bcontext br br')
      idecl.(ind_ctors) brs brs'.

    Lemma red_case_brs_wf :
      forall ci mdecl idecl p c brs brs',
        declared_inductive Σ ci.(ci_ind) mdecl idecl ->
        wf_predicate mdecl idecl p ->
        wf_branches idecl brs ->
        red_brs Γ ci.(ci_ind) mdecl idecl p brs brs' ->
        red Σ Γ (tCase ci p c brs) (tCase ci p c brs') * wf_branches idecl brs'.
    Proof.
      intros ci mdecl idecl p c brs brs' isdecl wfp wfbrs h.
      apply All3_many_OnOne2All in h.
      induction h; split; trea.
      + eapply red_trans.
        * eapply IHh.
        * eapply red_case_one_brs; eauto. eapply IHh.
      + destruct IHh.
        clear -r w.
        unfold wf_branches in *.
        eapply wf_branches_to_gen. apply wf_branches_to_gen in w.
        induction r.
        - simpl in *. destruct p0 as [_ bctx].
          now rewrite bctx in w.
        - simpl. depelim w; constructor; auto.
          apply IHr. apply w.
    Qed.

    Lemma red_case_brs :
      forall ci mdecl idecl p c brs brs',
      declared_inductive Σ ci.(ci_ind) mdecl idecl ->
      wf_predicate mdecl idecl p ->
      wf_branches idecl brs ->
      red_brs Γ ci.(ci_ind) mdecl idecl p brs brs' ->
      red Σ Γ (tCase ci p c brs) (tCase ci p c brs').
    Proof.
      intros. now eapply red_case_brs_wf.
    Qed.


    Lemma All2_ind_OnOne2 {A} P (l l' : list A) :
      All2 P l l' ->
      forall x a a', nth_error l x = Some a ->
                     nth_error l' x = Some a' ->
                     OnOne2 P (firstn x l ++ [a] ++ skipn (S x) l)
                              (firstn x l ++ [a'] ++ skipn (S x) l).
    Proof.
      induction 1.
      - simpl. intros x a a' Hnth. now rewrite nth_error_nil in Hnth.
      - intros.
        destruct x0.
        + simpl. constructor. simpl in H, H0. now noconf H; noconf H0.
        + simpl in H, H0.
          specialize (IHX _ _ _ H H0).
          simpl. constructor. auto.
    Qed.

    Lemma red_case {ci mdecl idecl p c brs pars' pret' c' brs'} :
      declared_inductive Σ ci.(ci_ind) mdecl idecl ->
      wf_predicate mdecl idecl p ->
      wf_branches idecl brs ->
      red Σ (Γ ,,, case_predicate_context ci mdecl idecl p) p.(preturn) pret' ->
      All2 (red Σ Γ) p.(pparams) pars' ->
      red Σ Γ c c' ->
      red_brs Γ ci.(ci_ind) mdecl idecl p brs brs' ->
      red Σ Γ (tCase ci p c brs) 
        (tCase ci {| pparams := pars'; puinst := p.(puinst);
                     pcontext := p.(pcontext); preturn := pret' |} c' brs').
    Proof.
      intros decli wfp wfbrs h1 h2 h3 h4.
      eapply red_trans; [eapply red_case_brs|]; eauto.
      eapply red_trans; [eapply red_case_c|]; eauto.
      eapply red_trans; [eapply red_case_p|]; eauto.
      eapply red_trans; [eapply red_case_pars|]; eauto.
    Qed.

    Lemma red1_it_mkLambda_or_LetIn :
      forall Δ u v,
        red1 Σ (Γ ,,, Δ) u v ->
        red1 Σ Γ (it_mkLambda_or_LetIn Δ u)
             (it_mkLambda_or_LetIn Δ v).
    Proof.
      intros Δ u v h.
      revert u v h.
      induction Δ as [| [na [b|] A] Δ ih ] ; intros u v h.
      - cbn. assumption.
      - simpl. eapply ih. cbn. constructor. assumption.
      - simpl. eapply ih. cbn. constructor. assumption.
    Qed.

    Lemma red1_it_mkProd_or_LetIn :
      forall Δ u v,
        red1 Σ (Γ ,,, Δ) u v ->
        red1 Σ Γ (it_mkProd_or_LetIn Δ u)
             (it_mkProd_or_LetIn Δ v).
    Proof.
      intros Δ u v h.
      revert u v h.
      induction Δ as [| [na [b|] A] Δ ih ] ; intros u v h.
      - cbn. assumption.
      - simpl. eapply ih. cbn. constructor. assumption.
      - simpl. eapply ih. cbn. constructor. assumption.
    Qed.

    Lemma red_it_mkLambda_or_LetIn :
      forall Δ u v,
        red Σ (Γ ,,, Δ) u v ->
        red Σ Γ (it_mkLambda_or_LetIn Δ u)
            (it_mkLambda_or_LetIn Δ v).
    Proof.
      intros Δ u v h.
      rst_induction h; eauto with pcuic.
      eapply red1_it_mkLambda_or_LetIn. assumption.
    Qed.

    Lemma red_it_mkProd_or_LetIn :
      forall Δ u v,
        red Σ (Γ ,,, Δ) u v ->
        red Σ Γ (it_mkProd_or_LetIn Δ u)
            (it_mkProd_or_LetIn Δ v).
    Proof.
      intros Δ u v h.
      rst_induction h; eauto with pcuic.
      eapply red1_it_mkProd_or_LetIn. assumption.
    Qed.

    Lemma red_proj_c :
      forall p c c',
        red Σ Γ c c' ->
        red Σ Γ (tProj p c) (tProj p c').
    Proof.
      intros p c c' h.
      rst_induction h; eauto with pcuic.
    Qed.

    Lemma red_fix_one_ty :
      forall mfix idx mfix',
        OnOne2 (on_Trel_eq (red Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
        red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (mfix = mfix').
        { eapply map_inj ; eauto.
          intros y z e. destruct y, z. inversion e. now subst.
        } now subst.
      - set (f := fun x : def term => (dtype x, (dname x, dbody x, rarg x))) in *.
        set (g := fun '(ty, (na, bo, ra)) => mkdef term na ty bo ra).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a as [? [[? ?] ?]]. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a. cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh. symmetry. apply el.
        + constructor. rewrite (el' mfix').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? [[? ?] ?]] [? [[? ?] ?]] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *. inversion h2. subst.
          unfold on_Trel. split ; eauto.
    Qed.

    Lemma red_fix_ty :
      forall mfix idx mfix',
        All2 (on_Trel_eq (red Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
        red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_fix_one_ty. assumption.
    Qed.

    Lemma red_fix_one_body :
      forall mfix idx mfix',
        OnOne2
          (on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix mfix' ->
        red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (mfix = mfix').
        { eapply map_inj ; eauto.
          intros y z e. cbn in e. destruct y, z. inversion e. eauto.
        } subst.
        reflexivity.
      - set (f := fun x : def term => (dbody x, (dname x, dtype x, rarg x))) in *.
        set (g := fun '(bo, (na, ty, ra)) => mkdef term na ty bo ra).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a as [? [[? ?] ?]]. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a. cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh. symmetry. apply el.
        + eapply fix_red_body. rewrite (el' mfix').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? [[? ?] ?]] [? [[? ?] ?]] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *. inversion h2. subst.
          unfold on_Trel. simpl. split ; eauto.
          assert (e : fix_context mfix = fix_context (map g l1)).
          { clear - h el el'. induction h.
            - rewrite <- el'. reflexivity.
            - rewrite IHh.
              unfold fix_context. f_equal.
              assert (e : map snd l1 = map snd l2).
              { clear - p. induction p.
                - destruct p as [h1 h2]. unfold on_Trel in h2.
                  cbn. f_equal. assumption.
                - cbn. f_equal. assumption.
              }
              clear - e.
              unfold mapi. generalize 0 at 2 4.
              intro n.
              induction l1 in l2, e, n |- *.
              + destruct l2 ; try discriminate e. cbn. reflexivity.
              + destruct l2 ; try discriminate e. cbn.
                cbn in e. inversion e.
                specialize (IHl1 _ H1 (S n)).
                destruct a as [? [[? ?] ?]], p as [? [[? ?] ?]].
                simpl in *. inversion H0. subst.
                f_equal. auto.
          }
          rewrite <- e. assumption.
    Qed.

    Lemma red_fix_body :
      forall mfix idx mfix',
        All2
          (on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix mfix' ->
        red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_fix_one_body.
          assert (e : fix_context mfix = fix_context y).
          { clear - h. induction h.
            - reflexivity.
            - rewrite IHh.
              unfold fix_context. f_equal.
              assert (e : map (fun d => (dname d, dtype d)) y = map (fun d => (dname d, dtype d)) z).
              { clear - r. induction r.
                - destruct p as [? e]. inversion e.
                  destruct hd as [? ? ? ?], hd' as [? ? ? ?]. simpl in *. subst.
                  reflexivity.
                - cbn. f_equal. eapply IHr.
              }
              clear - e.
              unfold mapi. generalize 0 at 2 4.
              intro n.
              induction y in z, e, n |- *.
              + destruct z ; try discriminate e. reflexivity.
              + destruct z ; try discriminate e. cbn.
                cbn in e. inversion e.
                destruct a as [? ? ? ?], d as [? ? ? ?]. simpl in *. subst.
                f_equal. eapply IHy. assumption.
          }
          rewrite <- e. assumption.
    Qed.

    Lemma red_fix_congr :
      forall mfix mfix' idx,
        All2 (fun d0 d1 =>
                (red Σ Γ (dtype d0) (dtype d1)) ×
                (red Σ (Γ ,,, fix_context mfix) (dbody d0) (dbody d1) ×
                (dname d0, rarg d0) = (dname d1, rarg d1))
        ) mfix mfix' ->
      red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix mfix' idx h.
      assert (∑ mfixi,
        All2 (
          on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody
                     (fun x : def term => (dname x, dtype x, rarg x))
        ) mfix mfixi ×
        All2 (
          on_Trel_eq (red Σ Γ) dtype
                     (fun x : def term => (dname x, dbody x, rarg x))

        ) mfixi mfix'
      ) as [mfixi [h1 h2]].
      { revert h. generalize (Γ ,,, fix_context mfix). intros Δ h.
        induction h.
        - exists []. auto.
        - destruct r as [? [? e]]. inversion e.
          destruct IHh as [mfixi [? ?]].
          eexists (mkdef _ _ _ _ _ :: mfixi). split.
          + constructor ; auto. simpl. split ; eauto.
          + constructor ; auto. simpl. split ; eauto. f_equal ; auto.
            f_equal. assumption.
      }
      eapply red_trans.
      - eapply red_fix_body. eassumption.
      - eapply red_fix_ty. assumption.
    Qed.

    Lemma red_cofix_one_ty :
      forall mfix idx mfix',
        OnOne2 (on_Trel_eq (red Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
        red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (mfix = mfix').
        { eapply map_inj ; eauto.
          intros y z e. cbn in e. destruct y, z. inversion e. eauto.
        } subst.
        reflexivity.
      - set (f := fun x : def term => (dtype x, (dname x, dbody x, rarg x))) in *.
        set (g := fun '(ty, (na, bo, ra)) => mkdef term na ty bo ra).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a as [? [[? ?] ?]]. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a. cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh. symmetry. apply el.
        + constructor. rewrite (el' mfix').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? [[? ?] ?]] [? [[? ?] ?]] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *. inversion h2. subst.
          unfold on_Trel. split ; eauto.
    Qed.

    Lemma red_cofix_ty :
      forall mfix idx mfix',
        All2 (on_Trel_eq (red Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
        red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_cofix_one_ty. assumption.
    Qed.

    Lemma red_cofix_one_body :
      forall mfix idx mfix',
        OnOne2
          (on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix mfix' ->
        red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (mfix = mfix').
        { eapply map_inj ; eauto.
          intros y z e. cbn in e. destruct y, z. inversion e. eauto.
        } subst.
        reflexivity.
      - set (f := fun x : def term => (dbody x, (dname x, dtype x, rarg x))) in *.
        set (g := fun '(bo, (na, ty, ra)) => mkdef term na ty bo ra).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a as [? [[? ?] ?]]. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a. cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh. symmetry. apply el.
        + eapply cofix_red_body. rewrite (el' mfix').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? [[? ?] ?]] [? [[? ?] ?]] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *. inversion h2. subst.
          unfold on_Trel. simpl. split ; eauto.
          assert (e : fix_context mfix = fix_context (map g l1)).
          { clear - h el el'. induction h.
            - rewrite <- el'. reflexivity.
            - rewrite IHh.
              unfold fix_context. f_equal.
              assert (e : map snd l1 = map snd l2).
              { clear - p. induction p.
                - destruct p as [h1 h2]. unfold on_Trel in h2.
                  cbn. f_equal. assumption.
                - cbn. f_equal. assumption.
              }
              clear - e.
              unfold mapi. generalize 0 at 2 4.
              intro n.
              induction l1 in l2, e, n |- *.
              + destruct l2 ; try discriminate e. cbn. reflexivity.
              + destruct l2 ; try discriminate e. cbn.
                cbn in e. inversion e.
                specialize (IHl1 _ H1 (S n)).
                destruct a as [? [[? ?] ?]], p as [? [[? ?] ?]].
                simpl in *. inversion H0. subst.
                f_equal. auto.
          }
          rewrite <- e. assumption.
    Qed.

    Lemma red_cofix_body :
      forall mfix idx mfix',
        All2
          (on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix mfix' ->
        red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros mfix idx mfix' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_cofix_one_body.
          assert (e : fix_context mfix = fix_context y).
          { clear - h. induction h.
            - reflexivity.
            - rewrite IHh.
              unfold fix_context. f_equal.
              assert (e : map (fun d => (dname d, dtype d)) y = map (fun d => (dname d, dtype d)) z).
              { clear - r. induction r.
                - destruct p as [? e]. inversion e.
                  destruct hd as [? ? ? ?], hd' as [? ? ? ?]. simpl in *. subst.
                  reflexivity.
                - cbn. f_equal. eapply IHr.
              }
              clear - e.
              unfold mapi. generalize 0 at 2 4.
              intro n.
              induction y in z, e, n |- *.
              + destruct z ; try discriminate e. reflexivity.
              + destruct z ; try discriminate e. cbn.
                cbn in e. inversion e.
                destruct a as [? ? ? ?], d as [? ? ? ?]. simpl in *. subst.
                f_equal. eapply IHy. assumption.
          }
          rewrite <- e. assumption.
    Qed.

    Lemma red_cofix_congr :
      forall mfix mfix' idx,
        All2 (fun d0 d1 =>
                (red Σ Γ (dtype d0) (dtype d1)) ×
                (red Σ (Γ ,,, fix_context mfix) (dbody d0) (dbody d1) ×
                (dname d0, rarg d0) = (dname d1, rarg d1))
        ) mfix mfix' ->
      red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros mfix mfix' idx h.
      assert (∑ mfixi,
        All2 (
          on_Trel_eq (red Σ (Γ ,,, fix_context mfix)) dbody
                     (fun x : def term => (dname x, dtype x, rarg x))
        ) mfix mfixi ×
        All2 (
          on_Trel_eq (red Σ Γ) dtype
                     (fun x : def term => (dname x, dbody x, rarg x))

        ) mfixi mfix'
      ) as [mfixi [h1 h2]].
      { revert h. generalize (Γ ,,, fix_context mfix). intros Δ h.
        induction h.
        - exists []. auto.
        - destruct r as [? [? e]]. inversion e.
          destruct IHh as [mfixi [? ?]].
          eexists (mkdef _ _ _ _ _ :: mfixi). split.
          + constructor ; auto. simpl. split ; eauto.
          + constructor ; auto. simpl. split ; eauto. f_equal ; auto.
            f_equal. assumption.
      }
      eapply red_trans.
      - eapply red_cofix_body. eassumption.
      - eapply red_cofix_ty. assumption.
    Qed.

    Lemma red_prod_l :
      forall na A B A',
        red Σ Γ A A' ->
        red Σ Γ (tProd na A B) (tProd na A' B).
    Proof.
      intros na A B A' h.
      rst_induction h; eauto with pcuic.
    Qed.

    Lemma red_prod_r :
      forall na A B B',
        red Σ (Γ ,, vass na A) B B' ->
        red Σ Γ (tProd na A B) (tProd na A B').
    Proof.
      intros na A B B' h.
      rst_induction h; eauto with pcuic.
    Qed.

    Lemma red_prod :
      forall na A B A' B',
        red Σ Γ A A' ->
        red Σ (Γ ,, vass na A) B B' ->
        red Σ Γ (tProd na A B) (tProd na A' B').
    Proof.
      intros na A B A' B' h1 h2.
      eapply red_trans.
      - eapply red_prod_r. eassumption.
      - eapply red_prod_l. assumption.
    Qed.

    Lemma red_one_evar :
      forall ev l l',
        OnOne2 (red Σ Γ) l l' ->
        red Σ Γ (tEvar ev l) (tEvar ev l').
    Proof.
      intros ev l l' h.
      apply OnOne2_on_Trel_eq_unit in h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - assert (l = l').
        { eapply map_inj ; eauto.
          intros y z e. cbn in e. inversion e. eauto.
        } subst.
        reflexivity.
      - set (f := fun x : term => (x, tt)) in *.
        set (g := (fun '(x, _) => x) : term × unit -> term).
        assert (el :  forall l, l = map f (map g l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. destruct a, u. cbn. f_equal. assumption.
        }
        assert (el' :  forall l, l = map g (map f l)).
        { clear. intros l. induction l.
          - reflexivity.
          - cbn. f_equal. assumption.
        }
        eapply trans_red.
        + eapply IHh. symmetry. apply el.
        + constructor. rewrite (el' l').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
          intros [? []] [? []] [h1 h2].
          unfold on_Trel in h1, h2. cbn in *.
          unfold on_Trel. cbn. assumption.
    Qed.

    Lemma red_evar :
      forall ev l l',
        All2 (red Σ Γ) l l' ->
        red Σ Γ (tEvar ev l) (tEvar ev l').
    Proof.
      intros ev l l' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - reflexivity.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_one_evar. assumption.
    Qed.

    Lemma red_atom t : atom t -> red Σ Γ t t.
    Proof.
      intros. reflexivity.
    Qed.

  End Congruences.
End ReductionCongruence.

Hint Resolve All_All2 : all.
Hint Resolve All2_same : pred.

Lemma OnOne2_All2 {A}:
  forall (ts ts' : list A) P Q,
    OnOne2 P ts ts' ->
    (forall x y, P x y -> Q x y)%type ->
    (forall x, Q x x) ->
    All2 Q ts ts'.
Proof.
  intros ts ts' P Q X.
  induction X; intuition auto with pred.
Qed.

Ltac OnOne2_All2 :=
  match goal with
  | [ H : OnOne2 ?P ?ts ?ts' |- All2 ?Q ?ts ?ts' ] =>
    unshelve eapply (OnOne2_All2 _ _ P Q H); simpl; intros
  end.

Hint Extern 0 (All2 _ _ _) => OnOne2_All2; intuition auto with pred : pred.

Lemma nth_error_firstn_skipn {A} {l : list A} {n t} : 
  nth_error l n = Some t -> 
  l = firstn n l ++ [t] ++ skipn (S n) l.
Proof. induction l in n |- *; destruct n; simpl; try congruence.
  intros. specialize (IHl _ H).
  now simpl in IHl.
Qed.

Lemma split_nth {A B} {l : list A} (l' l'' : list B) :
  (#|l| = #|l'| + S (#|l''|))%nat ->
  ∑ x, (nth_error l #|l'| = Some x) * (l = firstn #|l'| l ++ x :: skipn (S #|l'|) l).
Proof.
  induction l in l', l'' |- *; simpl; auto.
  - rewrite Nat.add_succ_r //.
  - rewrite Nat.add_succ_r => [= len].
    destruct l'; simpl.
    * exists a; auto.
    * simpl in len. rewrite -Nat.add_succ_r in len.
      specialize (IHl _ _ len) as [x eq].
      exists x; now f_equal.
Qed.

Lemma nth_error_map2 {A B C} (f : A -> B -> C) (l : list A) (l' : list B) n x : 
  nth_error (map2 f l l') n = Some x ->
  ∑ lx l'x, (nth_error l n = Some lx) *
    (nth_error l' n = Some l'x) * 
    (f lx l'x = x).
Proof.
  induction l in l', n, x |- *; destruct l', n; simpl; auto => //.
  intros [= <-].
  eexists _, _; intuition eauto.
Qed.

(* TODO Find a better place for this. *)
Require Import PCUICPosition.
Section Stacks.

  Context (Σ : global_env_ext).
  Context `{checker_flags}.

  Lemma red1_context :
    forall Γ t u π,
      wf_stack Σ π ->
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π wfπ h.
    cbn. revert wfπ t u h.
    induction π ; intros wfπ u v h; simpl in wfπ.
    all: try solve [ cbn ; apply IHπ ; [assumption|]; constructor ; assumption ].
    - cbn. assumption.
    - cbn. apply IHπ; [assumption|]. constructor.
      apply OnOne2_app. constructor.
      simpl. intuition eauto.
    - cbn. apply IHπ; [assumption|]. eapply fix_red_body.
      apply OnOne2_app. constructor.
      simpl in *.
      rewrite fix_context_fix_context_alt.
      rewrite map_app. cbn. unfold def_sig at 2. simpl.
      rewrite app_context_assoc in h.
      intuition eauto.
    - cbn. apply IHπ; [assumption|]. constructor.
      apply OnOne2_app. constructor.
      simpl. intuition eauto.
    - cbn. apply IHπ; [assumption|]. eapply cofix_red_body.
      apply OnOne2_app. constructor.
      simpl in *.
      rewrite fix_context_fix_context_alt.
      rewrite map_app. cbn. unfold def_sig at 2. simpl.
      rewrite app_context_assoc in h.
      intuition eauto.
    - cbn. destruct wfπ as [[mdecl [idecl decli]] wfπ].
      apply IHπ; [assumption|]. econstructor; tea.
      apply OnOne2_app. constructor.
      simpl. intuition eauto.
    - destruct wfπ as [[mdecl [idecl [[decli wfp] eq]]] wf]. cbn.
      eapply IHπ; [assumption|]. simpl in h.
      econstructor; eauto. unfold case_predicate_context.
      rewrite -eq. now rewrite app_context_assoc in h.
    - cbn. destruct wfπ as [[mdecl [idecl decli]] wfπ].
      apply IHπ; [assumption|]. econstructor; tea.
    - destruct wfπ as [[mdecl [idecl [[decli wfp] [[wfb enth] elen]]]] wf].
      cbn; apply IHπ; [assumption|].
      econstructor; eauto.
      { eapply wf_branches_to_gen. now rewrite !map_app /=. }
      destruct (split_nth _ _ elen) as [cdecl [hnth ->]].
      eapply OnOne2All_app.
      2:{ eapply nth_error_Some_length in enth. rewrite firstn_length_le //; lia. }
      simpl.
      constructor; try split; auto.
      * simpl in h. cbn -[case_branch_context].
        rewrite app_context_assoc in h.
        assert (bctx = case_branch_context ci.(ci_ind) mdecl p (forget_types bctx) cdecl).
        { unfold case_branches_contexts in enth.
          apply nth_error_map2 in enth as [bctx'  [cdecl' [[Hnth Hnth'] cbc]]].
          rewrite Hnth' in hnth. noconf hnth.
          rewrite nth_error_app_ge in Hnth; len => //.
          len in Hnth. rewrite Nat.sub_diag /= in Hnth. noconf Hnth.
          easy. }
        now rewrite -H0.
      * eapply nth_error_Some_length in enth. rewrite skipn_length //; lia.
  Qed.

  Corollary red_context :
    forall Γ t u π,
      wf_stack Σ π ->
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π wf h.
    have hred := red1_context _ _ _ _ wf.
    rst_induction h; eauto with pcuic.
  Qed.

  Lemma red1_zipp :
    forall Γ t u π,
      red1 Σ Γ t u ->
      red1 Σ Γ (zipp t π) (zipp u π).
  Proof.
    intros Γ t u π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply red1_mkApps_f.
    assumption.
  Qed.

  Lemma red_zipp :
    forall Γ t u π,
      red Σ Γ t u ->
      red Σ Γ (zipp t π) (zipp u π).
  Proof.
    intros Γ t u π h.
    rst_induction h; eauto with pcuic.
    eapply red1_zipp. assumption.
  Qed.

  Lemma red1_zippx :
    forall Γ t u π,
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zippx t π) (zippx u π).
  Proof.
    intros Γ t u π h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    eapply red1_it_mkLambda_or_LetIn.
    eapply red1_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack in h.
    assumption.
  Qed.

  Corollary red_zippx :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zippx t π) (zippx u π).
  Proof.
    intros Γ t u π h.
    rst_induction h; eauto with pcuic.
    eapply red1_zippx. assumption.
  Qed.

End Stacks.

(** Not used anywhere *)
(*
(* Properties about context closure *)
(** Reductions at top level *)
Inductive tred1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

(** Beta *)
| tred_beta na t b a :
    tred1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| tred_zeta na b t b' :
    tred1 Σ Γ (tLetIn na b t b') (subst10 b b')

| tred_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    tred1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| tred_iota ci c u args p brs :
    tred1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) c args brs)

(** Fix unfolding, with guard *)
| tred_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    tred1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| tred_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    tred1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| tred_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    tred1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| tred_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    tred1 Σ Γ (tConst c u) (subst_instance_constr u body)

(** Proj *)
| tred_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    tred1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg.

Definition ctred1 Σ :=
  context_env_clos (tred1 Σ).

(* TODO Prove context_clos_impl using subrelation *)

Lemma tred1_red1 :
  forall Σ Γ u v,
    tred1 Σ Γ u v ->
    red1 Σ Γ u v.
Proof.
  intros Σ Γ u v h.
  destruct h.
  all: solve [
    econstructor ; eauto
  ].
Qed.

Lemma ctred1_red1 :
  forall Σ Γ u v,
    ctred1 Σ Γ u v ->
    red1 Σ Γ u v.
Proof.
  intros Σ Γ u' v' [u [v [π [h [? ?]]]]]. subst.
  induction π in Γ, u, v, h |- * using stack_rev_rect.
  all: try solve [
    rewrite 2!zipc_stack_cat ; cbn ;
    rewrite stack_context_stack_cat in h ; cbn in h ;
    rewrite ?app_context_nil_l ?app_context_assoc in h ;
    econstructor ; eapply IHπ ; eassumption
  ].
  - cbn. eapply tred1_red1. assumption.
  - rewrite 2!zipc_stack_cat. cbn.
    rewrite stack_context_stack_cat in h. cbn in h.
    rewrite app_context_nil_l in h.
    eapply fix_red_ty. eapply OnOne2_app. constructor. cbn.
    intuition auto.
  - rewrite 2!zipc_stack_cat. cbn.
    rewrite stack_context_stack_cat in h. cbn in h.
    rewrite app_context_nil_l in h.
    eapply fix_red_body. eapply OnOne2_app. constructor. cbn.
    intuition auto.
    eapply IHπ.
    rewrite fix_context_fix_context_alt.
    rewrite map_app. cbn. unfold def_sig at 2. cbn.
    rewrite app_context_assoc in h.
    assumption.
  - rewrite 2!zipc_stack_cat. cbn.
    rewrite stack_context_stack_cat in h. cbn in h.
    rewrite app_context_nil_l in h.
    eapply cofix_red_ty. eapply OnOne2_app. constructor. cbn.
    intuition auto.
  - rewrite 2!zipc_stack_cat. cbn.
    rewrite stack_context_stack_cat in h. cbn in h.
    rewrite app_context_nil_l in h.
    eapply cofix_red_body. eapply OnOne2_app. constructor. cbn.
    intuition auto.
    eapply IHπ.
    rewrite fix_context_fix_context_alt.
    rewrite map_app. cbn. unfold def_sig at 2. cbn.
    rewrite app_context_assoc in h.
    assumption.
  - rewrite 2!zipc_stack_cat. cbn.
    rewrite stack_context_stack_cat in h. cbn in h.
    rewrite app_context_nil_l in h.
    econstructor. eapply OnOne2_app. constructor. cbn.
    intuition auto.
  -
Qed.
*)