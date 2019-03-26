(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

(** Atoms reduce to themselves *)

Definition atom t :=
  match t with
  | tRel _
  | tVar _
  | tMeta _
  | tSort _
  | tConst _ _
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _ => true
  | _ => false
  end.

(** Simple lemmas about reduction *)

Lemma red1_red (Σ : global_context) Γ t u : red1 (fst Σ) Γ t u -> red (fst Σ) Γ t u.
Proof. econstructor; eauto. constructor. Qed.
Hint Resolve red1_red refl_red.

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  induction 2. econstructor; auto.
  econstructor 2; eauto.
Qed.

Lemma red_alt@{i j +} Σ Γ t u : red Σ Γ t u <~> clos_refl_trans@{i j} (red1 Σ Γ) t u.
Proof.
  split. intros H. apply clos_rt_rtn1_iff.
  induction H; econstructor; eauto.
  intros H. apply clos_rt_rtn1_iff in H.
  induction H; econstructor; eauto.
Qed.

Lemma red_trans Σ Γ t u v : red Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  intros. apply red_alt. apply red_alt in X. apply red_alt in X0. now econstructor 3.
Defined.

Instance red_Transitive Σ Γ : Transitive (red Σ Γ).
Proof. refine (red_trans _ _). Qed.

(** Generic method to show that a relation is closed by congruence using
    a notion of one-hole context. *)

Section ReductionCongruence.
  Context {Σ : global_context}.

  Inductive term_context : Set :=
  | tCtxHole : term_context
  | tCtxEvar      : nat -> list_context -> term_context
  | tCtxProd_l      : name -> term_context (* the type *) -> term -> term_context
  | tCtxProd_r      : name -> term (* the type *) -> term_context -> term_context
  | tCtxLambda_l    : name -> term_context (* the type *) -> term -> term_context
  | tCtxLambda_r    : name -> term (* the type *) -> term_context -> term_context
  | tCtxLetIn_l     : name -> term_context (* the term *) -> term (* the type *) ->
                    term -> term_context
  | tCtxLetIn_b     : name -> term (* the term *) -> term_context (* the type *) ->
                    term -> term_context
  | tCtxLetIn_r     : name -> term (* the term *) -> term (* the type *) ->
                    term_context -> term_context
  | tCtxApp_l       : term_context -> term -> term_context
  | tCtxApp_r      : term -> term_context -> term_context
  | tCtxCase_pred      : (inductive * nat) (* # of parameters *) -> term_context (* type info *)
                         -> term (* discriminee *) -> list (nat * term) (* branches *) -> term_context
  | tCtxCase_discr      : (inductive * nat) (* # of parameters *) -> term (* type info *)
                 -> term_context (* discriminee *) -> list (nat * term) (* branches *) -> term_context
  | tCtxCase_branch      : (inductive * nat) (* # of parameters *) -> term (* type info *)
                           -> term (* discriminee *) -> list_nat_context (* branches *) -> term_context
  | tCtxProj      : projection -> term_context -> term_context
  | tCtxFix       : mfixpoint term -> nat -> term_context (* TODO *)
  | tCtxCoFix     : mfixpoint term -> nat -> term_context (* TODO *)

  with list_context : Set :=
   | tCtxHead : term_context -> list term -> list_context
   | tCtxTail : term -> list_context -> list_context

  with list_nat_context : Set :=
   | tCtxHead_nat : (nat * term_context) -> list (nat * term) -> list_nat_context
   | tCtxTail_nat : (nat * term) -> list_nat_context -> list_nat_context.

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
    | tCtxCase_pred par p c brs => tCase par (fill_context p) c brs;
    | tCtxCase_discr par p c brs => tCase par p (fill_context c) brs;
    | tCtxCase_branch par p c brs => tCase par p c (fill_list_nat_context brs);
    | tCtxProj p c => tProj p (fill_context c);
    | tCtxFix mfix n => tFix mfix n;
    | tCtxCoFix mfix n => tCoFix mfix n }
    with fill_list_context (l : list_context) : list term by struct l :=
    { fill_list_context (tCtxHead ctx l) => (fill_context ctx) :: l;
      fill_list_context (tCtxTail hd ctx) => hd :: fill_list_context ctx }
    with fill_list_nat_context (l : list_nat_context) : list (nat * term) by struct l :=
    { fill_list_nat_context (tCtxHead_nat (n, ctx) l) => (n, fill_context ctx) :: l;
      fill_list_nat_context (tCtxTail_nat hd ctx) => hd :: fill_list_nat_context ctx }.
    Global Transparent fill_context fill_list_context fill_list_nat_context.

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
    | tCtxCase_pred par p c brs | Γ => hole_context p Γ;
    | tCtxCase_discr par p c brs | Γ => hole_context c Γ;
    | tCtxCase_branch par p c brs | Γ => hole_list_nat_context brs Γ;
    | tCtxProj p c | Γ => hole_context c Γ;
    | tCtxFix mfix n | Γ => Γ; (* TODO *)
    | tCtxCoFix mfix n | Γ => Γ }
    with hole_list_context (l : list_context) (Γ : context) : context by struct l :=
    { hole_list_context (tCtxHead ctx l) Γ => hole_context ctx Γ;
      hole_list_context (tCtxTail hd ctx) Γ => hole_list_context ctx Γ }
    with hole_list_nat_context (l : list_nat_context) (Γ : context) : context by struct l :=
    { hole_list_nat_context (tCtxHead_nat (n, ctx) l) Γ => hole_context ctx Γ;
      hole_list_nat_context (tCtxTail_nat hd ctx) Γ => hole_list_nat_context ctx Γ }.
    Global Transparent hole_context hole_list_context hole_list_nat_context.

  End FillContext.

  Inductive contextual_closure (red : ∀ Γ, term -> term -> Type) : context -> term -> term -> Type :=
  | ctxclos_atom Γ t : atom t -> contextual_closure red Γ t t
  | ctxclos_ctx Γ (ctx : term_context) (u u' : term) :
      red (hole_context ctx Γ) u u' -> contextual_closure red Γ (fill_context u ctx) (fill_context u' ctx).

  Lemma red_contextual_closure Γ t u : red Σ Γ t u -> contextual_closure (red Σ) Γ t u.
  Proof.
    intros Hred.
    apply (ctxclos_ctx (red Σ) Γ tCtxHole t u Hred).
  Qed.

  Arguments fill_list_context : simpl never.

  Lemma contextual_closure_red Γ t u : contextual_closure (red Σ) Γ t u -> red Σ Γ t u.
  Proof.
    induction 1. constructor.
    apply red_alt in r. apply clos_rt_rt1n in r.
    induction r. constructor. apply clos_rt_rt1n_iff in r0. apply red_alt in r0.
    eapply red_step; eauto. clear r0 IHr z.
    set (P := fun ctx t => forall Γ y, red1 Σ (hole_context ctx Γ) x y ->
                                     red1 Σ Γ t (fill_context y ctx)).
    set (P' := fun l fill_l =>
                 forall Γ y,
                   red1 Σ (hole_list_context l Γ) x y ->
                   OnOne2 (red1 (fst Σ) Γ) fill_l (fill_list_context y l)).
    revert Γ y r.
    eapply (fill_context_elim x P P' _); subst P P'; cbv beta;
      intros **; simp fill_context; cbn in *; auto; try solve [constructor; eauto].
    - simpl in *. (* FIXME missing case in red1 for predicate *)
      admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem red_contextual_closure_equiv Γ t u : red Σ Γ t u <~> contextual_closure (red Σ) Γ t u.
  Proof.
    split. apply red_contextual_closure. apply contextual_closure_red.
  Qed.

  (* Lemma contextual_closure_trans (R : context -> term -> term -> Type) Γ : *)
  (*   Transitive (R Γ) -> *)
  (*   forall t u v, *)
  (*   contextual_closure R Γ t u -> contextual_closure R Γ u v -> *)
  (*   contextual_closure R Γ t v. *)
  (* Proof. *)
  (*   intros Htr t u v. *)
  (*   induction 1. destruct 1. constructor; auto. *)
  (*   constructor. auto. *)
  (*   intros H. depelim H. constructor; auto. *)
  (* Admitted. *)

  Lemma red_ctx {Γ} {M M'} ctx : red Σ (hole_context ctx Γ) M M' ->
                               red Σ Γ (fill_context M ctx) (fill_context M' ctx).
  Proof.
    intros.
    apply red_contextual_closure_equiv.
    now apply (ctxclos_ctx _ _ ctx).
  Qed.

  Section Congruences.
    Context {Γ : context}.

    Lemma red_abs na M M' N N' : red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N' ->
                                               red Σ Γ (tLambda na M N) (tLambda na M' N').
    Proof.
      intros. eapply (transitivity (y := tLambda na M' N)).
      now apply (red_ctx (tCtxLambda_l _ tCtxHole _)).
      now eapply (red_ctx (tCtxLambda_r _ _ tCtxHole)).
    Qed.

    Lemma red_app M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      red Σ Γ N0 N1 ->
      red Σ Γ (tApp M0 N0) (tApp M1 N1).
    Proof.
      intros; eapply (transitivity (y := tApp M1 N0)).
      now apply (red_ctx (tCtxApp_l tCtxHole _)).
      now eapply (red_ctx (tCtxApp_r _ tCtxHole)).
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

    Lemma red_mkApps M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      All2 (red Σ Γ) N0 N1 ->
      red Σ Γ (mkApps M0 N0) (mkApps M1 N1).
    Proof.
      intros.
      induction X0 in M0, M1, X |- *. auto.
      simpl. eapply IHX0. now eapply red_app.
    Qed.

    Lemma red_letin na d0 d1 t0 t1 b0 b1 :
      red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d1 t1) b0 b1 ->
      red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
    Proof.
      intros; eapply (transitivity (y := tLetIn na d1 t0 b0)).
      now apply (red_ctx (tCtxLetIn_l _ tCtxHole _ _)).
      eapply (transitivity (y := tLetIn na d1 t1 b0)).
      now eapply (red_ctx (tCtxLetIn_b _ _ tCtxHole _)).
      now eapply (red_ctx (tCtxLetIn_r _ _ _ tCtxHole)).
    Qed.

    Lemma red_case ind p0 p1 c0 c1 brs0 brs1 :
      red Σ Γ p0 p1 ->
      red Σ Γ c0 c1 ->
      All2 (on_Trel (red Σ Γ) snd) brs0 brs1 ->
      red Σ Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1).
    Proof.
      intros; eapply (transitivity (y := tCase ind p1 c0 brs0)).
      now apply (red_ctx (tCtxCase_pred _ tCtxHole _ _)).
      eapply (transitivity (y := tCase ind p1 c1 brs0)).
      now eapply (red_ctx (tCtxCase_discr _ _ tCtxHole _)).
      admit.
    Admitted.

    Lemma red_proj_congr p c c' : red Σ Γ c c' -> red Σ Γ (tProj p c) (tProj p c').
    Proof.
    (*   intros; eapply (transitivity (y := tApp M1 N0)). *)
    (*   now apply (red_ctx (tCtxApp_l tCtxHole _)). *)
    (*   now eapply (red_ctx (tCtxApp_r _ tCtxHole)). *)
    (* Qed. *)
    Admitted.

    Lemma red_fix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (red Σ Γ (dtype d0) (dtype d1)) *
                         (red Σ (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      red Σ Γ (tFix mfix0 idx) (tFix mfix1 idx).
    Proof.
    Admitted.

    (*   intros; eapply (transitivity (y := tApp M1 N0)). *)
    (*   now apply (red_ctx (tCtxApp_l tCtxHole _)). *)
    (*   now eapply (red_ctx (tCtxApp_r _ tCtxHole)). *)
    (* Qed. *)

    Lemma red_cofix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (red Σ Γ (dtype d0) (dtype d1)) *
                         (red Σ (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      red Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx).
    Proof.
    Admitted.
    (*   intros; eapply (transitivity (y := tApp M1 N0)). *)
    (*   now apply (red_ctx (tCtxApp_l tCtxHole _)). *)
    (*   now eapply (red_ctx (tCtxApp_r _ tCtxHole)). *)
    (* Qed. *)

    Lemma red_prod na M0 M1 N0 N1 : red Σ Γ M0 M1 -> red Σ (Γ ,, vass na M0) N0 N1 ->
                                    red Σ Γ (tProd na M0 N0) (tProd na M1 N1).
    Proof.
    (*   intros; eapply (transitivity (y := tApp M1 N0)). *)
    (*   now apply (red_ctx (tCtxApp_l tCtxHole _)). *)
    (*   now eapply (red_ctx (tCtxApp_r _ tCtxHole)). *)
    (* Qed. *)
    Admitted.

    Lemma red_evar ev l l' : All2 (red Σ Γ) l l' -> red Σ Γ (tEvar ev l) (tEvar ev l').
    Proof.
    Admitted.
    (*   intros; eapply (transitivity (y := tApp M1 N0)). *)
    (*   now apply (red_ctx (tCtxApp_l tCtxHole _)). *)
    (*   now eapply (red_ctx (tCtxApp_r _ tCtxHole)). *)
    (* Qed. *)

    Lemma red_atom t : atom t -> red Σ Γ t t.
    Proof.
      intros. constructor.
    Qed.

  End Congruences.
End ReductionCongruence.

Hint Resolve All_All2 : all.

Section ParallelReduction.
  Context (Σ : global_declarations).

  Inductive pred1 (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t b0 b1 a0 a1 :
      pred1 (Γ ,, vass na t) b0 b1 -> pred1 Γ a0 a1 ->
      pred1 Γ (tApp (tLambda na t b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t b0 b1 :
      pred1 Γ d0 d1 -> pred1 Γ b0 b1 ->
      pred1 Γ (tLetIn na d0 t b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def i body body' :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      pred1 Γ (lift0 (S i) body) body' ->
      pred1 Γ (tRel i) body'

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2 (pred1 Γ) args0 args1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix idx args0 args1 narg fn0 fn1 :
      unfold_fix mfix idx = Some (narg, fn0) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix idx args0 args1 narg fn0 fn1 brs0 brs1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ p0 p1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0)
            (tCase ip (mkApps fn1 args1) p1 brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix idx args0 args1 narg fn0 fn1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (tProj p (mkApps (tCoFix mfix idx) args0))
            (tProj p (mkApps fn1 args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      pred1 Γ (tConst c u) (subst_instance_constr u body)

  (** Proj *)
  | pred_proj i pars narg args k u args0 args1 arg1 :
      All2 (pred1 Γ) args0 args1 ->
      nth_error args (pars + narg) = Some arg1 ->
      pred1 Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ M M' -> pred1 (Γ ,, vass na M) N N' ->
                            pred1 Γ (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ M0 M1 ->
      pred1 Γ N0 N1 ->
      pred1 Γ (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)
  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ d0 d1 -> pred1 Γ t0 t1 -> pred1 (Γ ,, vdef na d0 t0) b0 b1 ->
      pred1 Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ p0 p1 ->
      pred1 Γ c0 c1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' : pred1 Γ c c' -> pred1 Γ (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (pred1 Γ (dtype d0) (dtype d1)) *
                         (pred1 (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      pred1 Γ (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (pred1 Γ (dtype d0) (dtype d1)) *
                            (pred1 (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      pred1 Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ M0 M1 -> pred1 (Γ ,, vass na M0) N0 N1 ->
                               pred1 Γ (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' : All2 (pred1 Γ) l l' -> pred1 Γ (tEvar ev l) (tEvar ev l')

  | pred_atom t : atom t -> pred1 Γ t t.

  Definition All2_prop_relevant Γ {A} (f : A -> term) (rel1 : forall (t t' : term), pred1 Γ t t' -> Type) :=
    All2 (fun x y => { red : pred1 Γ (f x) (f y) & rel1 (f x) (f y) red}).

  Definition All2_prop Γ {A} (f : A -> term) (rel : forall (Γ : context) (t t' : term), Type) :=
    All2 (on_Trel (rel Γ) f).

  Definition All2_prop2 Γ Γ' {A} (f g : A -> term) (rel : forall (Γ : context) (t t' : term), Type) :=
    All2 (fun x y => (on_Trel (rel Γ) f x y) * on_Trel (rel Γ') g x y)%type.

  (* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

  Lemma All2_All2_prop {A} {P Q : context -> term -> term -> Type} {par} {f : A -> term} {l l' : list A} :
    All2 (on_Trel (P par) f) l l' ->
    (forall x y, P par x y -> Q par x y) ->
    All2_prop par f Q l l'.
  Proof.
    intros H aux.
    induction H; constructor. unfold on_Trel in *.
    apply aux. apply r. apply IHAll2.
  Defined.

  Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'} {f g : A -> term} {l l' : list A} :
    All2_prop2 par par' f g P l l' ->
    (forall par x y, P par x y -> Q par x y) ->
    All2_prop2 par par' f g Q l l'.
  Proof.
    intros H aux.
    induction H; constructor. unfold on_Trel in *. split.
    apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2.
  Defined.

  Definition extendP {P Q: context -> term -> term -> Type} (aux : forall Γ t t', P Γ t t' -> Q Γ t t') :
    (forall Γ t t', P Γ t t' -> (P Γ t t' * Q Γ t t')).
  Proof.
    intros. split. apply X. apply aux. apply X.
  Defined.

  Lemma pred1_ind_all :
    forall P : forall (Γ : context) (t t0 : term), Type,
      let P' Γ x y := ((pred1 Γ x y) * P Γ x y)%type in
      (forall (Γ : context) (na : name) (t b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t) b0 b1 -> P (Γ ,, vass na t) b0 b1 -> pred1 Γ a0 a1 -> P Γ a0 a1 -> P Γ (tApp (tLambda na t b0) a0) (b1 {0 := a1})) ->
      (forall (Γ : context) (na : name) (d0 d1 t b0 b1 : term),
          pred1 Γ d0 d1 -> P Γ d0 d1 -> pred1 Γ b0 b1 -> P Γ (* FIXME *) b0 b1 -> P Γ (tLetIn na d0 t b0) (b1 {0 := d1})) ->
      (forall (Γ : context) (i : nat) (body body' : term),
          option_map decl_body (nth_error Γ i) = Some (Some body) ->
          pred1 Γ ((lift0 (S i)) body) body' -> P Γ ((lift0 (S i)) body) body' -> P Γ (tRel i) body') ->
      (forall (Γ : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_prop Γ id P' args0 args1 ->
          All2_prop Γ snd P' brs0 brs1 ->
          P Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term),
          unfold_fix mfix idx = Some (narg, fn0) ->
          is_constructor narg args1 = true ->
          All2_prop Γ id P' args0 args1 ->
          pred1 Γ fn0 fn1 -> P Γ fn0 fn1 -> P Γ (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) ->
      (forall (Γ : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2_prop Γ id P' args0 args1 ->
          pred1 Γ fn0 fn1 ->
          P Γ fn0 fn1 ->
          pred1 Γ p0 p1 ->
          P Γ p0 p1 ->
          All2_prop Γ snd P' brs0 brs1 ->
          P Γ (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip (mkApps fn1 args1) p1 brs1)) ->
      (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term)
              (narg : nat) (fn0 fn1 : term),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2_prop Γ id P' args0 args1 ->
          pred1 Γ fn0 fn1 -> P Γ fn0 fn1 -> P Γ (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) ->
      (forall (Γ : context) (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2_prop Γ id P' args0 args1 ->
          nth_error args (pars + narg) = Some arg1 -> P Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ : context) (na : name) (M M' N N' : term),
          pred1 Γ M M' ->
          P Γ M M' -> pred1 (Γ,, vass na M) N N' -> P (Γ,, vass na M) N N' -> P Γ (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ : context) (M0 M1 N0 N1 : term),
          pred1 Γ M0 M1 -> P Γ M0 M1 -> pred1 Γ N0 N1 -> P Γ N0 N1 -> P Γ (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ d0 d1 ->
          P Γ d0 d1 ->
          pred1 Γ t0 t1 ->
          P Γ t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) b0 b1 -> P (Γ,, vdef na d0 t0) b0 b1 -> P Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ p0 p1 ->
          P Γ p0 p1 ->
          pred1 Γ c0 c1 ->
          P Γ c0 c1 -> All2_prop Γ snd P' brs0 brs1 -> P Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ : context) (p : projection) (c c' : term), pred1 Γ c c' -> P Γ c c' -> P Γ (tProj p c) (tProj p c')) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_prop2 Γ (Γ ,,, fix_context mfix0) dtype dbody P' mfix0 mfix1 ->
          P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_prop2 Γ (Γ ,,, fix_context mfix0) dtype dbody P' mfix0 mfix1 ->
          P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ M0 M1 ->
          P Γ M0 M1 -> pred1 (Γ,, vass na M0) N0 N1 -> P (Γ,, vass na M0) N0 N1 -> P Γ (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ : context) (ev : nat) (l l' : list term), All2_prop Γ id P' l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ : context) (t : term), atom t -> P Γ t t) ->
      forall (Γ : context) (t t0 : term), pred1 Γ t t0 -> P Γ t t0.
  Proof.
    intros. revert Γ t t0 X18.
    fix aux 4. intros Γ t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - apply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a ((extendP aux) Γ)).
    - apply (All2_All2_prop (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ)).
    - eapply X3; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a (extendP aux Γ)).
    - eapply X4; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a (extendP aux Γ)).
      eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ)).
    - eapply X5; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a (extendP aux Γ)).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a (extendP aux Γ)).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ)).
    - eapply X13.
      eapply (All2_All2_prop2 (P:=pred1) (Q:=P') (f:=dtype) (g:=dbody) a (extendP aux)).
    - eapply X14.
      eapply (All2_All2_prop2 (P:=pred1) (Q:=P') (f:=dtype) (g:=dbody) a (extendP aux)).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') (f:=id) a (extendP aux Γ)).
  Defined.

  Lemma pred1_refl Γ t : pred1 Γ t t.
  Proof.
    induction t in Γ |- * using term_forall_list_ind;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [constructor; unfold on_Trel; solve_all].
  Qed.

  Hint Constructors pred1 : pred.
  Hint Resolve pred1_refl : pred.

  Lemma All2_same {A} (P : A -> A -> Type) l : (forall x, P x x) -> All2 P l l.
  Proof. induction l; constructor; auto. Qed.

  Hint Resolve All2_same : pred.
  Hint Unfold on_rel on_Trel snd on_snd : pred.

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

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Γ M N.
    induction 1 using red1_ind_all; intros; eauto with pred;
      try solve [constructor; intuition auto with pred].

    constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred.
    constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred.
    constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred.
    constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred.
  Qed.

End ParallelReduction.

Hint Constructors pred1 : pred.
Hint Resolve pred1_refl : pred.
Hint Resolve All2_same : pred.
Hint Unfold on_rel on_Trel snd on_snd : pred.
Ltac OnOne2_All2 :=
  match goal with
  | [ H : OnOne2 ?P ?ts ?ts' |- All2 ?Q ?ts ?ts' ] =>
    unshelve eapply (OnOne2_All2 _ _ P Q H); simpl; intros
  end.
Hint Extern 0 (All2 _ _ _) => OnOne2_All2; intuition auto with pred : pred.

Section ParallelReduction2.
  Context {Σ : global_context}.

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ : forall M N, pred1 Σ Γ M N -> red Σ Γ M N.
  Proof.
    revert Γ. eapply (@pred1_ind_all Σ); intros; try constructor; auto with pred.

    - (* Beta *)
      apply red_trans with (tApp (tLambda na t b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pred.
      apply red_trans with (tApp (tLambda na t b1) a1).
      eapply (@red_app Σ); auto with pred.
      apply red1_red. constructor.

  Admitted.

End ParallelReduction2.

(* Lemma substitution_pred1 `{cf:checker_flags} Σ Γ Γ' Γ'' s M N : *)
(*   wf Σ -> All Ast.wf s -> subs Σ Γ s Γ' -> wf_local Σ Γ -> Ast.wf M -> *)
(*   wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> *)
(*   pred1 (fst Σ) (Γ ,,, Γ' ,,, Γ'') M N -> *)
(*   pred1 (fst Σ) (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N). *)
(* Proof. *)
(*   intros. *)
(*   induction H1. constructor. *)
(*   econstructor 2; eauto. *)
(*   eapply substitution_red1; eauto. *)
(*   eapply wf_red_wf. 4:eauto. all:eauto. *)
(* Qed. *)
