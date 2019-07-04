(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

(** * Parallel reduction and confluence *)

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

(** Simple lemmas about reduction *)

Lemma red1_red (Σ : global_env_ext) Γ t u : red1 (fst Σ) Γ t u -> red (fst Σ) Γ t u.
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
  Context {Σ : global_env_ext}.

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

Lemma All2_same {A} (P : A -> A -> Type) l : (forall x, P x x) -> All2 P l l.
Proof. induction l; constructor; auto. Qed.

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
