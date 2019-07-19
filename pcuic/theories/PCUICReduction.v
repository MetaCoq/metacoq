(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq Require Import LibHypsNaming.
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

Lemma red1_red (Σ : global_env) Γ t u : red1 Σ Γ t u -> red Σ Γ t u.
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
  Context {Σ : global_env}.

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
  (* | tCtxFix       : mfixpoint_context -> nat -> term_context harder because types of fixpoints are necessary *)
  (* | tCtxCoFix     : mfixpoint_context -> nat -> term_context *)

  with list_context : Set :=
   | tCtxHead : term_context -> list term -> list_context
   | tCtxTail : term -> list_context -> list_context

  with list_nat_context : Set :=
   | tCtxHead_nat : (nat * term_context) -> list (nat * term) -> list_nat_context
   | tCtxTail_nat : (nat * term) -> list_nat_context -> list_nat_context.

  (* with mfixpoint_context : Set := *)
  (*  | tCtxHead_mfix : def_context -> list (def term) -> mfixpoint_context *)
  (*  | tCtxTail_mfix : def term -> mfixpoint_context -> mfixpoint_context *)

  (* with def_context : Set := *)
  (*  | tCtxType : name -> term_context -> term -> nat -> def_context *)
  (*  | tCtxDef : name -> term -> term_context -> nat -> def_context. *)

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
    | tCtxProj p c => tProj p (fill_context c) }
    (* | tCtxFix mfix n => tFix (fill_mfix_context mfix) n; *)
    (* | tCtxCoFix mfix n => tCoFix (fill_mfix_context mfix) n } *)

    with fill_list_context (l : list_context) : list term by struct l :=
    { fill_list_context (tCtxHead ctx l) => (fill_context ctx) :: l;
      fill_list_context (tCtxTail hd ctx) => hd :: fill_list_context ctx }

    with fill_list_nat_context (l : list_nat_context) : list (nat * term) by struct l :=
    { fill_list_nat_context (tCtxHead_nat (n, ctx) l) => (n, fill_context ctx) :: l;
      fill_list_nat_context (tCtxTail_nat hd ctx) => hd :: fill_list_nat_context ctx }.

    (* with fill_mfix_context (l : mfixpoint_context) : mfixpoint term by struct l := *)
    (* { fill_mfix_context (tCtxHead_mfix (tCtxType na ty def rarg) l) => *)
    (*     {| dname := na; dtype := fill_context ty; dbody := def; rarg := rarg |} :: l; *)
    (*   fill_mfix_context (tCtxHead_mfix (tCtxDef na ty def rarg) l) => *)
    (*     {| dname := na; dtype := ty; dbody := fill_context def; rarg := rarg |} :: l; *)
    (*   fill_mfix_context (tCtxTail_mfix hd ctx) => hd :: fill_mfix_context ctx }. *)
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
    | tCtxProj p c | Γ => hole_context c Γ }
    (* | tCtxFix mfix n | Γ => hole_mfix_context mfix Γ ; *)
    (* | tCtxCoFix mfix n | Γ => hole_mfix_context mfix Γ } *)

    with hole_list_context (l : list_context) (Γ : context) : context by struct l :=
    { hole_list_context (tCtxHead ctx l) Γ => hole_context ctx Γ;
      hole_list_context (tCtxTail hd ctx) Γ => hole_list_context ctx Γ }

    with hole_list_nat_context (l : list_nat_context) (Γ : context) : context by struct l :=
    { hole_list_nat_context (tCtxHead_nat (n, ctx) l) Γ => hole_context ctx Γ;
      hole_list_nat_context (tCtxTail_nat hd ctx) Γ => hole_list_nat_context ctx Γ }.

    (* with hole_mfix_context (l : mfixpoint_context) (Γ : context) : context by struct l := *)
    (* { hole_mfix_context (tCtxHead_mfix (tCtxType na ctx def rarg) _) Γ => hole_context ctx Γ; *)
    (*   hole_mfix_context (tCtxHead_mfix (tCtxDef na ty ctx rarg) _) Γ => hole_context ctx; *)
    (*   hole_mfix_context (tCtxTail_mfix hd ctx) Γ => hole_mfix_context ctx tys Γ }. *)
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
                   OnOne2 (red1 Σ Γ) fill_l (fill_list_context y l)).
    set (P'' := fun l fill_l =>
                 forall Γ y,
                   red1 Σ (hole_list_nat_context l Γ) x y ->
                   OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) fill_l (fill_list_nat_context y l)).
    (* set (Pfix := fun l fixc fill_l => *)
    (*              forall Γ y, *)
    (*                red1 Σ (hole_mfix_context l fixc Γ) x y -> *)
    (*                (OnOne2 (on_Trel_eq (red1 (fst Σ) Γ) dtype (fun d => (dname d, dbody d, rarg d))) *)
    (*                       fill_l (fill_mfix_context y l fixc)) + *)
    (*                (OnOne2 (on_Trel_eq (red1 (fst Σ) (Γ ,,, fix_context fill_l)) dbody (fun d => (dname d, dtype d, rarg d))) *)
    (*                       fill_l (fill_mfix_context y l fixc))). *)
    revert Γ y r.
    eapply (fill_context_elim x P P' P''); subst P P' P''; cbv beta;
      intros **; simp fill_context; cbn in *; auto; try solve [constructor; eauto].
  Qed.

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

    Inductive redl Γ {A} l : list (term × A) -> Type :=
    | refl_redl : redl Γ l l
    | trans_redl :
        forall l1 l2,
          redl Γ l l1 ->
          OnOne2 (Trel_conj (on_Trel (red1 Σ Γ) fst) (on_Trel eq snd)) l1 l2 ->
          redl Γ l l2.

    Lemma OnOne2_red_redl :
      forall Γ A (l l' : list (term × A)),
        OnOne2 (Trel_conj (on_Trel (red Σ Γ) fst) (on_Trel eq snd)) l l' ->
        redl Γ l l'.
    Proof.
      intros Γ A l l' h.
      induction h.
      - destruct p as [p1 p2].
        unfold on_Trel in p1, p2.
        destruct hd as [t a], hd' as [t' a']. simpl in *. subst.
        induction p1.
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

    Lemma OnOne2_on_Trel_eq_red_redl :
      forall Γ A B (f : A -> term) (g : A -> B) l l',
        OnOne2 (on_Trel_eq (red Σ Γ) f g) l l' ->
        redl Γ (map (fun x => (f x, g x)) l) (map (fun x => (f x, g x)) l').
    Proof.
      intros Γ A B f g l l' h.
      eapply OnOne2_red_redl.
      eapply OnOne2_map. eapply OnOne2_impl ; eauto.
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

    Notation swap := (fun x => (snd x, fst x)).

    Lemma list_map_swap_eq :
      forall A B (l l' : list (A × B)),
        map swap l = map swap l' ->
        l = l'.
    Proof.
      intros A B l l' h.
      induction l in l', h |- *.
      - destruct l' ; try discriminate. reflexivity.
      - destruct l' ; try discriminate.
        cbn in h. inversion h.
        f_equal ; eauto.
        destruct a, p. cbn in *. subst. reflexivity.
    Qed.

    Lemma map_swap_invol :
      forall A B (l : list (A × B)),
        l = map swap (map swap l).
    Proof.
      intros A B l.
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
      intros t u π h. induction h.
      - constructor.
      - econstructor.
        + eapply IHh.
        + eapply red1_mkApps_f. assumption.
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

    Lemma red_case_p :
      forall indn p c brs p',
        red Σ Γ p p' ->
        red Σ Γ (tCase indn p c brs) (tCase indn p' c brs).
    Proof.
      intros indn p c brs p' h.
      induction h.
      - constructor.
      - econstructor ; try eassumption.
        constructor. assumption.
    Qed.

    Lemma red_case_c :
      forall indn p c brs c',
        red Σ Γ c c' ->
        red Σ Γ (tCase indn p c brs) (tCase indn p c' brs).
    Proof.
      intros indn p c brs c' h.
      induction h.
      - constructor.
      - econstructor ; try eassumption.
        constructor. assumption.
    Qed.

    Lemma red_case_one_brs :
      forall indn p c brs brs',
        OnOne2 (on_Trel_eq (red Σ Γ) snd fst) brs brs' ->
        red Σ Γ (tCase indn p c brs) (tCase indn p c brs').
    Proof.
      intros indn p c brs brs' h.
      apply OnOne2_on_Trel_eq_red_redl in h.
      dependent induction h.
      - apply list_map_swap_eq in x. subst. constructor.
      - econstructor.
        + eapply IHh. apply map_swap_invol.
        + constructor. rewrite (map_swap_invol _ _ brs').
          eapply OnOne2_map.
          eapply OnOne2_impl ; eauto.
    Qed.

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

    Lemma red_case_brs :
      forall indn p c brs brs',
        All2 (on_Trel_eq (red Σ Γ) snd fst) brs brs' ->
        red Σ Γ (tCase indn p c brs) (tCase indn p c brs').
    Proof.
      intros indn p c brs brs' h.
      apply All2_many_OnOne2 in h.
      induction h.
      - constructor.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_case_one_brs. assumption.
    Qed.

    (* Fixpoint brs_n_context l := *)
    (*   match l with *)
    (*   | [] => tCtxHole *)
    (*   | hd :: tl => tCtxApp_l (mkApps_context tl) hd *)
    (*   end. *)

    Lemma All2_ind_OnOne2 {A} P (l l' : list A) :
      All2 P l l' ->
      forall x a a', nth_error l x = Some a ->
                     nth_error l' x = Some a' ->
                     OnOne2 P (firstn x l ++ [a] ++ skipn (S x) l)%list
                            (firstn x l ++ [a'] ++ skipn (S x) l)%list.
    Proof.
      induction 1.
      simpl. intros x a a' Hnth. now rewrite nth_error_nil in Hnth.
      intros.
      destruct x0. simpl. constructor. simpl in H, H0. now noconf H; noconf H0.
      simpl in H, H0.
      specialize (IHX _ _ _ H H0).
      simpl. constructor. auto.
    Qed.

    Lemma reds_case :
      forall indn p c brs p' c' brs',
        red Σ Γ p p' ->
        red Σ Γ c c' ->
        All2 (on_Trel_eq (red Σ Γ) snd fst) brs brs' ->
        red Σ Γ (tCase indn p c brs) (tCase indn p' c' brs').
    Proof.
      intros indn p c brs p' c' brs' h1 h2 h3.
      eapply red_trans.
      - eapply red_case_brs. eassumption.
      - eapply red_trans.
        + eapply red_case_c. eassumption.
        + eapply red_case_p. assumption.
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

    Lemma red_it_mkLambda_or_LetIn :
      forall Δ u v,
        red Σ (Γ ,,, Δ) u v ->
        red Σ Γ (it_mkLambda_or_LetIn Δ u)
            (it_mkLambda_or_LetIn Δ v).
    Proof.
      intros Δ u v h.
      induction h.
      - constructor.
      - econstructor.
        + eassumption.
        + eapply red1_it_mkLambda_or_LetIn. assumption.
    Qed.

    Lemma red_proj_c :
      forall p c c',
        red Σ Γ c c' ->
        red Σ Γ (tProj p c) (tProj p c').
    Proof.
      intros p c c' h.
      induction h in p |- *.
      - constructor.
      - econstructor.
        + eapply IHh.
        + econstructor. assumption.
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
          intros y z e. cbn in e. destruct y, z. inversion e. eauto.
        } subst.
        constructor.
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
        econstructor.
        + eapply IHh. apply el.
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
      - constructor.
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
        constructor.
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
        econstructor.
        + eapply IHh. apply el.
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
              { clear - o. induction o.
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
      - constructor.
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
                     (λ x : def term, (dname x, dtype x, rarg x))
        ) mfix mfixi ×
        All2 (
          on_Trel_eq (red Σ Γ) dtype
                     (λ x : def term, (dname x, dbody x, rarg x))

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
        constructor.
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
        econstructor.
        + eapply IHh. apply el.
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
      - constructor.
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
        constructor.
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
        econstructor.
        + eapply IHh. apply el.
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
              { clear - o. induction o.
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
      - constructor.
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
                     (λ x : def term, (dname x, dtype x, rarg x))
        ) mfix mfixi ×
        All2 (
          on_Trel_eq (red Σ Γ) dtype
                     (λ x : def term, (dname x, dbody x, rarg x))

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
      induction h.
      - constructor.
      - econstructor ; try eassumption.
        constructor. assumption.
    Qed.

    Lemma red_prod_r :
      forall na A B B',
        red Σ (Γ ,, vass na A) B B' ->
        red Σ Γ (tProd na A B) (tProd na A B').
    Proof.
      intros na A B B' h.
      induction h.
      - constructor.
      - econstructor ; try eassumption.
        constructor. assumption.
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

    Lemma OnOne2_on_Trel_eq_unit :
      forall A (R : A -> A -> Type) l l',
        OnOne2 R l l' ->
        OnOne2 (on_Trel_eq R (fun x => x) (fun x => tt)) l l'.
    Proof.
      intros A R l l' h.
      eapply OnOne2_impl ; eauto.
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
        constructor.
      - set (f := fun x : term => (x, ())) in *.
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
        econstructor.
        + eapply IHh. apply el.
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
      - constructor.
      - eapply red_trans.
        + eapply IHh.
        + eapply red_one_evar. assumption.
    Qed.

    Lemma red_atom t : atom t -> red Σ Γ t t.
    Proof.
      intros. constructor.
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
