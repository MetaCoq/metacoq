(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia Classes.RelationClasses.
From Template
Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
From Equations Require Import Equations NoConfusion.

Import MonadNotation.

(** * Type checker for PCUIC without fuel

  *WIP*

  The idea is to subsume PCUICChecker by providing a fuel-free implementation
  of reduction, conversion and type checking.

  We will follow the same structure, except that we assume normalisation of
  the system. Since we will be using an axiom to justify termination, the checker
  won't run inside Coq, however, its extracted version should correspond more or less
  to the current implementation in ocaml, except it will be certified.

 *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.

End RedFlags.

(* We assume normalisation of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Normalisation.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom Subterm for term.

  Lemma subject_reduction :
    forall {Σ Γ u v A},
      Σ ;;; Γ |- u : A ->
      red1 (fst Σ) Γ u v ->
      Σ ;;; Γ |- v : A.
  Admitted.

  Inductive stack : Type :=
  | Empty
  | App (t : term) (e : stack)
  | Fix (f : mfixpoint term) (n : nat) (args : list term) (e : stack)
  | Case (indn : inductive * nat) (pred : term) (brs : list (nat * term)) (e : stack).

  Fixpoint zipc t stack :=
    match stack with
    | Empty => t
    | App u e => zipc (tApp t u) e
    | Fix f n args e => zipc (tApp (mkApps (tFix f n) args) t) e
    | Case indn pred brs e => zipc (tCase indn pred t brs) e
    end.

  Definition zip (t : term * stack) := zipc (fst t) (snd t).

  (* TODO Tail-rec version *)
  (* Get the arguments out of a stack *)
  Fixpoint decompose_stack π :=
    match π with
    | App u π => let '(l,π) := decompose_stack π in (u :: l, π)
    | _ => ([], π)
    end.

  (* TODO Tail-rec *)
  Fixpoint appstack l π :=
    match l with
    | u :: l => App u (appstack l π)
    | [] => π
    end.

  Lemma decompose_stack_eq :
    forall π l ρ,
      decompose_stack π = (l, ρ) ->
      π = appstack l ρ.
  Proof.
    intros π l ρ eq.
    revert l ρ eq. induction π ; intros l ρ eq.
    - cbn in eq. inversion eq. subst. reflexivity.
    - destruct l.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros. inversion eq.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros l0 s H0 eq. inversion eq. subst.
        cbn. f_equal. eapply IHπ. assumption.
    - cbn in eq. inversion eq. subst. reflexivity.
    - cbn in eq. inversion eq. subst. reflexivity.
  Qed.

  Lemma decompose_stack_not_app :
    forall π l u ρ,
      decompose_stack π = (l, App u ρ) -> False.
  Proof.
    intros π l u ρ eq.
    revert u l ρ eq. induction π ; intros u l ρ eq.
    all: try solve [ cbn in eq ; inversion eq ].
    cbn in eq. revert eq. case_eq (decompose_stack π).
    intros l0 s H0 eq. inversion eq. subst.
    eapply IHπ. eassumption.
  Qed.

  Lemma zipc_appstack :
    forall {t args ρ},
      zipc t (appstack args ρ) = zipc (mkApps t args) ρ.
  Proof.
    intros t args ρ. revert t ρ. induction args ; intros t ρ.
    - cbn. reflexivity.
    - cbn. rewrite IHargs. reflexivity.
  Qed.

  Lemma decompose_stack_appstack :
    forall l ρ,
      decompose_stack (appstack l ρ) =
      (l ++ fst (decompose_stack ρ), snd (decompose_stack ρ)).
  Proof.
    intros l. induction l ; intros ρ.
    - cbn. destruct (decompose_stack ρ). reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Fixpoint decompose_stack_at π n : option (list term * term * stack) :=
    match π with
    | App u π =>
      match n with
      | 0 => ret ([], u, π)
      | S n =>
        r <- decompose_stack_at π n ;;
        let '(l, v, π) := r in
        ret (u :: l, v, π)
      end
    | _ => None
    end.

  Lemma decompose_stack_at_eq :
    forall π n l u ρ,
      decompose_stack_at π n = Some (l,u,ρ) ->
      π = appstack l (App u ρ).
  Proof.
    intros π n l u ρ h. revert n l u ρ h.
    induction π ; intros m l u ρ h.
    all: try solve [ cbn in h ; discriminate ].
    destruct m.
    - cbn in h. inversion h. subst.
      cbn. reflexivity.
    - cbn in h. revert h.
      case_eq (decompose_stack_at π m).
      + intros [[l' v] ρ'] e1 e2.
        inversion e2. subst. clear e2.
        specialize IHπ with (1 := e1). subst.
        cbn. reflexivity.
      + intros H0 h. discriminate.
  Qed.

  Lemma decompose_stack_at_length :
    forall π n l u ρ,
      decompose_stack_at π n = Some (l,u,ρ) ->
      #|l| = n.
  Proof.
    intros π n l u ρ h. revert n l u ρ h.
    induction π ; intros m l u ρ h.
    all: try solve [ cbn in h ; discriminate ].
    destruct m.
    - cbn in h. inversion h. reflexivity.
    - cbn in h. revert h.
      case_eq (decompose_stack_at π m).
      + intros [[l' v] ρ'] e1 e2.
        inversion e2. subst. clear e2.
        specialize IHπ with (1 := e1). subst.
        cbn. reflexivity.
      + intros H0 h. discriminate.
  Qed.

  (*! Notion of term positions and an order on them *)

  Inductive position : term -> Type :=
  | root : forall t, position t
  | app_l : forall u (p : position u) v, position (tApp u v)
  | app_r : forall u v (p : position v), position (tApp u v)
  | case_c : forall indn pr c brs (p : position c), position (tCase indn pr c brs).

  Equations atpos (t : term) (p : position t) : term :=
    atpos ?(t) (root t) := t ;
    atpos ?(tApp u v) (app_l u p v) := atpos u p ;
    atpos ?(tApp u v) (app_r u v p) := atpos v p ;
    atpos ?(tCase indn pr c brs) (case_c indn pr c brs p) := atpos c p.

  Equations poscat t (p : position t) (q : position (atpos t p)) : position t :=
    poscat _ (root t) q := q ;
    poscat _ (app_l u p v) q := app_l u (poscat _ p q) v ;
    poscat _ (app_r u v p) q := app_r u v (poscat _ p q) ;
    poscat _ (case_c indn pr c brs p) q := case_c indn pr c brs (poscat _ p q).

  Arguments root {_}.

  Lemma atpos_poscat :
    forall t p q,
      atpos t (poscat t p q) = atpos (atpos t p) q.
  Proof.
    intros t p q. revert q. induction p ; intros q.
    - reflexivity.
    - rewrite <- IHp. reflexivity.
    - rewrite <- IHp. reflexivity.
    - rewrite <- IHp. reflexivity.
  Qed.

  Notation ex t := (exist _ t _) (only parsing).

  Notation coe h t := (eq_rec_r (fun x => position x) t h).

  (* Set Equations Debug. *)

  Equations stack_position t π : { p : position (zipc t π) | atpos _ p = t } :=
    stack_position t π with π := {
    | Empty => ex root ;
    | App u ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat _ p (coe h (app_l _ root _)))
      } ;
    | Fix f n args ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat _ p (coe h (app_r _ _ root)))
      } ;
    | Case indn pred brs ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat _ p (coe h (case_c _ _ _ _ root)))
      }
    }.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.

  Lemma stack_position_fix :
    forall c mfix idx args ρ,
      ` (stack_position c (Fix mfix idx args ρ)) =
      poscat _ (` (stack_position _ ρ))
             (coe (proj2_sig (stack_position _ ρ)) (app_r _ _ root)).
  Proof.
    intros c mfix idx args ρ.
    simp stack_position.
    replace (stack_position_clause_1 stack_position ρ ρ (tApp (mkApps (tFix mfix idx) args) c))
      with (stack_position (tApp (mkApps (tFix mfix idx) args) c) ρ).
    - case_eq (stack_position (tApp (mkApps (tFix mfix idx) args) c) ρ).
      intros x e H0. cbn. reflexivity.
    - simp stack_position.
  Qed.

  Inductive posR : forall {t}, position t -> position t -> Prop :=
  | posR_app_lr : forall u v pu pv, posR (app_r u v pv) (app_l u pu v)
  | posR_app_l : forall u v p q, posR p q -> posR (app_l u p v) (app_l u q v)
  | posR_app_r : forall u v p q, posR p q -> posR (app_r u v p) (app_r u v q)
  | posR_case_c :
      forall indn pr c brs p q,
        posR p q -> posR (case_c indn pr c brs p) (case_c indn pr c brs q)
  | posR_app_l_root : forall u v p, posR (app_l u p v) root
  | posR_app_r_root : forall u v p, posR (app_r u v p) root
  | posR_case_c_root : forall indn pr c brs p, posR (case_c indn pr c brs p) root.

  Derive Signature for position.
  Derive Signature for posR.

  Lemma existT_position_inj :
    forall u p q,
      existT position u p = existT _ u q ->
      p = q.
  Proof.
    intros u p q eq.
    revert p q eq.
    induction u ; intros q r eq.
    all: try (
      dependent destruction q ;
      dependent destruction r ;
      reflexivity
    ).
    - dependent destruction q.
      + dependent destruction r.
        all: try discriminate.
        reflexivity.
      + dependent destruction r.
        all: try discriminate.
        cbn in eq. inversion eq.
        apply IHu1 in H1. subst. reflexivity.
      + dependent destruction r.
        all: try discriminate.
        cbn in eq. inversion eq.
        apply IHu2 in H1. subst. reflexivity.
    - dependent destruction q.
      + dependent destruction r.
        all: try discriminate.
        reflexivity.
      + dependent destruction r.
        all: try discriminate.
        cbn in eq. inversion eq.
        apply IHu2 in H1. subst. reflexivity.
  Qed.

  Lemma app_l_inj :
    forall u v p q, app_l u p v = app_l u q v -> p = q.
  Proof.
    intros u v p q eq.
    inversion eq.
    eapply existT_position_inj. assumption.
  Qed.

  Lemma app_r_inj :
    forall u v p q, app_r u v p = app_r u v q -> p = q.
  Proof.
    intros u v p q eq.
    inversion eq.
    eapply existT_position_inj. assumption.
  Qed.

  Lemma case_c_inj :
    forall indn pr c brs p q,
      case_c indn pr c brs p = case_c indn pr c brs q ->
      p = q.
  Proof.
    intros indn pr c brs p q eq.
    inversion eq.
    eapply existT_position_inj. assumption.
  Qed.

  Lemma posR_Acc :
    forall t p, Acc (@posR t) p.
  Proof.
    intro t. induction t ; intro q.
    all: try solve [
      dependent destruction q ;
      constructor ; intros r h ;
      dependent destruction h
    ].
    - assert (forall u v p, Acc posR p -> Acc posR (app_r u v p)) as hr.
      { clear. intros u v p h. induction h.
        constructor. intros p h.
        dependent destruction h.
        all: try discriminate.
        apply app_r_inj in H1. subst.
        eapply H0. assumption.
      }
      assert (forall u v p, Acc posR p -> (forall q : position v, Acc posR q) -> Acc posR (app_l u p v)) as hl.
      { clear - hr. intros u v p h ih.
        induction h.
        constructor. intros p h.
        dependent destruction h.
        all: try discriminate.
        - apply app_l_inj in H1. subst.
          eapply hr. apply ih.
        - apply app_l_inj in H1. subst.
          eapply H0. assumption.
      }
      constructor. intros r h.
      dependent destruction h.
      + eapply hr. apply IHt2.
      + eapply hl ; try assumption. apply IHt1.
      + eapply hr. apply IHt2.
      + eapply hl ; try assumption. apply IHt1.
      + eapply hr. apply IHt2.
    - assert (forall indn pr q, Acc posR (case_c indn pr t2 l q)) as hcase.
      { clear q. intros indn pr q.
        specialize (IHt2 q).
        clear - IHt2.
        rename IHt2 into h, t2 into c.
        revert l indn pr.
        induction h.
        intros l indn pr.
        constructor. intros p h.
        dependent destruction h.
        - apply case_c_inj in H1. subst.
          eapply H0. assumption.
        - inversion H1.
      }
      constructor. intros r h.
      dependent destruction h.
      + eapply hcase.
      + eapply hcase.
  Qed.

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  (* Definition R Σ Γ u v := *)
  (*   Subterm.lexprod _ _ (cored Σ Γ) term_subterm (zip u, fst u) (zip v, fst v). *)

  (* Definition R Σ Γ u v := *)
  (*   Subterm.lexprod _ _ (cored Σ Γ) posR *)
  (*                   (zip u, proj1_sig (stack_position (fst u) (snd u))) *)
  (*                   (zip v, proj1_sig (stack_position (fst v) (snd v))). *)

  (* Since there is a dependency in the orders we need to redefine
     the lexicographic order ourselves.
   *)

  Notation "( x ; y )" := (existT _ x y).

  Inductive dlexprod {A} {B : A -> Type} (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop) : sigT B -> sigT B -> Prop :=
  | left_lex : forall x x' y y', leA x x' -> dlexprod leA leB (x;y) (x';y')
  | right_lex : forall x y y', leB x y y' -> dlexprod leA leB (x;y) (x;y').

  (* Lemma acc_dlexprod : *)
  (*   forall A B leA leB x, *)
  (*     Acc leA x -> *)
  (*     well_founded (leB x) -> *)
  (*     forall y, *)
  (*       Acc (leB x) y -> *)
  (*       Acc (@dlexprod A B leA leB) (x;y). *)
  (* Proof. *)
  (*   intros A B leA leB. *)
  (*   induction 1 as [x hx ih1]. *)
  (*   intros hB y. *)
  (*   induction 1 as [y hy ih2]. *)
  (*   constructor. *)
  (*   intros [x' y'] h. simple inversion h. *)
  (*   - intro. inversion H1. inversion H2. subst. *)
  (*     eapply ih1. *)
  (*     + assumption. *)
  (*     + admit. *)
  (*     +  *)

  Lemma acc_dlexprod :
    forall A B leA leB,
      (forall (x : A) (y y' : B x), (x; y) = (x; y') -> y = y') ->
      (forall x, well_founded (leB x)) ->
      forall x,
        Acc leA x ->
        forall y,
          Acc (leB x) y ->
          Acc (@dlexprod A B leA leB) (x;y).
  Proof.
    intros A B leA leB hinj hw.
    induction 1 as [x hx ih1].
    intros y.
    induction 1 as [y hy ih2].
    constructor.
    intros [x' y'] h. simple inversion h.
    - intro hA. inversion H1. inversion H2. subst.
      eapply ih1.
      + assumption.
      + apply hw.
    - intro hB.
      inversion H1. inversion H2. subst.
      eapply ih2.
      apply hinj in H2. subst.
      assumption.
  Qed.

  Definition R Σ Γ u v :=
    dlexprod (cored Σ Γ) (@posR)
             (zip u; proj1_sig (stack_position (fst u) (snd u)))
             (zip v; proj1_sig (stack_position (fst v) (snd v))).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  (* Axiom normalisation : *)
  (*   forall Σ Γ t A, *)
  (*     Σ ;;; Γ |- t : A -> *)
  (*     Acc (cored (fst Σ) Γ) t. *)

  Axiom normalisation :
    forall Σ Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

  Corollary R_Acc_aux :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      Acc (dlexprod (cored (fst Σ) Γ) (@posR))
          (zip t ; proj1_sig (stack_position (fst t) (snd t))).
  Proof.
    intros Σ Γ t h.
    eapply acc_dlexprod.
    - apply existT_position_inj.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - eapply normalisation. eassumption.
    - eapply posR_Acc.
  Qed.

  Derive Signature for Acc.

  Corollary R_Acc :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      Acc (R (fst Σ) Γ) t.
  Proof.
    intros Σ Γ t h.
    pose proof (R_Acc_aux _ _ _ h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H1 ; try reflexivity.
    unfold R in hy. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Σ Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    intros Σ Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction ; eassumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction ; eassumption.
  Qed.

  Definition Req Σ Γ t t' :=
    t = t' \/ R Σ Γ t t'.

  Derive Signature for dlexprod.

  Lemma cored_trans' :
    forall {Σ Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Definition transitive {A} (R : A -> A -> Prop) :=
    forall u v w, R u v -> R v w -> R u w.

  Lemma dlexprod_trans :
    forall A B RA RB,
      transitive RA ->
      (forall x, transitive (RB x)) ->
      transitive (@dlexprod A B RA RB).
  Proof.
    intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
    revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
    - dependent induction h2.
      + left. eapply hA ; eassumption.
      + left. assumption.
    - dependent induction h2.
      + left. assumption.
      + right. eapply hB ; eassumption.
  Qed.

  Lemma posR_trans :
    forall t, transitive (@posR t).
  Proof.
    intros t p q r h1 h2.
    revert r h2. dependent induction h1 ; intros r h2.
    all: try (dependent induction h2 ; discriminate).
    - dependent induction h2.
      all: try discriminate.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
    - dependent induction h2.
      all: try discriminate.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor. eapply IHh1. assumption.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
    - dependent induction h2.
      all: try discriminate.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor. eapply IHh1. assumption.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
    - dependent induction h2.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor. eapply IHh1. assumption.
      + cbn in H0. inversion H0. subst.
        apply existT_position_inj in H2. subst.
        clear H0.
        econstructor.
  Qed.

  Lemma Rtrans :
    forall Σ Γ u v w,
      R Σ Γ u v ->
      R Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Σ Γ}, transitive (Req Σ Γ).
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Σ Γ u v},
      R Σ Γ u v ->
      Req Σ Γ u v.
  Proof.
    intros Σ Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Σ Γ, Reflexive (Req Σ Γ).
  Proof.
    intros Σ Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Σ Γ u v w},
      R Σ Γ u v ->
      Req Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  Lemma red1_context :
    forall Σ Γ t u stack,
      red1 Σ Γ t u ->
      red1 Σ Γ (zip (t, stack)) (zip (u, stack)).
  Admitted.

  Corollary red_context :
    forall Σ Γ t u stack,
      red Σ Γ t u ->
      red Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Corollary cored_context :
    forall Σ Γ t u stack,
      cored Σ Γ t u ->
      cored Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Σ Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Σ' Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma case_reds_discr :
    forall Σ Γ ind p c c' brs,
      red Σ Γ c c' ->
      red Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor.
    - econstructor.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Existing Instance Req_refl.

  Lemma cored_case :
    forall Σ Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma closedn_context :
    forall n t,
      closedn n (zip t) = true ->
      closedn n (fst t).
  Admitted.

  Notation "∥ T ∥" := (squash T) (at level 10).

  Derive Signature for typing.

  Lemma inversion_App :
    forall {Σ Γ u v T},
      Σ ;;; Γ |- tApp u v : T ->
      exists na A B,
        ∥ Σ ;;; Γ |- u : tProd na A B ∥ /\
        ∥ Σ ;;; Γ |- v : A ∥ /\
        (Σ ;;; Γ |- B{ 0 := v } <= T).
  Proof.
    intros Σ' Γ u v T h. dependent induction h.
    - exists na, A, B. split ; [| split].
      + constructor. assumption.
      + constructor. assumption.
      + apply cumul_refl'.
    - destruct IHh1 as [na [A' [B' [? [? ?]]]]].
      exists na, A', B'. split ; [| split].
      + assumption.
      + assumption.
      + eapply cumul_trans ; eassumption.
  Qed.

  Lemma inversion_Rel :
    forall {Σ Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      exists decl,
        ∥ wf_local Σ Γ ∥ /\
        (nth_error Γ n = Some decl) /\
        (Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T).
  Proof.
    intros Σ' Γ n T h.
    dependent induction h.
    - exists decl. split ; [| split].
      + constructor. assumption.
      + assumption.
      + apply cumul_refl'.
    - destruct IHh1 as [decl [? [? ?]]].
      exists decl. split ; [| split].
      + assumption.
      + assumption.
      + eapply cumul_trans ; eassumption.
  Qed.

  (* Weaker inversion lemma *)
  Lemma weak_inversion_Case :
    forall {Σ Γ ind npar pred c brs T},
      Σ ;;; Γ |- tCase (ind, npar) pred c brs : T ->
      exists args u,
        ∥ Σ ;;; Γ |- c : mkApps (tInd ind u) args ∥.
  Proof.
    intros Σ' Γ ind npar pred c brs T h.
    dependent induction h.
    - exists args, u. constructor. assumption.
    - destruct IHh1 as [args [u ?]].
      exists args, u. assumption.
  Qed.

  Lemma welltyped_context :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ Γ (fst t).
  Proof.
    intros Σ' Γ [t π] h.
    destruct h as [A h].
    revert Γ t A h.
    induction π ; intros Γ u A h.
    - cbn. cbn in h. eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] ?]]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] ?]]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      destruct (weak_inversion_Case h) as [? [? [?]]].
      eexists. eassumption.
  Qed.

  Lemma Case_Construct_ind_eq :
    forall {Σ Γ ind ind' npar pred i u brs args},
      welltyped Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
      ind = ind'.
  (* Proof. *)
  (*   intros Σ' Γ ind ind' npar pred i u brs args [A h]. *)
  (*   destruct (weak_inversion_Case h) as [args' [ui [hh]]]. *)
  (*   clear - hh. induction args. *)
  (*   - cbn in hh. dependent induction hh. *)
  (*     + unfold type_of_constructor in H0. *)
  (*       cbn in H0. induction args'. *)
  (*       * cbn in H0. admit. *)
  (*       * eapply IHargs'. cbn in H0. *)
  Admitted.

  (* Lemma weak_inversion_Construct : *)
  (*   forall {Σ Γ ind i u T}, *)
  (*     Σ ;;; Γ |- tConstruct ind i u : T -> *)
  (*     exists mdecl idecl cdecl, *)
  (*       Σ ;;; Γ |- type_of_constructor mdecl cdecl (ind, i) u <= T. *)

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e.
    - cbn in e. assumption.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
  Qed.

  Lemma posR_poscat :
    forall t p q, q <> @root (atpos t p) -> posR (poscat t p q) p.
  Proof.
    clear. intros t p q h.
    funelim (poscat t p q).
    - revert q h.
      assert (forall q : position t, q <> root t -> posR q (root t)) as h.
      { intros q h.
        dependent destruction q.
        - exfalso. apply h. reflexivity.
        - econstructor.
        - econstructor.
        - econstructor.
      }
      apply h.
    - revert u v p q H h.
      assert (forall u v p (q : position (atpos u p)),
                 (q <> root _ -> posR (poscat _ p q) p) ->
                 q <> root _ ->
                 posR (app_l u (poscat u p q) v) (app_l u p v)
             ).
      { intros u v p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
    - revert u0 v0 p0 q H h.
      assert (forall u v p (q : position (atpos v p)),
                 (q <> root _ -> posR (poscat v p q) p) ->
                 q <> root _ ->
                 posR (app_r u v (poscat v p q)) (app_r u v p)
             ).
      { intros u v p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
    - revert indn pr c p1 q H h.
      assert (
          forall indn pr c p (q : position (atpos c p)),
            (q <> root _ -> posR (poscat c p q) p) ->
            q <> root _ ->
            posR (case_c indn pr c brs (poscat c p q)) (case_c indn pr c brs p)
        ).
      { intros indn pr c p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
  Qed.

  Notation "( x ; y )" := (existT _ x y).

  (* Lemma right_lex_eq : *)
  (*   forall {A B leA} {leB : forall x : A, B x -> B x -> Prop} {x x' y y'}, *)
  (*     x = x' -> *)
  (*     leB x y y' -> *)
  (*     @dlexprod A B leA leB (x;y) (x';y'). *)

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

  (* Definition Pr (t' : term * stack) (π : stack) := True. *)

  (* Definition Pr (t' : term * stack) π := *)
  (*   forall indn c args ρ, *)
  (*     π = Case indn c args ρ -> *)
  (*     let '(args', ρ') := decompose_stack (snd t') in *)
  (*     ρ' = Case indn c args ρ. *)

  Definition Pr (t' : term * stack) π :=
    forall indn c args ρ,
      let '(l, θ) := decompose_stack π in
      θ = Case indn c args ρ ->
      let '(args', ρ') := decompose_stack (snd t') in
      ρ' = Case indn c args ρ.

  Notation givePr := (fun indn c args ρ (* e *) => _) (only parsing).
  (* Notation givePr := (_) (only parsing). *)
  (* Notation givePr := (I) (only parsing). *)

  (* Definition Pr' (t' : term * stack) π := *)
  (*   forall f n args ρ, *)
  (*     snd (decompose_stack π) = Fix f n args ρ -> *)
  (*     snd (decompose_stack (snd t')) = Fix f n args ρ. *)

  Definition Pr' (t' : term * stack) π :=
    forall f n args ρ,
      let '(l, θ) := decompose_stack π in
      θ = Fix f n args ρ ->
      let '(l', θ') := decompose_stack (snd t') in
      θ' = Fix f n args ρ.

  (* Notation givePr' := (fun f n args ρ e => _) (only parsing). *)
  Notation givePr' := (fun f n args ρ => _) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist _ res (conj prf (conj h h'))) := reduce t π smaller in
     exist _ res (conj (Req_trans _ _ _ _ (R_to_Req smaller)) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist _ (t,π) (conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Ltac dealPr_Pr' P :=
    lazymatch goal with
    | h : P (?t,?s) ?π |- let '(_,_) := decompose_stack ?π in _ =>
      let e := fresh "e" in
      case_eq (decompose_stack π) ; intros ? ? e ? ; subst ;
      unfold P in h ; rewrite e in h ;
      specialize h with (1 := eq_refl) ;
      cbn in h ; assumption
    end.

  Ltac dealPr := dealPr_Pr' Pr.
  Ltac dealPr' := dealPr_Pr' Pr'.

  Ltac dealDecompose :=
    lazymatch goal with
    | |- let '(_,_) := decompose_stack ?π in _ =>
      case_eq (decompose_stack π) ; intros ; assumption
    end.

  Ltac obTac :=
    program_simpl ;
    try reflexivity ;
    try dealDecompose ;
    try dealPr ;
    try dealPr'.

  Obligation Tactic := obTac.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', R (fst Σ) Γ (t',π') (t,π) -> { t'' : term * stack | Req (fst Σ) Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' π' })
    : { t' : term * stack | Req (fst Σ) Γ t' (t,π) /\ Pr t' π /\ Pr' t' π } :=

    _reduce_stack Γ (tRel c) π h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error Γ c) := {
      | @exist None eq := ! ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := give (tRel c) π ;
        | @exist (Some b) H := rec reduce (lift0 (S c) b) π
        }
      } ;
    | false := give (tRel c) π
    } ;

    _reduce_stack Γ (tLetIn A b B c) π h reduce with RedFlags.zeta flags := {
    | true := rec reduce (subst10 b c) π ;
    | false := give (tLetIn A b B c) π
    } ;

    _reduce_stack Γ (tConst c u) π h reduce with RedFlags.delta flags := {
    | true with inspect (lookup_env (fst Σ) c) := {
      | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
        let body' := subst_instance_constr u body in
        rec reduce body' π ;
      | @exist _ eq := give (tConst c u) π
      } ;
    | _ := give (tConst c u) π
    } ;

    _reduce_stack Γ (tApp f a) π h reduce :=
      rec reduce f (App a π) ;

    _reduce_stack Γ (tLambda na A t) (App a args) h reduce with RedFlags.beta flags := {
    | true := rec reduce (subst10 a t) args ;
    | false := give (tLambda na A t) (App a args)
    } ;

    _reduce_stack Γ (tFix mfix idx) π h reduce with RedFlags.fix_ flags := {
    | true with inspect (unfold_fix mfix idx) := {
      | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
        | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix mfix idx args ρ) _) := {
          | @exist (@exist (tConstruct ind n ui, ρ') prf) eq3 with inspect (decompose_stack ρ') := {
            | @exist (l, θ) eq4 :=
              rec reduce fn (appstack args (App (mkApps (tConstruct ind n ui) l) ρ))
            } ;
          | _ := give (tFix mfix idx) π
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | _ := give (tFix mfix idx) π
      } ;
    | false := give (tFix mfix idx) π
    } ;

    (* Nothing special seems to be done for Π-types. *)
    (* _reduce_stack Γ (tProd na A B) *)

    _reduce_stack Γ (tCase (ind, par) p c brs) π h reduce with RedFlags.iota flags := {
    | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
      | @exist (@exist (tConstruct ind' c' _, π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' := rec reduce (iota_red par c' args brs) π
        } ;
      | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' := give (tCase (ind, par) p (mkApps t args) brs) π
        }
      } ;
    | false := give (tCase (ind, par) p c brs) π
    } ;

    _reduce_stack Γ t π h reduce := give t π.
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    pose proof (welltyped_context _ _ _ h) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc. revert c hc eq.
    induction Γ ; intros c hc eq.
    - destruct hc as [A h].
      destruct (inversion_Rel h) as [? [[?] [e ?]]].
      rewrite e in eq. discriminate eq.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption.
        destruct hc as [A h].
        destruct (inversion_Rel h) as [? [[?] [e ?]]].
        cbn in e. rewrite e in eq. discriminate.
  Qed.
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros l θ e1 e2. subst.
    unfold Pr in h.
    rewrite e1 in h. specialize h with (1 := eq_refl).
    cbn in h. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros l θ e1 e2. subst.
    unfold Pr' in h'.
    rewrite e1 in h'. specialize h' with (1 := eq_refl).
    cbn in h'. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros. assumption.
  Qed.
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.
  Next Obligation.
    right.
    cbn.
    simp stack_position.
    destruct stack_position_clause_1. cbn.
    apply posR_poscat. intro bot. clear - bot.
    revert x e bot.
    generalize (zipc (tApp f a)).
    intros t x.
    generalize (atpos (t π) x).
    intros t0 e bot. subst. cbn in bot. discriminate.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack π).
    intros l θ e1 e2. subst.
    unfold Pr in h. cbn in h. rewrite e1 in h.
    specialize h with (1 := eq_refl). assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack π).
    intros l θ e1 e2. subst.
    unfold Pr' in h'. cbn in h'. rewrite e1 in h'.
    specialize h' with (1 := eq_refl). assumption.
  Qed.
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    (* Should be a lemma! *)
    - unfold declared_constant. rewrite <- eq. f_equal.
      f_equal. clear - eq.
      revert c wildcard wildcard0 body wildcard1 eq.
      set (Σ' := fst Σ). clearbody Σ'. clear Σ. rename Σ' into Σ.
      induction Σ ; intros c na t body univ eq.
      + cbn in eq. discriminate.
      + cbn in eq. revert eq.
        case_eq (ident_eq c (global_decl_ident a)).
        * intros e eq. inversion eq. subst. clear eq.
          cbn in e. revert e. destruct (ident_eq_spec c na) ; easy.
        * intros e eq. eapply IHg. eassumption.
    - cbn. reflexivity.
  Qed.
  Next Obligation.
    right. simp stack_position.
    destruct stack_position_clause_1. cbn.
    apply posR_poscat. clear.
    intro bot.
    revert x e bot. cbn.
    match goal with
    | |- forall x : position ?t, _ =>
      generalize t
    end.
    intros t x.
    generalize (atpos t x).
    intros t' e bot.
    subst. cbn in bot.
    discriminate.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    clear - prf' r p0. unfold Pr in p0.
    cbn in p0.
    specialize p0 with (1 := eq_refl).
    rewrite <- prf' in p0. subst.
    symmetry in prf'.
    pose proof (decompose_stack_eq _ _ _ prf'). subst.
    subst t.
    destruct r.
    - inversion H. subst. clear H.
      destruct args.
      + cbn. reflexivity.
      + cbn in H2. discriminate H2.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H1. cbn in H1.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        rewrite zipc_appstack in H5. cbn in H5.
        apply zipc_inj in H5. inversion H5. subst. reflexivity.
  Qed.
  Next Obligation.
    unfold Pr in p0. cbn in p0.
    specialize p0 with (1 := eq_refl) as hh.
    rewrite <- prf' in hh. subst.
    eapply R_Req_R.
    - econstructor. econstructor. eapply red1_context.
      eapply red_iota.
    - instantiate (4 := ind'). instantiate (2 := p).
      instantiate (1 := wildcard).
      destruct r.
      + inversion e.
        subst.
        cbn in prf'. inversion prf'. subst. clear prf'.
        cbn.
        assert (ind = ind').
        { clear - h flags.
          apply welltyped_context in h.
          cbn in h.
          apply (Case_Construct_ind_eq (args := [])) in h.
          assumption.
        } subst.
        reflexivity.
      + clear eq. dependent destruction r.
        * cbn in H0.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H0.
          cbn in H0.
          right. econstructor.
          lazymatch goal with
          | h : cored _ _ ?t _ |- _ =>
            assert (welltyped Σ Γ t) as h'
          end.
          { clear - h H0 flags.
            eapply cored_welltyped ; eassumption.
          }
          assert (ind = ind').
          { clear - h' flags.
            zip fold in h'.
            apply welltyped_context in h'.
            cbn in h'.
            apply Case_Construct_ind_eq in h'.
            assumption.
          } subst.
          exact H0.
        * cbn in H1. inversion H1. subst. clear H1.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H3. cbn in H3.
          apply zipc_inj in H3.
          inversion H3. subst.
          assert (ind = ind').
          { clear - h flags.
            apply welltyped_context in h.
            cbn in h.
            apply Case_Construct_ind_eq in h.
            assumption.
          } subst.
          reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H0. subst. subst t.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      specialize p0 with (1 := eq_refl).
      rewrite <- prf' in p0. subst. subst t.
      dependent destruction H0.
      + cbn in H0. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H0. cbn in H0.
        right. econstructor. assumption.
      + cbn in H1. inversion H1. subst. clear H1.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H3. cbn in H3.
        apply zipc_inj in H3. inversion H3. subst.
        reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H0. subst. subst t.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      specialize p0 with (1 := eq_refl).
      rewrite <- prf' in p0. subst. subst t.
      dependent destruction H0.
      + cbn in H0. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H0. cbn in H0.
        right. econstructor. assumption.
      + cbn in H1. inversion H1. subst. clear H1.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H3. cbn in H3.
        apply zipc_inj in H3. inversion H3. subst.
        reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H0. subst. subst t.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      specialize p0 with (1 := eq_refl).
      rewrite <- prf' in p0. subst. subst t.
      dependent destruction H0.
      + cbn in H0. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H0. cbn in H0.
        right. econstructor. assumption.
      + cbn in H1. inversion H1. subst. clear H1.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H3. cbn in H3.
        apply zipc_inj in H3. inversion H3. subst.
        reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H0. subst. subst t.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      specialize p0 with (1 := eq_refl).
      rewrite <- prf' in p0. subst. subst t.
      dependent destruction H0.
      + cbn in H0. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H0. cbn in H0.
        right. econstructor. assumption.
      + cbn in H1. inversion H1. subst. clear H1.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H3. cbn in H3.
        apply zipc_inj in H3. inversion H3. subst.
        reflexivity.
  Qed.
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    unfold R. cbn.
    (* Induction on args maube? *)

    (* Unfortunately, this is probably wrong with the order as it is.
       Indeed, we have p.app_r < p.app_l, which is fine when considering
       fix c, but not for (fix x) c which requires p.app_r < p.app_l.app_l.
       Actually it seems it is the case. We compare the heads first, no matter
       how deep we go afterwards.

       As such, induction on args might be a safe bet.
       I hope I don't have to remove dependency in order to remove
       unwanted transports...

       Maybe a lemma to say (coe h app_r p) < app_l q or something of
       the sort (might even be usefyl those times I did generalize).

       destruct args might actually be enough, since we only need to know
       we're going left or right.

       Maybe a lemma stackpos (c, fix) = poscat (fst _) (coe (snd _) _)
     *)

    (* rewrite zipc_appstack. cbn. *)




    simp stack_position.

    destruct stack_position_clause_1 as [p hp]. cbn.
    destruct stack_position_clause_1 as [q hq]. cbn.
    revert p hp q hq.
    rewrite zipc_appstack.
    intros p hp q hq.
    cbn. right.

    (* case_eq (stack_position_clause_1 stack_position (appstack args (App c ρ)) *)
    (*                                  (appstack args (App c ρ)) (tFix mfix idx)). *)
    (* cbn. *)
    (* intros p hp ep. *)
    (* case_eq (stack_position_clause_1 stack_position ρ ρ *)
    (*                                  (tApp (mkApps (tFix mfix idx) args) c)). *)
    (* cbn. *)
    (* intros q hq eq. *)
    (* revert p hp ep q hq eq. *)
    (* Fail rewrite zipc_appstack. *)

    (* Perhaps do we need to do case_eq instead of destruct? *)
    (* This way we could relate p and q. *)
    (* Maybe a case analysis on p and/or q will prove sufficient. *)
    dependent destruction q.
    - admit.
    - inversion H0.
  Admitted.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H0 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H1. subst.
        destruct ll.
        * cbn in H4. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H4. discriminate H4.
      + dependent destruction H1.
        * cbn in H1. rewrite 2!zipc_appstack in H1.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr' in p0. cbn in p0.
             specialize p0 with (1 := eq_refl).
             rewrite e1 in p0. subst.
             cbn in H1.
             clear - H1.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H1 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * (* This case is not really worth doing as the definition of R is
             expected to change. *)
          cbn in H1. cbn in H2. inversion H2. subst. clear H2.
          admit.
  Admitted.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e1 e2. subst.
    cbn. unfold Pr in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l' θ' e.
    rewrite e in h. cbn in h.
    pose proof (decompose_stack_eq _ _ _ e). subst.

    clear eq3 smaller. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack in e1. cbn in e1.
    rewrite e in e1. cbn in e1.
    inversion e1. subst.

    specialize h with (1 := eq_refl).
    assumption.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e1 e2. subst.
    cbn. unfold Pr' in h'.
    rewrite decompose_stack_appstack in h'. cbn in h'.
    case_eq (decompose_stack ρ). intros l' θ' e.
    rewrite e in h'. cbn in h'.
    pose proof (decompose_stack_eq _ _ _ e). subst.

    clear eq3 smaller. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack in e1. cbn in e1.
    rewrite e in e1. cbn in e1.
    inversion e1. subst.

    specialize h' with (1 := eq_refl).
    assumption.
  Qed.

  Lemma closedn_cored :
    forall Σ Γ u v,
      cored Σ Γ v u ->
      closedn #|Γ| u = true ->
      closedn #|Γ| v = true.
  Admitted.

  Lemma closedn_typed :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      closedn #|Γ| t = true.
  Admitted.

  Equations reduce_stack (Γ : context) (t A : term) (π : stack)
           (h : welltyped Σ Γ (zip (t,π))) : term * stack :=
    reduce_stack Γ t A π h :=
      let '(exist _ ts _) :=
          Fix_F (R := R (fst Σ) Γ)
                (fun x => welltyped Σ Γ (zip x) -> { t' : term * stack | Req (fst Σ) Γ t' x /\ Pr t' (snd x) /\ Pr' t' (snd x) })
                (fun t' f => _) (x := (t, π)) _ _
      in ts.
  Next Obligation.
    intro hc.
    eapply _reduce_stack.
    - assumption.
    - intros t' π' h'.
      eapply f.
      + assumption.
      + simple inversion h'.
        * inversion H1. inversion H2. subst. clear H1 H2.
          intros H0.
          eapply cored_welltyped ; eassumption.
        * inversion H1. inversion H2. subst. clear H1 H2.
          intros H0. rewrite H5. assumption.
  Qed.
  Next Obligation.
    eapply R_Acc. eassumption.
  Qed.

End Reduce.