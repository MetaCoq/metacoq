(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia Classes.RelationClasses.
From Template
Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICReflect
                          PCUICLiftSubst PCUICUnivSubst PCUICTyping
                          PCUICPosition.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Import MonadNotation.

(** * Reduction machine for PCUIC without fuel

  We subsume the reduction machine of PCUICChecker without relying on fuel.
  Instead we assume strong normalisation of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the ocaml implementation.

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

Notation "∥ T ∥" := (squash T) (at level 10).

Inductive stack : Type :=
| Empty
| App (t : term) (π : stack)
| Fix (f : mfixpoint term) (n : nat) (args : list term) (π : stack)
| Case (indn : inductive * nat) (p : term) (brs : list (nat * term)) (π : stack)
| Prod_l (na : name) (B : term) (π : stack)
| Prod_r (na : name) (A : term) (π : stack).

Notation "'ε'" := (Empty).

Derive NoConfusion NoConfusionHom EqDec for stack.

Instance reflect_stack : ReflectEq stack :=
  let h := EqDec_ReflectEq stack in _.

Fixpoint zipc t stack :=
  match stack with
  | ε => t
  | App u π => zipc (tApp t u) π
  | Fix f n args π => zipc (tApp (mkApps (tFix f n) args) t) π
  | Case indn pred brs π => zipc (tCase indn pred t brs) π
  | Prod_l na B π => zipc (tProd na t B) π
  | Prod_r na A π => zipc (tProd na A t) π
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
  all: try solve [ cbn in eq ; inversion eq ; subst ; reflexivity ].
  destruct l.
  - cbn in eq. revert eq. case_eq (decompose_stack π).
    intros. inversion eq.
  - cbn in eq. revert eq. case_eq (decompose_stack π).
    intros l0 s H0 eq. inversion eq. subst.
    cbn. f_equal. eapply IHπ. assumption.
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

Fixpoint stack_context π : context :=
  match π with
  | ε => []
  | App u π => stack_context π
  | Fix f n args π => stack_context π
  | Case indn pred brs π => stack_context π
  | Prod_l na B π => stack_context π
  | Prod_r na A π => stack_context π ,, vass na A
  end.

Lemma stack_context_appstack :
  forall {π args},
    stack_context (appstack args π) = stack_context π.
Proof.
  intros π args.
  revert π. induction args ; intros π.
  - reflexivity.
  - simpl. apply IHargs.
Qed.

(* We assume normalisation of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Normalisation.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.

  Lemma subject_reduction :
    forall {Σ Γ u v A},
      Σ ;;; Γ |- u : A ->
      red1 (fst Σ) Γ u v ->
      Σ ;;; Γ |- v : A.
  Admitted.

  Set Equations With UIP.

  (* IDEA Perhaps we can handle Prod_r if we were to add stack_context.

     red1_context would update to this.
       Lemma red1_context :
    forall Σ Γ t u π,
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zip (t, π)) (zip (u, π)).

      This is painful as it would probably require some change in reduce_stack.
      That would mean we could also see stacks a copositions and put them in
      their own file or Position.

      Careful, stack_context is reversed (rev_map).
   *)

  Fixpoint stack_position π : position :=
    match π with
    | ε => []
    | App u ρ => stack_position ρ ++ [ app_l ]
    | Fix f n args ρ => stack_position ρ ++ [ app_r ]
    | Case indn pred brs ρ => stack_position ρ ++ [ case_c ]
    | Prod_l na B ρ => stack_position ρ ++ [ prod_l ]
    | Prod_r na A ρ => stack_position ρ ++ [ prod_r ]
    end.

  Lemma stack_position_atpos :
    forall t π, atpos (zipc t π) (stack_position π) = t.
  Proof.
    intros t π. revert t. induction π ; intros u.
    all: solve [ cbn ; rewrite ?poscat_atpos, ?IHπ ; reflexivity ].
  Qed.

  Lemma stack_position_valid :
    forall t π, validpos (zipc t π) (stack_position π).
  Proof.
    intros t π. revert t. induction π ; intros u.
    all: try solve [
      cbn ; eapply poscat_valid ; [
        eapply IHπ
      | rewrite stack_position_atpos ; reflexivity
      ]
    ].
    reflexivity.
  Qed.

  Definition stack_pos t π : pos (zipc t π) :=
    exist (stack_position π) (stack_position_valid t π).

  Fixpoint list_make {A} n x : list A :=
    match n with
    | 0 => []
    | S n => x :: list_make n x
    end.

  Lemma list_make_app_r :
    forall A n (x : A),
      x :: list_make n x = list_make n x ++ [x].
  Proof.
    intros A n x. revert x.
    induction n ; intro x.
    - reflexivity.
    - cbn. rewrite IHn. reflexivity.
  Qed.

  Lemma stack_position_appstack :
    forall args ρ,
      stack_position (appstack args ρ) =
      stack_position ρ ++ list_make #|args| app_l.
  Proof.
    intros args ρ. revert ρ.
    induction args as [| u args ih ] ; intros ρ.
    - cbn. rewrite app_nil_r. reflexivity.
    - cbn. rewrite ih. rewrite <- app_assoc.
      rewrite list_make_app_r. reflexivity.
  Qed.

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Notation "( x ; y )" := (existT _ x y).

  (* TODO Move somewhere else *)
  (* Dependent lexicographic order *)
  Inductive dlexprod {A} {B : A -> Type}
            (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop)
    : sigT B -> sigT B -> Prop :=
  | left_lex : forall x x' y y', leA x x' -> dlexprod leA leB (x;y) (x';y')
  | right_lex : forall x y y', leB x y y' -> dlexprod leA leB (x;y) (x;y').

  Derive Signature for dlexprod.

  Lemma acc_dlexprod :
    forall A B leA leB,
      (forall x, well_founded (leB x)) ->
      forall x,
        Acc leA x ->
        forall y,
          Acc (leB x) y ->
          Acc (@dlexprod A B leA leB) (x;y).
  Proof.
    intros A B leA leB hw.
    induction 1 as [x hx ih1].
    intros y.
    induction 1 as [y hy ih2].
    constructor.
    intros [x' y'] h. simple inversion h.
    - intro hA. inversion H1. inversion H2. subst.
      eapply ih1.
      + assumption.
      + apply hw.
    - intro hB. rewrite <- H1.
      pose proof (projT2_eq H2) as p2.
      set (projT1_eq H2) as p1 in *; cbn in p1.
      destruct p1; cbn in p2; destruct p2.
      eapply ih2. assumption.
  Qed.

  Lemma dlexprod_Acc :
    forall A B leA leB,
      (forall x, well_founded (leB x)) ->
      forall x y,
        Acc leA x ->
        Acc (@dlexprod A B leA leB) (x;y).
  Proof.
    intros A B leA leB hB x y hA.
    eapply acc_dlexprod ; try assumption.
    apply hB.
  Qed.

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

  Definition R_aux Σ Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Σ Γ u v :=
    R_aux Σ Γ (zip u ; stack_pos (fst u) (snd u))
              (zip v ; stack_pos (fst v) (snd v)).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Axiom normalisation :
    forall Σ Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

  Corollary R_Acc_aux :
    forall Σ Γ t p,
      welltyped Σ Γ t ->
      Acc (R_aux Σ Γ) (t ; p).
  Proof.
    intros Σ Γ t p h.
    eapply dlexprod_Acc.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - eapply normalisation. eassumption.
  Qed.

  Derive Signature for Acc.

  Corollary R_Acc :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      Acc (R (fst Σ) Γ) t.
  Proof.
    intros Σ Γ t h.
    pose proof (R_Acc_aux _ _ _ (stack_pos (fst t) (snd t)) h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H1 ; try reflexivity.
    unfold R in hy. assumption.
  Qed.

  Lemma R_positionR :
    forall Σ Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Σ Γ (t1 ; p1) (t2 ; p2).
  Proof.
    intros Σ Γ t1 t2 p1 p2 e h.
    subst. right. assumption.
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

  (* Notation coe h t := (eq_rec_r (fun x => position x) t h). *)

  Lemma red1_context :
    forall Γ t u π,
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h.
    cbn. revert t u h.
    induction π ; intros u v h.
    all: try solve [ cbn ; apply IHπ ; constructor ; assumption ].
    cbn. assumption.
  Qed.

  Corollary red_context :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Corollary cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
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

  Derive Signature for typing.

  Lemma inversion_App :
    forall {Σ Γ u v T},
      Σ ;;; Γ |- tApp u v : T ->
      exists na A B,
        ∥ Σ ;;; Γ |- u : tProd na A B ∥ /\
        ∥ Σ ;;; Γ |- v : A ∥ /\
        ∥ Σ ;;; Γ |- B{ 0 := v } <= T ∥.
  Proof.
    intros Σ' Γ u v T h. dependent induction h.
    - exists na, A, B. split ; [| split].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [na [A' [B' [? [? [?]]]]]].
      exists na, A', B'. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma inversion_Rel :
    forall {Σ Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      exists decl,
        ∥ wf_local Σ Γ ∥ /\
        (nth_error Γ n = Some decl) /\
        ∥ Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T ∥.
  Proof.
    intros Σ' Γ n T h.
    dependent induction h.
    - exists decl. split ; [| split].
      + constructor. assumption.
      + assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [decl [? [? [?]]]].
      exists decl. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
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
    - destruct IHh as [args [u ?]].
      exists args, u. assumption.
  Qed.

  Lemma inversion_Lambda :
    forall {Σ Γ na A t T},
      Σ ;;; Γ |- tLambda na A t : T ->
      exists s1 B,
        ∥ Σ ;;; Γ |- A : tSort s1 ∥ /\
        ∥ Σ ;;; Γ ,, vass na A |- t : B ∥ /\
        ∥ Σ ;;; Γ |- tProd na A B <= T ∥.
  Proof.
    intros Σ' Γ na A t T h. dependent induction h.
    - exists s1, bty. split ; [| split].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [s1 [B' [? [? [?]]]]].
      exists s1, B'. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma inversion_Prod :
    forall {Σ Γ na A B T},
      Σ ;;; Γ |- tProd na A B : T ->
      exists s1 s2,
        ∥ Σ ;;; Γ |- A : tSort s1 ∥ /\
        ∥ Σ ;;; Γ ,, vass na A |- B : tSort s2 ∥ /\
        ∥ Σ ;;; Γ |- tSort (Universe.sort_of_product s1 s2) <= T ∥.
  Proof.
    intros Σ' Γ na A B T h. dependent induction h.
    - exists s1, s2. split ; [| split].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [s1 [s2 [? [? [?]]]]].
      exists s1, s2. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    intros Γ [t π] h.
    destruct h as [T h].
    revert Γ t T h.
    induction π ; intros Γ u T h.
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
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      destruct (inversion_Prod h) as [s1 [s2 [[?] [[?] [?]]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      destruct (inversion_Prod h) as [s1 [s2 [[?] [[?] [?]]]]].
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
  (*       cbn in H0. (* clear - H0. *) induction args'. *)
  (*       * cbn in H0. admit. *)
  (*       * eapply IHargs'. cbn in H0. *)
  Admitted.

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e.
    all: try solve [ cbn in e ; apply IHπ in e ; inversion e ; reflexivity ].
    cbn in e. assumption.
  Qed.

  Notation "( x ; y )" := (existT _ x y).

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Notation givePr := (_) (only parsing).

  Definition isStackApp π :=
    match π with
    | App _ _ => true
    | _ => false
    end.

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Notation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist res (conj prf (conj h (conj h1 h2)))) := reduce t π smaller in
     exist res (conj (Req_trans _ _ _ _ (R_to_Req smaller)) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist (t,π) (conj _ (conj givePr givePr'))) (only parsing).

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

  (* Show Obligation Tactic. *)

  Ltac obTac :=
    (* program_simpl ; *)
    program_simplify ;
    Tactics.equations_simpl ;
    try program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Set :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', R (fst Σ) Γ (t',π') (t,π) -> { t'' : term * stack | Req (fst Σ) Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | Req (fst Σ) Γ t' (t,π) /\ Pr t' π /\ Pr' t' } :=

    _reduce_stack Γ (tRel c) π h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error (Γ ,,, stack_context π) c) := {
      | @exist None eq := False_rect _ _ ;
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

    _reduce_stack Γ (tLambda na A t) (App a args) h reduce with inspect (RedFlags.beta flags) := {
    | @exist true eq1 := rec reduce (subst10 a t) args ;
    | @exist false eq1 := give (tLambda na A t) (App a args)
    } ;

    _reduce_stack Γ (tFix mfix idx) π h reduce with RedFlags.fix_ flags := {
    | true with inspect (unfold_fix mfix idx) := {
      | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
        | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix mfix idx args ρ) _) := {
          | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
            | view_construct ind n ui with inspect (decompose_stack ρ') := {
              | @exist (l, θ) eq4 :=
                rec reduce fn (appstack args (App (mkApps (tConstruct ind n ui) l) ρ))
              } ;
            | view_other t ht := give (tFix mfix idx) π
            }
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | _ := give (tFix mfix idx) π
      } ;
    | false := give (tFix mfix idx) π
    } ;

    _reduce_stack Γ (tCase (ind, par) p c brs) π h reduce with RedFlags.iota flags := {
    | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
      | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' with construct_viewc t := {
          | view_construct ind' c' _ := rec reduce (iota_red par c' args brs) π ;
          | view_other t ht := give (tCase (ind, par) p (mkApps t args) brs) π
          }
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
    pose proof (welltyped_context _ _ h) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc. revert c hc eq.
    generalize (Γ ,,, stack_context π) as Δ. clear Γ π.
    intro Γ.
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
    unfold Pr. cbn.
    case_eq (decompose_stack args). intros l ρ e.
    cbn. unfold Pr in h. rewrite e in h. cbn in h.
    assumption.
  Qed.
  Next Obligation.
    rewrite β in eq1. discriminate.
  Qed.
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.
  Next Obligation.
    right.
    cbn. unfold posR. cbn.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. rewrite e in h. cbn in h.
    assumption.
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
    right. unfold posR. cbn.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
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
    - inversion H0. subst.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      rewrite <- prf' in p0. cbn in p0. subst.
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
    eapply R_positionR.
    - cbn. rewrite zipc_appstack. cbn. reflexivity.
    - cbn. rewrite stack_position_appstack. cbn.
      rewrite <- app_assoc.
      eapply positionR_poscat.
      constructor.
  Qed.
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
        unfold isConstruct_app.
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
             unfold Pr in p. cbn in p.
             rewrite e1 in p. cbn in p. subst.
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
        * cbn in H2. inversion H2.
          rewrite 2!zipc_appstack in H4.
          unfold Pr in p. cbn in p.
          rewrite e1 in p. cbn in p. subst.
          cbn in H4. rewrite zipc_appstack in H4.
          apply zipc_inj in H4.
          apply mkApps_inj in H4.
          inversion H4. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l1 ρ1 e.
    rewrite e in h. cbn in h. subst.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack. cbn.
    rewrite e. cbn. reflexivity.
  Qed.

  Equations reduce_stack_full (Γ : context) (t : term) (π : stack)
           (h : welltyped Σ Γ (zip (t,π))) : { t' : term * stack | Req (fst Σ) Γ t' (t, π) /\ Pr t' π /\ Pr' t' } :=
    reduce_stack_full Γ t π h :=
      Fix_F (R := R (fst Σ) Γ)
            (fun x => welltyped Σ Γ (zip x) -> { t' : term * stack | Req (fst Σ) Γ t' x /\ Pr t' (snd x) /\ Pr' t' })
            (fun t' f => _) (x := (t, π)) _ _.
  Next Obligation.
    eapply _reduce_stack.
    - assumption.
    - intros t' π' h'.
      eapply f.
      + assumption.
      + simple inversion h'.
        * cbn in H2. cbn in H3.
          inversion H2. subst. inversion H3. subst. clear H2 H3.
          intros.
          eapply cored_welltyped ; eassumption.
        * cbn in H2. cbn in H3.
          inversion H2. subst. inversion H3. subst. clear H2 H3.
          intros. cbn. rewrite H4. assumption.
  Qed.
  Next Obligation.
    eapply R_Acc. eassumption.
  Qed.

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Theorem reduce_stack_sound :
    forall Γ t π h,
      ∥ red (fst Σ) Γ (zip (t, π)) (zip (reduce_stack Γ t π h)) ∥.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]].
    dependent destruction r.
    - noconf H0. constructor. constructor.
    - rename H0 into r. clear - flags r.
      dependent destruction r.
      + cbn in H0. cbn in H1.
        inversion H0. subst. inversion H1. subst.
        noconf H4. noconf H5. subst. clear H0 H1.
        revert H. cbn.
        generalize (zipc t' π').
        generalize (zipc t π).
        intros u v. clear - flags.
        intro r.
        induction r.
        * constructor. econstructor ; try eassumption.
          constructor.
        * destruct IHr as [ih].
          constructor. econstructor ; eassumption.
      + cbn in H0, H1. inversion H0. inversion H1.
        subst. cbn. rewrite H5.
        constructor. constructor.
  Qed.

  Lemma reduce_stack_Req :
    forall Γ t π h,
      Req (fst Σ) Γ (reduce_stack Γ t π h) (t, π).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]].
    assumption.
  Qed.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p p']]].
    unfold Pr in p. symmetry. assumption.
  Qed.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]].
    assumption.
  Qed.

  (* I would have liked better a lemma concluding the stack is empty.
     Unfortunately, it is not correct as we only match on tLambda and
     App together.
     Typing might get the better of it though.
   *)
  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]].
    assumption.
  Qed.

  Definition reduce_term Γ t (h : welltyped Σ Γ t) :=
    zip (reduce_stack Γ t ε h).

  Theorem reduce_term_sound :
    forall Γ t h,
      ∥ red (fst Σ) Γ t (reduce_term Γ t h) ∥.
  Proof.
    intros Γ t h.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ ε _).
  Qed.

End Reduce.