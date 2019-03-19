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

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Definition R Σ Γ u v :=
    Subterm.lexprod _ _ (cored Σ Γ) term_subterm (zip u, fst u) (zip v, fst v).

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
      Acc (Subterm.lexprod _ _ (cored (fst Σ) Γ) term_subterm) (zip t, fst t).
  Proof.
    intros Σ Γ t h.
    eapply Subterm.acc_A_B_lexprod.
    - eapply normalisation. eassumption.
    - eapply well_founded_term_subterm.
    - eapply well_founded_term_subterm.
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

  Derive Signature for Subterm.lexprod.

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

  Lemma lexprod_trans :
    forall A B RA RB,
      transitive RA ->
      transitive RB ->
      transitive (Subterm.lexprod A B RA RB).
  Proof.
    intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
    revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
    - dependent induction h2.
      + eapply Subterm.left_lex. eapply hA ; eassumption.
      + eapply Subterm.left_lex. assumption.
    - dependent induction h2.
      + eapply Subterm.left_lex. assumption.
      + eapply Subterm.right_lex. eapply hB ; eassumption.
  Qed.

  Lemma Rtrans :
    forall Σ Γ u v w,
      R Σ Γ u v ->
      R Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    eapply lexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - intros ? ? ? ? ?. eapply Relation_Operators.t_trans ; eassumption.
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

  (* Lemma R_case : *)
  (*   forall Σ Γ ind p c c' brs π, *)
  (*     R Σ Γ c c' -> *)
  (*     Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p (zipapp c') brs, π). *)
  (* Proof. *)
  (*   intros Σ' Γ ind p [c e] [c' e'] brs π h. *)
  (*   dependent destruction h. *)
  (*   - right. econstructor. eapply cored_context. eapply cored_case. *)
  (*     assumption. *)
  (*   - cbn in H1. inversion H1. subst. clear H1. *)
  (*     cbn in H0. cbn. rewrite H3. reflexivity. *)
  (* Qed. *)

  (* Lemma Req_case : *)
  (*   forall Σ Γ ind p c c' brs π, *)
  (*     Req Σ Γ c c' -> *)
  (*     Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p (zipapp c') brs, π). *)
  (* Proof. *)
  (*   intros Σ' Γ ind p [c e] [c' e'] brs π h. *)
  (*   dependent destruction h. *)
  (*   - rewrite H0. reflexivity. *)
  (*   - eapply R_case. assumption. *)
  (* Qed. *)

 (*  Lemma R_case : *)
 (*    forall Σ Γ ind p c c' brs π, *)
 (*      R Σ Γ c (c', Case ind p brs π) -> *)
 (*      Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p c' brs, π). *)
 (*  Proof. *)
 (*    intros Σ' Γ ind p [c e] c' brs π h. *)
 (*    dependent destruction h. *)
 (*    - cbn in H0. cbn. eapply Req_trans. *)
 (*      2:{ right. econstructor. *)
 (*          instantiate (1 := (c,e)). cbn. *)
 (*          exact H0. *)
 (*      } *)


 (*      right. econstructor. eapply cored_context. eapply cored_case. *)
 (*      assumption. *)
 (*    - cbn in H1. inversion H1. subst. clear H1. *)
 (*      cbn in H0. cbn. rewrite H3. reflexivity. *)
 (*  Qed. *)

 (*  Lemma Req_case : *)
 (*    forall Σ Γ ind p c c' brs π, *)
 (*      Req Σ Γ c (c', Case ind p brs π) -> *)
 (*      Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p c' brs, π). *)
 (*  Proof. *)
 (*    intros Σ' Γ ind p [c e] c' brs π h. *)
 (*    dependent destruction h. *)
 (*    - rewrite H0. reflexivity. *)
 (*    - eapply R_case. assumption. *)
 (*  Qed. *)

 (* prf : Req (fst Σ) Γ (tConstruct ind' c' wildcard, args) (c, Case (ind, par) p brs π) *)
 (*  ============================ *)
 (*  Req (fst Σ) Γ (tCase (?Goal1, par) ?Goal0 (mkApps (tConstruct ?Goal1 c' ?u) (stack_args args)) brs, π) *)
 (*    (tCase (ind, par) p c brs, π) *)

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
    econstructor.
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
    econstructor. econstructor.
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
    econstructor. econstructor.
    eapply red1_context.
    econstructor.
  Qed.
  Next Obligation.
    eapply Subterm.right_lex. cbn. constructor. constructor.
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
    econstructor. econstructor. eapply red1_context.
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
    eapply Subterm.right_lex. cbn. constructor. constructor.
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
    unfold R. cbn. rewrite zipc_appstack. cbn.
    (* eapply Subterm.right_lex. *)
    (* Not a subterm! :( *)
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
             (* TODO Using Pr' *)
             admit.
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