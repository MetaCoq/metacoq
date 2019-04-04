(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template Require Import config univ monad_utils utils BasicAst AstUtils
     UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICSafeReduce.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.

(** * Conversion for PCUIC without fuel

  Following PCUICSafereduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Inductive conv_pb :=
| Conv
| Cumul.

Section Conversion.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.
  Context (Σ : global_context).

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

  Definition conv leq Σ Γ u v :=
    match leq with
    | Conv => ∥ Σ ;;; Γ |- u = v ∥
    | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
    end.

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Lemma red_welltyped :
    forall {Σ Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    intros Σ' Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction ; eassumption.
  Qed.

  Set Equations With UIP.

  Derive NoConfusion NoConfusionHom EqDec for stack.

  (* A choice is a local position.
     We redefine positions in a non dependent way to make it more practical.
   *)
  Inductive choice :=
  | app_l
  | app_r
  | case_c
  | lam_ty
  | lam_tm
  | prod_l
  | prod_r.

  Derive NoConfusion NoConfusionHom EqDec for choice.

  Definition position := list choice.

  Fixpoint validpos t (p : position) {struct p} :=
    match p with
    | [] => true
    | c :: p =>
      match c, t with
      | app_l, tApp u v => validpos u p
      | app_r, tApp u v => validpos v p
      | case_c, tCase indn pr c brs => validpos c p
      | lam_ty, tLambda na A t => validpos A p
      | lam_tm, tLambda na A t => validpos t p
      | prod_l, tProd na A B => validpos A p
      | prod_r, tProd na A B => validpos B p
      | _, _ => false
      end
    end.

  Definition pos (t : term) := { p : position | validpos t p = true }.

  Arguments exist {_ _} _ _.

  Definition dapp_l u v (p : pos u) : pos (tApp u v) :=
    exist (app_l :: ` p) (proj2_sig p).

  Definition dapp_r u v (p : pos v) : pos (tApp u v) :=
    exist (app_r :: ` p) (proj2_sig p).

  Definition dcase_c indn pr c brs (p : pos c) : pos (tCase indn pr c brs) :=
    exist (case_c :: ` p) (proj2_sig p).

  Definition dlam_ty na A t (p : pos A) : pos (tLambda na A t) :=
    exist (lam_ty :: ` p) (proj2_sig p).

  Definition dlam_tm na A t (p : pos t) : pos (tLambda na A t) :=
    exist (lam_tm :: ` p) (proj2_sig p).

  Definition dprod_l na A B (p : pos A) : pos (tProd na A B) :=
    exist (prod_l :: ` p) (proj2_sig p).

  Definition dprod_r na A B (p : pos B) : pos (tProd na A B) :=
    exist (prod_r :: ` p) (proj2_sig p).

  Inductive positionR : position -> position -> Prop :=
  | positionR_app_lr p q : positionR (app_r :: p) (app_l :: q)
  | positionR_deep c p q : positionR p q -> positionR (c :: p) (c :: q)
  | positionR_root c p : positionR (c :: p) [].

  Derive Signature for positionR.

  Definition posR {t} (p q : pos t) : Prop :=
    positionR (` p) (` q).

  Lemma posR_Acc :
    forall t p, Acc (@posR t) p.
  Proof.
    assert (forall na A B p, Acc posR p -> Acc posR (dprod_l na A B p)) as Acc_prod_l.
    { intros na A B p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h. cbn in e.
      eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall na A B p, Acc posR p -> Acc posR (dprod_r na A B p)) as Acc_prod_r.
    { intros na A B p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h. cbn in e.
      eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall na A t p, Acc posR p -> Acc posR (dlam_ty na A t p)) as Acc_lam_ty.
    { intros na A t p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h. cbn in e.
      eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall na A t p, Acc posR p -> Acc posR (dlam_tm na A t p)) as Acc_lam_tm.
    { intros na A t p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h. cbn in e.
      eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall u v p, Acc posR p -> Acc posR (dapp_r u v p)) as Acc_app_r.
    { intros u v p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h. cbn in e.
      eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall u v p, Acc posR p -> (forall q : pos v, Acc posR q) -> Acc posR (dapp_l u v p)) as Acc_app_l.
    { intros u v p h ih.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h.
      - eapply Acc_app_r with (p := exist p0 e). eapply ih.
      - eapply (ih2 (exist p0 e)). assumption.
    }
    assert (forall indn pr c brs p, Acc posR p -> Acc posR (dcase_c indn pr c brs p))
      as Acc_case_c.
    { intros indn pr c brs p h.
      induction h as [p ih1 ih2].
      constructor. intros [q e] h.
      dependent destruction h.
      eapply (ih2 (exist p0 e)). assumption.
    }
    intro t. induction t ; intros q.
    all: try solve [
      destruct q as [q e] ; destruct q as [| c q] ; [
        constructor ; intros [p' e'] h ;
        unfold posR in h ; cbn in h ;
        dependent destruction h ;
        destruct c ; cbn in e' ; discriminate
      | destruct c ; cbn in e ; discriminate
      ]
    ].
    - destruct q as [q e]. destruct q as [| c q].
      + constructor. intros [p e'] h.
        unfold posR in h. cbn in h.
        dependent destruction h.
        destruct c ; noconf e'.
        * eapply Acc_prod_l with (p := exist p0 e').
          eapply IHt1.
        * eapply Acc_prod_r with (p := exist p0 e').
          eapply IHt2.
      + destruct c ; noconf e.
        * eapply Acc_prod_l with (p := exist q e).
          eapply IHt1.
        * eapply Acc_prod_r with (p := exist q e).
          eapply IHt2.
    - destruct q as [q e]. destruct q as [| c q].
      + constructor. intros [p e'] h.
        unfold posR in h. cbn in h.
        dependent destruction h.
        destruct c ; noconf e'.
        * eapply Acc_lam_ty with (p := exist p0 e').
          eapply IHt1.
        * eapply Acc_lam_tm with (p := exist p0 e').
          eapply IHt2.
      + destruct c ; noconf e.
        * eapply Acc_lam_ty with (p := exist q e).
          eapply IHt1.
        * eapply Acc_lam_tm with (p := exist q e).
          eapply IHt2.
    - destruct q as [q e]. destruct q as [| c q].
      + constructor. intros [p e'] h.
        unfold posR in h. cbn in h.
        dependent destruction h.
        destruct c ; noconf e'.
        * eapply Acc_app_l with (p := exist p0 e').
          -- eapply IHt1.
          -- assumption.
        * eapply Acc_app_r with (p := exist p0 e').
          eapply IHt2.
      + destruct c ; noconf e.
        * eapply Acc_app_l with (p := exist q e).
          -- eapply IHt1.
          -- assumption.
        * eapply Acc_app_r with (p := exist q e).
          eapply IHt2.
    - destruct q as [q e]. destruct q as [| c q].
      + constructor. intros [p' e'] h.
        unfold posR in h. cbn in h.
        dependent destruction h.
        destruct c ; noconf e'.
        eapply Acc_case_c with (p := exist p0 e').
        eapply IHt2.
      + destruct c ; noconf e.
        eapply Acc_case_c with (p := exist q e).
        eapply IHt2.
  Qed.

  (* Equations atpos (t : term) (p : position) : term := *)
  (*   atpos t [] := t ; *)
  (*   atpos (tApp u v) (app_l :: p) := atpos u p ; *)
  (*   atpos (tApp u v) (app_r :: p) := atpos v p ; *)
  (*   atpos (tCase indn pr c brs) (case_c :: p) := atpos c p ; *)
  (*   atpos (tLambda na A t) (lam_ty :: p) := atpos A p ; *)
  (*   atpos (tLambda na A t) (lam_tm :: p) := atpos t p ; *)
  (*   atpos (tProd na A B) (prod_l :: p) := atpos A p ; *)
  (*   atpos (tProd na A B) (prod_r :: p) := atpos B p ; *)
  (*   atpos _ _ := tRel 0. *)

  Fixpoint atpos t (p : position) {struct p} : term :=
    match p with
    | [] => t
    | c :: p =>
      match c, t with
      | app_l, tApp u v => atpos u p
      | app_r, tApp u v => atpos v p
      | case_c, tCase indn pr c brs => atpos c p
      | lam_ty, tLambda na A t => atpos A p
      | lam_tm, tLambda na A t => atpos t p
      | prod_l, tProd na A B => atpos A p
      | prod_r, tProd na A B => atpos B p
      | _, _ => tRel 0
      end
    end.

  (* Derive NoConfusion NoConfusionHom for list. *)

  Lemma poscat_atpos :
    forall t p q, atpos t (p ++ q) = atpos (atpos t p) q.
  Proof.
    assert (forall p, atpos (tRel 0) p = tRel 0) as hh.
    { intros p. destruct p.
      - reflexivity.
      - destruct c ; reflexivity.
    }
    intros t p q.
    revert t q. induction p ; intros t q.
    - cbn. reflexivity.
    - destruct t ; destruct a.
      all: try solve [ rewrite hh ; reflexivity ].
      all: apply IHp.
  Qed.

  Lemma poscat_valid :
    forall t p q,
      validpos t p ->
      validpos (atpos t p) q ->
      validpos t (p ++ q).
  Proof.
    intros t p q hp hq.
    revert t q hp hq.
    induction p ; intros t q hp hq.
    - assumption.
    - destruct t ; destruct a.
      all: try noconf hp.
      all: apply IHp ; assumption.
  Qed.

  Fixpoint stack_position π : position :=
    match π with
    | Empty => []
    | App u ρ => stack_position ρ ++ [ app_l ]
    | Fix f n args ρ => stack_position ρ ++ [ app_r ]
    | Case indn pred brs ρ => stack_position ρ ++ [ case_c ]
    end.

  Lemma stack_position_atpos :
    forall t π, atpos (zipc t π) (stack_position π) = t.
  Proof.
    intros t π. revert t. induction π ; intros u.
    - reflexivity.
    - cbn. rewrite poscat_atpos. rewrite IHπ. reflexivity.
    - cbn. rewrite poscat_atpos. rewrite IHπ. reflexivity.
    - cbn. rewrite poscat_atpos. rewrite IHπ. reflexivity.
  Qed.

  Lemma stack_position_valid :
    forall t π, validpos (zipc t π) (stack_position π).
  Proof.
    intros t π. revert t. induction π ; intros u.
    - reflexivity.
    - cbn. eapply poscat_valid.
      + eapply IHπ.
      + rewrite stack_position_atpos. reflexivity.
    - cbn. eapply poscat_valid.
      + eapply IHπ.
      + rewrite stack_position_atpos. reflexivity.
    - cbn. eapply poscat_valid.
      + eapply IHπ.
      + rewrite stack_position_atpos. reflexivity.
  Qed.

  Definition stack_pos t π : pos (zipc t π) :=
    exist (stack_position π) (stack_position_valid t π).

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_refl.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_trans :
    forall Γ u v w,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = w ->
      Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma conv_trans' :
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_conv_l :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ u v.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.

  Lemma conv_conv_r :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ v u.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.


  (* Shouldn't be here. *)
  (* Lemma eq_term_refl : *)
  (*   forall ϕ t, eq_term ϕ t t. *)
  (* Proof. *)
  (*   intros ϕ t. induction t. *)
  (*   all: cbn. *)
  (*   all: try rewrite IHt. *)
  (*   all: try rewrite IHt1. *)
  (*   all: try rewrite IHt2. *)
  (*   all: try rewrite IHt3. *)
  (*   all: try rewrite eq_nat_refl. *)
  (*   all: try rewrite eq_string_refl. *)
  (*   all: simpl. *)
  (*   all: auto. *)
  (* Admitted. *)

  Lemma cumul_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipc u ρ <= zipc v ρ.
  Proof.
    intros Γ u v ρ h.
    (* induction h. *)
    (* - eapply cumul_refl. *)
    (*   revert t u e. *)
    (*   induction ρ ; intros u v e. *)
    (*   + cbn. assumption. *)
    (*   + cbn. apply IHρ. cbn. rewrite e. *)
    (*     rewrite eq_term_refl. reflexivity. *)
    (*   + cbn. apply IHρ. cbn.  *)
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - cbn. apply IHρ.
      (* Congruence for application *)
      admit.
    - cbn.
      (* Congruence for application and mkApps *)
      admit.
    - cbn.
      (* Congruence for case *)
      admit.
  Admitted.

  Lemma conv_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- zipc u ρ = zipc v ρ.
  Proof.
    intros Γ u v ρ [].
    constructor ; eapply cumul_context ; assumption.
  Qed.

  Lemma conv_context' :
    forall Γ leq u v ρ,
      conv leq Σ Γ u v ->
      conv leq Σ Γ (zipc u ρ) (zipc v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [[h1 h2]]. constructor.
      constructor ; eapply cumul_context ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_context. assumption.
  Qed.

  Inductive state :=
  | Reduction (t : term)
  | Term (t : term)
  | Args.

  (* Will definitely depend on Γ (Σ is already here) *)
  Definition R (u v : state * term * stack * stack) := False.

  Lemma R_Acc : forall u, Acc R u.
  Admitted.

  Definition Ret s Γ t π π' :=
    match s with
    | Reduction t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zipc t π) (zipc t' π') else True }
    | Term t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zipc t π) (zipc t' π') else True }
    | Args =>
      { b : bool | if b then ∥ Σ ;;; Γ |- zipc t π = zipc t π' ∥ else True }
    end.

  Definition wts Γ s t π :=
    match s with
    | Reduction t' => welltyped Σ Γ (zipc t' π)
    | Term t' => welltyped Σ Γ (zipc t' π)
    | Args => welltyped Σ Γ (zipc t π)
    end.

  (* Probably have to generalise over Γ as well. *)
  Definition Aux s Γ t π1 π2 :=
     forall s' t' π1' π2',
       welltyped Σ Γ (zipc t' π1') ->
       wts Γ s' t' π2' ->
       R (s', t', π1', π2') (s, t, π1, π2) ->
       Ret s' Γ t' π1' π2'.

  Notation no := (exist false I) (only parsing).
  Notation yes := (exist true _) (only parsing).

  Notation repack e := (let '(exist b h) := e in exist b _) (only parsing).

  Notation isconv_red_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Reduction t2) t1 π1 π2 _ _ _ leq) (only parsing).
  Notation isconv_prog_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Term t2) t1 π1 π2 _ _ _ leq) (only parsing).
  Notation isconv_args_raw Γ t π1 π2 aux :=
    (aux Args t π1 π2 _ _ _) (only parsing).

  Notation isconv_red Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args Γ t π1 π2 aux :=
    (repack (isconv_args_raw Γ t π1 π2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux (Reduction t2) Γ t1 π1 π2)
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux
    with inspect (reduce_stack nodelta_flags Σ Γ t1 π1 h1) := {
    | @exist (t1',π1') eq1
      with inspect (reduce_stack nodelta_flags Σ Γ t2 π2 h2) := {
      | @exist (t2',π2') eq2 => isconv_prog Γ leq t1' π1' t2' π2' aux
      }
    }.
  Next Obligation.
    eapply red_welltyped.
    - eapply h1.
    - do 2 zip fold. rewrite eq1.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - eapply h2.
    - repeat zip fold. rewrite eq2.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    (* (t1', π1') = reduce_stack nodelta_flags Σ Γ t1 π1 h1 *)
    (* ---------------------------------------------------- *)
    (* R (Term t2', t1', π1', π2') (Reduction t2, t1, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h1).
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h2).
    eapply conv_trans'.
    - eapply red_conv_l. eassumption.
    - eapply conv_trans'.
      + rewrite <- eq1. eassumption.
      + zip fold. rewrite eq2.
        eapply red_conv_r. assumption.
  Qed.

  Lemma lookup_env_const_name :
    forall {c c' d},
      lookup_env Σ c' = Some (ConstantDecl c d) ->
      c' = c.
  Proof.
    intros c c' d e.
    destruct Σ as [Σ' ?]. cbn in e.
    induction Σ'.
    - cbn in e. discriminate.
    - destruct a.
      + cbn in e. destruct (ident_eq_spec c' k).
        * subst. inversion e. reflexivity.
        * apply IHΣ'. assumption.
      + cbn in e. destruct (ident_eq_spec c' k).
        * inversion e.
        * apply IHΣ'. assumption.
  Qed.

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux (Term t2) Γ t1 π1 π2)
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    (* This case is impossible, but we would need some extra argument to make it
       truly impossible (namely, only allow results of reduce_stack). *)
    (* _isconv_prog Γ leq (tApp _ _) π1 h1 (tApp _ _) π2 h2 aux := no ; *)

    _isconv_prog Γ leq (tConst c u) π1 h1 (tConst c' u') π2 h2 aux
    with eq_dec c c' := {
    | left eq1 with eq_dec u u' := {
      | left eq2 with isconv_args_raw Γ (tConst c u) π1 π2 aux := {
        | @exist true h := yes ;
        (* Unfold both constants at once *)
        | @exist false _ with inspect (lookup_env Σ c) := {
          | @exist (Some (ConstantDecl n {| cst_body := Some body |})) eq3 :=
            (* In PCUICChecker, there is no subst but I guess it's just wrong. *)
            isconv_red Γ leq (subst_instance_constr u body) π1
                             (subst_instance_constr u body) π2 aux ;
          (* Inductive or not found *)
          | @exist _ _ := no
          }
        } ;
      (* If the two constants are different, we unfold one of them *)
      | right _ with inspect (lookup_env Σ c') := {
        | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
          isconv_red Γ leq (tConst c u) π1 (subst_instance_constr u b) π2 aux ;
        (* Inductive or not found *)
        | _ with inspect (lookup_env Σ c) := {
          | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
            isconv_red Γ leq (subst_instance_constr u b) π1
                             (tConst c' u') π2 aux ;
          (* Both Inductive or not found *)
          | _ := no
          }
        }
      } ;
    | right _ := no
    } ;

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux := no.
  Next Obligation.
    (* R (Args, tConst c' u', π1, π2) (Term (tConst c' u'), tConst c' u', π1, π2) *)
  Admitted.
  Next Obligation.
    destruct h. eapply conv_conv_l. assumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h1.
    - constructor.
      Opaque subst_instance_constr.
      eapply red_context.
      Transparent subst_instance_constr.
      symmetry in eq3.
      pose proof (lookup_env_const_name eq3). subst.
      econstructor.
      + econstructor.
      + econstructor.
        * exact eq3.
        * reflexivity.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h2.
    - constructor.
      Opaque subst_instance_constr.
      eapply red_context.
      Transparent subst_instance_constr.
      symmetry in eq3.
      pose proof (lookup_env_const_name eq3). subst.
      econstructor.
      + econstructor.
      + econstructor.
        * exact eq3.
        * reflexivity.
  Qed.
  Next Obligation.
    (* tConst c' u' reduces to subst_instance_constr u' body *)
    (* R (Reduction (subst_instance_constr u' body), subst_instance_constr u' body, π1, π2) *)
    (*   (Term (tConst c' u'), tConst c' u', π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_trans'.
    - eapply red_conv_l.
      eapply red_context.
      symmetry in eq3.
      pose proof (lookup_env_const_name eq3). subst.
      eapply trans_red.
      + econstructor.
      + econstructor.
        * exact eq3.
        * reflexivity.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r.
      eapply red_context.
      symmetry in eq3.
      pose proof (lookup_env_const_name eq3). subst.
      eapply trans_red.
      + econstructor.
      + econstructor.
        * exact eq3.
        * reflexivity.
  Qed.
  Next Obligation.
    (* Same as above, using reduction, should be a lemma I guess *)
  Admitted.
  Next Obligation.
    (* R (Reduction (subst_instance_constr u b), tConst c' u, π1, π2) *)
    (*   (Term (tConst c' u'), tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    (* By the same reduction, again... *)
  Admitted.
  Next Obligation.
    (* Same *)
  Admitted.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    (* Same *)
  Admitted.
  Next Obligation.
    (* Same *)
  Admitted.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    (* Same *)
  Admitted.
  Next Obligation.
    (* Same *)
  Admitted.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    (* Same *)
  Admitted.

  Equations(noeqns) _isconv_args (Γ : context) (t : term)
            (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : welltyped Σ Γ (zipc t π2))
            (aux : Aux Args Γ t π1 π2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zipc t π1 = zipc t π2 ∥ else True } :=

    _isconv_args Γ t (App u1 ρ1) h1 (App u2 ρ2) h2 aux
    with isconv_red_raw Γ Conv u1 Empty u2 Empty aux := {
    | @exist true h1 := isconv_args Γ (tApp t u1) ρ1 ρ2 aux ;
    | @exist false _ := no
    } ;

    _isconv_args Γ t Empty h1 Empty h2 aux := yes ;

    _isconv_args Γ t π1 h1 π2 h2 aux := no.
  Next Obligation.
    constructor.
    apply conv_refl.
  Qed.
  Next Obligation.
    zip fold in h1.
    apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_App h1) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    zip fold in h2.
    apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_App h2) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    (* R (Reduction u2, u1, Empty, Empty) (Args, t, App u1 ρ1, App u2 ρ2) *)
  Admitted.
  Next Obligation.
    (* Here it is a bit unclear. Maybe things would be better if a common
       type was assumed.
     *)
  Admitted.
  Next Obligation.
    (* R (Args, tApp t u1, ρ1, ρ2) (Args, t, App u1 ρ1, App u2 ρ2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h1 as [h1]. destruct h as [h].
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    (* We need congruence of application. *)
    admit.
  Admitted.

  Equations _isconv (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : wts Γ s t π2)
            (aux : Aux s Γ t π1 π2)
  : Ret s Γ t π1 π2 :=
    _isconv (Reduction t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv (Term t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv Args Γ t π1 h1 π2 h2 aux :=
        _isconv_args Γ t π1 h1 π2 h2 aux.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : wts Γ s t π2)
    : Ret s Γ t π1 π2 :=

    isconv_full s Γ t π1 h1 π2 h2 :=
      Fix_F (R := R)
            (fun '(s', t', π1', π2') => welltyped Σ Γ (zipc t' π1') -> wts Γ s' t' π2' -> Ret s' Γ t' π1' π2')
            (fun t' f => _)
            (x := (s, t, π1, π2))
            _ _ _.
  Next Obligation.
    eapply _isconv ; try assumption.
    intros s' t' π1' π2' h1' h2' hR.
    specialize (f (s', t', π1', π2') hR). cbn in f.
    eapply f ; assumption.
  Qed.
  Next Obligation.
    apply R_Acc.
  Qed.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 :=
    let '(exist b _) := isconv_full (Reduction t2) Γ t1 π1 h1 π2 h2 leq in b.

  Theorem isconv_sound :
    forall Γ leq t1 π1 h1 t2 π2 h2,
      isconv Γ leq t1 π1 h1 t2 π2 h2 ->
      conv leq Σ Γ (zipc t1 π1) (zipc t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2.
    destruct isconv_full as [[]] ; auto.
    discriminate.
  Qed.

End Conversion.