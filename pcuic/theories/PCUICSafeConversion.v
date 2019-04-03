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
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1 as [[h1 h1']]. destruct h2 as [[h2 h2']].
      constructor. constructor ; eapply cumul_trans ; eassumption.
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
    - eapply conv_trans ; try eassumption.
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
    - eapply conv_trans ; try eassumption.
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
  | Reduction
  | Term
  | Args.

  Definition R (u v : state * term * stack) := False.

  Definition Ret s Γ leq t π :=
    match s with
    | Reduction =>
      forall t' π' (h' : welltyped Σ Γ (zipc t' π')),
        { b : bool | if b then conv leq Σ Γ (zipc t π) (zipc t' π') else True }
    | Term =>
      forall t' π' (h' : welltyped Σ Γ (zipc t' π')),
        { b : bool | if b then conv leq Σ Γ (zipc t π) (zipc t' π') else True }
    | Args =>
      forall π' (h' : welltyped Σ Γ (zipc t π')),
        { b : bool | if b then conv leq Σ Γ (zipc t π) (zipc t π') else True }
    end.

  Definition Aux s Γ t π :=
     forall leq s' t' π' (h' : welltyped Σ Γ (zipc t' π')),
       R (s', t', π') (s, t, π) -> Ret s' Γ leq t' π'.

  Notation no := (exist false I) (only parsing).
  Notation yes := (exist true _) (only parsing).
  Notation repack e := (let '(exist b h) := e in exist b _) (only parsing).
  Notation isconv_red_raw Γ leq t1 π1 h1 t2 π2 h2 aux :=
    (aux leq Reduction t1 π1 h1 _ t2 π2 h2) (only parsing).
  Notation isconv_prog_raw Γ leq t1 π1 h1 t2 π2 h2 aux :=
    (aux leq Term t1 π1 h1 _ t2 π2 h2) (only parsing).
  Notation isconv_args_raw Γ leq t π1 h1 π2 h2 aux :=
    (aux leq Args t π1 h1 _ π2 h2) (only parsing).
  Notation isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 h1 t2 π2 h2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 h1 t2 π2 h2 aux)) (only parsing).
  Notation isconv_args Γ leq t π1 h1 π2 h2 aux :=
    (repack (isconv_args_raw Γ leq t π1 h1 π2 h2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux Reduction Γ t1 π1)
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux
    with inspect (reduce_stack nodelta_flags Σ Γ t1 π1 h1) := {
    | @exist (t1',π1') eq1
      with inspect (reduce_stack nodelta_flags Σ Γ t2 π2 h2) := {
      | @exist (t2',π2') eq2 => isconv_prog Γ leq t1' π1' _ t2' π2' _ aux
      }
    }.
  Next Obligation.
    eapply red_welltyped.
    - eapply h1.
    - do 2 zip fold. rewrite eq1.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    (* (t1', π1') = reduce_stack nodelta_flags Σ Γ t1 π1 h1 *)
    (* ---------------------------------------------------- *)
    (*        R (Term, t1', π1') (Reduction, t1, π1)        *)
  Admitted.
  Next Obligation.
    eapply red_welltyped.
    - eapply h2.
    - repeat zip fold. rewrite eq2.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h1).
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h2).
    eapply conv_trans.
    - eapply red_conv_l. eassumption.
    - eapply conv_trans.
      + rewrite <- eq1. eassumption.
      + zip fold. rewrite eq2.
        eapply red_conv_r. assumption.
  Qed.

  Equations _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux Term Γ t1 π1)
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux := no.


  (* TODO Replace by Conv, perhaps it should even be global to iscong_args.
     In any case, leq should be quantified over in Aux.
   *)
  Equations(noeqns) _isconv_args (Γ : context) (leq : conv_pb) (t : term)
            (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : welltyped Σ Γ (zipc t π2))
            (aux : Aux Args Γ t π1)
    : { b : bool | if b then conv leq Σ Γ (zipc t π1) (zipc t π2) else True } :=

    _isconv_args Γ leq t (App u1 ρ1) h1 (App u2 ρ2) h2 aux
    with isconv_red_raw Γ leq u1 Empty _ u2 Empty _ aux := {
    | @exist true h1 := isconv_args Γ leq (tApp t u1) ρ1 _ ρ2 _ aux ;
    | @exist false _ := no
    } ;

    _isconv_args Γ leq t Empty h1 Empty h2 aux := yes ;

    _isconv_args Γ leq t π1 h1 π2 h2 aux := no.
  Next Obligation.
    apply conv_refl'.
  Qed.
  Next Obligation.
    zip fold in h1.
    apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_App h1) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    (* R (Reduction, u1, Empty) (Args, t, App u1 ρ1) *)
  Admitted.
  Next Obligation.
    zip fold in h2.
    apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_App h2) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    (* R (Args, tApp t u1, ρ1) (Args, t, App u1 ρ1) *)
  Admitted.
  Next Obligation.
    (* Here it is a bit unclear. Maybe things would be better if a common
       type was assumed.
     *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    (* We need congruence of application. *)
    admit.
  Admitted.

  Equations _isconv (s : state) (Γ : context) (leq : conv_pb)
            (t : term) (π : stack) (h : welltyped Σ Γ (zipc t π))
            (aux : Aux s Γ t π)
  : Ret s Γ leq t π :=
    _isconv Reduction Γ leq t π h aux :=
      λ { | t' | π' | h' := _isconv_red Γ leq t π h t' π' h' aux } ;

    _isconv Term Γ leq t π h aux :=
      λ { | t' | π' | h' := _isconv_prog Γ leq t π h t' π' h' aux } ;

    _isconv Args Γ leq t π h aux :=
      λ { | π' | h' := _isconv_args Γ leq t π h π' h' aux }.

  (* The idea is that when comparing two terms, we first reduce on both sides.
     We then go deeper inside the term, and sometimes recurse on the stacks
     themselves. That is why we use position instead of the subterm order.

     To define it we need more information. We need welltypedness for reduction.
     That is not all however. Indeed as of now, the two compared positions
     are not in the same term. This suggests yet another lexicographic order.
   *)
  (* Definition R Σ Γ (u v : term * stack) : Prop := *)
  (*   let '(u, π) := reduce_stack RedFlags.default Σ Γ (fst u) (snd u) in *)
  (*   let '(v, ρ) := reduce_stack RedFlags.default Σ Γ (fst v) (snd v) in *)
  (*   posR (stack_pos u π) (stack_pos v ρ). *)

  (* We have to devise an order for termination.
     It seems that we could somehow use the R from before, except that we would
     need to include more positions.
     So maybe, just lex cored subterm would work.

     Another solution would be to consider (t,π) ≤ (u,θ)
     when fst (reduce (t,π)) is a subterm of fst (reduce (u,θ)).

     If we need to speak about the stacks for the order, then we probably have
     to include a lot more stacks as well.
     That would be unfortunate.

     It seems that this approach is fine, except for a few (important) things:
     - the fallback terminates because we check reduction progressed
     - isconv_stacks needs to be able to reduce on the stack, so the order would
       have to mention it.

     A different point, we might need to update reduce in some way to assert
     that it cannot return an application, they must reside on the stack.

     Maybe implement a naive version first that reduces both sides (with delta
     or rather with provided flags).
     When two sides are equal, go to subterms (meaning stacks are empty by
     typing). When two sides are constants/variables, compare the stacks.
     This is fine for a lex order on subterm for the term and then subterm
     for the stack.

     This order is actually not ok. Because we want to convert on the stack.
     This means we have to use positions again.
     But this time with more constructors.
   *)

End Conversion.