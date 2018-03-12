From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon ITyping.

(* Lemmata about typing *)

Open Scope type_scope.
Open Scope i_scope.

(* Typing up to equality *)
Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqctx_conv :
  forall {Σ Γ Δ t1 t2 A},
    Σ ;;; Γ |-i t1 = t2 : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t1 = t2 : A.
Proof.
  intros Σ Γ Δ t1 t2 A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-i t : A ->
    A = B ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqconv :
  forall {Σ Γ t t' A B},
    Σ ;;; Γ |-i t = t' : A ->
    A = B ->
    Σ ;;; Γ |-i t = t' : B.
Proof.
  intros Σ Γ t t' A B h e.
  rewrite <- e. exact h.
Defined.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Ltac erewrite_assumption :=
  match goal with
  | H : _ = _ |- _ =>
    erewrite H by omega
  end.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try omega.
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-i t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact typed_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ decl' hind. unfold type_inductive in hind.
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. unfold isArity in i.
      assumption.
    + cbn in h. eapply IHhind.
      eassumption.
Defined.

Fact ident_neq_fresh :
  forall {Σ ind decl' d},
    slookup_env Σ (inductive_mind ind) =
    Some (SInductiveDecl (inductive_mind ind) decl') ->
    fresh_global (sglobal_decl_ident d) Σ ->
    ident_eq (inductive_mind ind) (sglobal_decl_ident d) = false.
Proof.
  intro Σ. induction Σ.
  - intros ind decl' d h1 h2.
    cbn in h1. inversion h1.
  - intros ind decl' d h1 h2.
    cbn in h1.
    set (id1 := inductive_mind ind) in *.
    set (id2 := sglobal_decl_ident d) in *.
    set (id3 := sglobal_decl_ident a) in *.
    dependent destruction h2.
    case_eq (ident_eq id1 id3) ;
      intro e ; rewrite e in h1.
    + inversion h1 as [ h1' ]. subst. clear h1 e.
      cbn in *.
      destruct (ident_eq_spec id1 id2) ; easy.
    + eapply IHΣ ; eassumption.
Defined.

Fixpoint weak_glob_type {Σ ϕ Γ t A} (h : (Σ,ϕ) ;;; Γ |-i t : A) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    (d::Σ, ϕ) ;;; Γ |-i t : A

with weak_glob_eq {Σ ϕ Γ t1 t2 A} (h : (Σ,ϕ) ;;; Γ |-i t1 = t2 : A) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    (d::Σ, ϕ) ;;; Γ |-i t1 = t2 : A

with weak_glob_wf {Σ ϕ Γ} (h : wf (Σ,ϕ) Γ) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    wf (d::Σ, ϕ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
                eassumption
               ).
      - eapply type_HeqTrans with (B := B) (b := b).
        all: apply weak_glob_type ; eassumption.
      - eapply type_ProjT2 with (A1 := A1).
        all: apply weak_glob_type ; eassumption.
      - eapply type_Ind with (univs := univs).
        + apply weak_glob_wf ; assumption.
        + destruct isdecl as [decl' [h1 [h2 h3]]].
          exists decl'. repeat split.
          * cbn in *. unfold sdeclared_minductive in *.
            cbn. erewrite ident_neq_fresh by eassumption.
            assumption.
          * assumption.
          * assumption.
    }

  (* weak_glob_eq *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
                eassumption
               ).
      - eapply cong_HeqTrans with (B := B) (b := b).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
      - eapply cong_ProjT2 with (A1 := A1).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
    }

  (* weak_glob_wf *)
  - { dependent destruction h ; intros fd.
      - constructor.
      - econstructor.
        + apply weak_glob_wf ; assumption.
        + apply weak_glob_type ; eassumption.
    }
Defined.

Fact typed_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ hg. destruct Σ as [Σ ϕ].
  dependent induction hg.
  - intros ind decl univs isdecl.
    cbn in *. destruct isdecl as [decl' [h1 [h2 h3]]].
    inversion h1.
  - intros ind decl univs isdecl.
    destruct isdecl as [decl' [h1 [h2 h3]]].
    cbn in h1. unfold sdeclared_minductive in h1.
    cbn in h1.
    case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e. rewrite e in h1.
      inversion h1 as [ h1' ]. subst.
      cbn in t. clear e.
      destruct (typed_ind_type' t h3) as [s h].
      exists s. eapply weak_glob_type ; assumption.
    + intro e. rewrite e in h1.
      destruct (IHhg ind decl univs) as [s h].
      * exists decl'. repeat split ; eassumption.
      * exists s. eapply weak_glob_type ; assumption.
Defined.

Fact lift_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n k,
        lift n k (sind_type decl) = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n k.
  destruct (typed_ind_type hg h).
  eapply closed_lift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact xcomp_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      Xcomp (sind_type decl).
Proof.
  intros Σ decl' hind. unfold type_inductive in hind.
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. assumption.
    + cbn in h. eapply IHhind.
      eassumption.
Defined.

Fact xcomp_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      Xcomp (sind_type decl).
Proof.
  intros Σ hg. destruct Σ as [Σ ϕ].
  dependent induction hg.
  - intros ind decl univs isdecl.
    cbn in *. destruct isdecl as [decl' [h1 [h2 h3]]].
    inversion h1.
  - intros ind decl univs isdecl.
    destruct isdecl as [decl' [h1 [h2 h3]]].
    cbn in h1. unfold sdeclared_minductive in h1.
    cbn in h1.
    case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e. rewrite e in h1.
      inversion h1 as [ h1' ]. subst.
      cbn in t. clear e.
      apply (xcomp_ind_type' t h3).
    + intro e. rewrite e in h1.
      apply (IHhg ind decl univs).
      exists decl'. repeat split ; eassumption.
Defined.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-i t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A,
      cong_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Ξ |-i t1 = t2 : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t1 = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift or cong_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i lift _ _ ?t : _ => ih h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i lift _ _ ?t = _ : _ =>
    ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-i t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with cong_lift {Σ Γ Δ Ξ t1 t2 A} (h : Σ ;;; Γ ,,, Ξ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t1
  = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by omega.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; omega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. omega.
        + eapply meta_conv.
          * eapply type_Rel. eapply wf_lift ; assumption.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort. now apply wf_lift.
      - cbn. eapply type_Prod ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1.
        cbn. eapply type_J ; try eih.
        + instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
          rewrite !lift_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn. eapply type_Heq ; eih.
      - cbn. eapply type_HeqToEq ; eih.
      - cbn. eapply type_HeqRefl ; eih.
      - cbn. eapply type_HeqSym ; eih.
      - cbn. eapply @type_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply type_HeqTransport ; eih.
      - cbn. eapply type_CongProd ; try eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; try eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite 2!substP1.
        eapply type_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongEq ; eih.
      - cbn. eapply type_CongRefl ; eih.
      - cbn. eapply type_EqToHeq ; eih.
      - cbn. eapply type_HeqTypeEq ; eih.
      - cbn. eapply type_Pack ; eih.
      - cbn. eapply @type_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply @type_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply type_ProjTe ; eih.
      - cbn. erewrite lift_ind_type by eassumption.
        eapply type_Ind.
        + now apply wf_lift.
        + eassumption.
      - eapply type_conv ; eih.
    }

  (* cong_lift *)
  - { intros hg hwf. dependent destruction h.
      - apply eq_reflexivity. apply type_lift ; assumption.
      - apply eq_symmetry. eapply cong_lift ; assumption.
      - eapply eq_transitivity ; eih.
      - change (lift #|Δ| #|Ξ| (t {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t { 0 := u })).
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite 2!substP1. cbn.
        eapply eq_beta ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply eq_JRefl ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply eq_TransportRefl ; eih.
      - eapply eq_conv ; eih.
      - cbn. eapply cong_Prod ; eih.
      - cbn. eapply cong_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
        rewrite substP1.
        eapply cong_App ; eih.
      - cbn. eapply cong_Eq ; eih.
      - cbn. eapply cong_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply cong_J ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A1) (lift #|Δ| #|Ξ| u1))
            with (lift #|Δ| #|Ξ| (sRefl A1 u1)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply cong_Transport ; eih.
      - cbn. eapply cong_Heq ; eih.
      - cbn. eapply cong_Pack ; eih.
      - cbn. eapply cong_HeqToEq ; eih.
      - cbn. eapply cong_HeqRefl ; eih.
      - cbn. eapply cong_HeqSym ; eih.
      - cbn. eapply cong_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply cong_HeqTransport ; eih.
      - cbn. eapply cong_CongProd ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        rewrite substP1.
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite substP1.
        eapply cong_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; eih.
      - cbn. eapply cong_CongRefl ; eih.
      - cbn. eapply cong_EqToHeq ; eih.
      - cbn. eapply cong_HeqTypeEq ; eih.
      - cbn. eapply cong_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply cong_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply cong_ProjTe ; eih.
      - cbn. eapply eq_HeqToEqRefl ; eih.
    }

  (* wf_lift *)
  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; omega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A x B s hg ht hB.
  apply (@type_lift _ _ [ svass x B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A x B s y C s'},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i C : sSort s' ->
    Σ ;;; Γ ,, svass x B ,, svass y C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A x B s y C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Corollary cong_lift01 :
  forall {Σ Γ t1 t2 A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t1 = lift0 1 t2 : lift0 1 A.
Proof.
  intros Σ Γ t1 t2 A x B s hg H H0.
  apply @cong_lift with (Δ := [ svass x B ]) (Ξ := nil).
  - cbn. assumption.
  - assumption.
  - econstructor.
    + eapply typing_wf. eassumption.
    + eassumption.
Defined.

Fact subst_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n u,
        (sind_type decl){ n := u } = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n u.
  destruct (typed_ind_type hg h).
  eapply closed_subst.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm) (nx : name)
          (B u : sterm),
          Σ;;; Γ,, svass nx B ,,, Δ |-i t : A ->
          type_glob Σ ->
          Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
          t {#|Δ| := u} : A {#|Δ| := u},
     cong_subst :
       forall (Σ : sglobal_context) (Γ Δ : scontext) (t1 t2 A : sterm) (nx : name)
         (B u : sterm),
         Σ;;; Γ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
         type_glob Σ ->
         Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
         t1 {#|Δ| := u} = t2 {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst, cong_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i ?t{ _ := _ } : _ => sh h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i ?t{ _ := _ } = _ : _ =>
    sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t{ #|Δ| := u } : A{ #|Δ| := u }

with cong_subst {Σ Γ Δ t1 t2 A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t1{ #|Δ| := u }
  = t2{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ nx B u}
  (h : wf Σ (Γ ,, svass nx B ,,, Δ)) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by omega.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H. intro ge'.
          cbn. rewrite substP3 by omega.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by omega.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by omega.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by omega.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-i _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; omega)
          end.
          rewrite substP2 by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_subst ; eassumption.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort. eapply wf_subst ; eassumption.
      - cbn. eapply type_Prod ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Eq ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply type_J ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_Transport ; esh.
      - cbn. eapply type_Heq ; esh.
      - cbn. eapply type_HeqToEq ; esh.
      - cbn. eapply type_HeqRefl ; esh.
      - cbn. eapply type_HeqSym ; esh.
      - cbn. eapply type_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply type_HeqTransport ; esh.
      - cbn. eapply type_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply type_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongEq ; esh.
      - cbn. eapply type_CongRefl ; esh.
      - cbn. eapply type_EqToHeq ; esh.
      - cbn. eapply type_HeqTypeEq ; esh.
      - cbn. eapply type_Pack ; esh.
      - cbn. eapply @type_ProjT1 with (A2 := A2{#|Δ| := u}) ; esh.
      - cbn. eapply @type_ProjT2 with (A1 := A1{#|Δ| := u}) ; esh.
      - cbn. eapply type_ProjTe ; esh.
      - cbn. erewrite subst_ind_type by eassumption.
        eapply type_Ind.
        + now eapply wf_subst.
        + eassumption.
      - cbn. eapply type_conv ; esh.
    }

  (* cong_subst *)
  - { intros hg hu.
      dependent destruction h.
      - constructor. esh.
      - constructor. esh.
      - eapply eq_transitivity ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply eq_beta ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply eq_JRefl ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {#|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply eq_TransportRefl ; esh.
      - eapply eq_conv ; esh.
      - cbn. eapply cong_Prod ; esh.
      - cbn. eapply cong_Lambda ; esh.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_App ; esh.
      - cbn. eapply cong_Eq ; esh.
      - cbn. eapply cong_Refl ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply cong_J ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A1 {0 + #|Δ| := u}) (u1 {0 + #|Δ| := u}))
            with ((sRefl A1 u1){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply cong_Transport ; esh.
      - cbn. eapply cong_Heq ; esh.
      - cbn. eapply cong_Pack ; esh.
      - cbn. eapply cong_HeqToEq ; esh.
      - cbn. eapply cong_HeqRefl ; esh.
      - cbn. eapply cong_HeqSym ; esh.
      - cbn. eapply cong_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_HeqTransport ; esh.
      - cbn. eapply cong_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite !substP4. cbn.
        eapply cong_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; esh.
      - cbn. eapply cong_CongRefl ; esh.
      - cbn. eapply cong_EqToHeq ; esh.
      - cbn. eapply cong_HeqTypeEq ; esh.
      - cbn. eapply cong_ProjT1 with (A2 := A2{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjT2 with (A1 := A1{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjTe ; esh.
      - cbn. eapply eq_HeqToEqRefl ; esh.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. rewrite subst_decl_svass. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u n hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C na nb u v},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C na nb u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ svass nb B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Lemma cong_substs :
  forall {Σ Γ Δ t A nx B},
  Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A ->
  type_glob Σ ->
  forall {u1 u2},
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ
    |-i t{ #|Δ| := u1 }
     = t{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ Δ t A nx B ht hg.
  dependent induction ht ; intros uu1 uu2 huu huu1.
  - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
    + assert (h : n >= #|Δ|) by omega.
      rewrite safe_nth_ge' with (h0 := h).
      set (ge := ge_sub isdecl h).
      rewrite substP3 by omega.
      generalize ge.
      replace (n - #|Δ|) with 0 by omega.
      intro ge'. cbn.
      subst.
      replace #|Δ| with #|subst_context uu1 Δ|
        by (now rewrite subst_context_length).
      eapply @cong_lift with (Ξ := []) (Δ := subst_context uu1 Δ).
      * cbn. assumption.
      * assumption.
      * eapply wf_subst ; eassumption.
    + assert (h : n >= #|Δ|) by omega.
      rewrite safe_nth_ge' with (h0 := h).
      set (ge := ge_sub isdecl h).
      destruct n ; try easy.
      rewrite substP3 by omega.
      generalize ge.
      replace (S n - #|Δ|) with (S (n - #|Δ|)) by omega.
      cbn. intro ge'.
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel. eapply wf_subst ; eassumption.
      * erewrite safe_nth_ge'.
        f_equal. f_equal. eapply safe_nth_cong_irr.
        rewrite subst_context_length. reflexivity.
    + assert (h : n < #|Δ|) by omega.
      rewrite @safe_nth_lt with (isdecl' := h).
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?t{?d := ?u} =>
        replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
          by (f_equal ; omega)
      end.
      rewrite substP2 by omega.
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel.
        eapply wf_subst ; eassumption.
      * f_equal.
        erewrite safe_nth_lt.
        eapply safe_nth_subst_context.
  - cbn. apply eq_reflexivity. apply type_Sort.
    eapply wf_subst ; eassumption.
  - cbn. eapply cong_Prod.
    + now apply IHht1.
    + specialize (IHht2 Γ0 (Δ ,, svass n t) b (sSort s2) nx B eq_refl).
      apply IHht2 ; assumption.
  - cbn. eapply cong_Lambda.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n t) (A := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht3 with (Δ0 := Δ ,, svass n t)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4. cbn.
    eapply cong_App.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n A) (A0 := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Eq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_Refl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4.
    replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
    rewrite substP4.
    eapply cong_J.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht4
          with (Δ0 := (Δ ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)))
               (A0 := sSort s2)
        ; [ reflexivity | eassumption .. ].
      * instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
        rewrite !subst_decl_svass. cbn. f_equal.
        f_equal. f_equal.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
    + apply IHht5 ; eassumption.
    + eapply meta_eqconv.
      * apply IHht6 ; eassumption.
      * replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
        rewrite <- substP4.
        replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
        change (sRefl (A {0 + #|Δ| := uu1}) (u {0 + #|Δ| := uu1}))
          with ((sRefl A u){ 0 + #|Δ| := uu1}).
        rewrite <- substP4. reflexivity.
  - cbn. eapply cong_Transport.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Heq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_HeqToEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_HeqSym.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht5 ; eassumption.
  - cbn. eapply cong_HeqTrans with (B := B{#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht7 ; eassumption.
    + apply IHht8 ; eassumption.
  - cbn. eapply cong_HeqTransport.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_CongProd.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht5 with (Δ0 := Δ,, svass nx A1) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
    + eapply meta_eqctx_conv.
      * eapply IHht6 with (Δ0 := Δ,, svass ny A2) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
  - cbn. eapply cong_CongLambda.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht3 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht6 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply IHht8 with (Δ0 := Δ,, svass nx A1)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht9 with (Δ0 := Δ,, svass ny A2)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite 2!substP4. cbn.
    eapply cong_CongApp.
    + eapply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht8 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply @type_subst with (A := sProd nx A1 B1) ; eassumption.
    + eapply @type_subst with (A := sProd ny A2 B2) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongEq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_EqToHeq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqTypeEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_Pack.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_ProjT1 with (A2 :=  A2 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjT2 with (A1 :=  A1 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjTe.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply eq_reflexivity.
    erewrite subst_ind_type by eassumption.
    eapply type_Ind.
    + eapply wf_subst ; eassumption.
    + eassumption.
  - eapply eq_conv.
    + eapply IHht1 ; assumption.
    + eapply @cong_subst with (A := sSort s) ; eassumption.
  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary full_cong_subst :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    type_glob Σ ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t2 : A ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A hg ht hu ht2 hu1.
  eapply eq_transitivity.
  - exact (cong_subst ht hg hu1).
  - exact (cong_substs ht2 hg hu hu1).
Defined.

Lemma pre_cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ ,, svass n A |-i t2 : B ->
    Σ ;;; Γ |-i u1 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n hg ht hu ht2 hu1.
  eapply @full_cong_subst with (Δ := []) ; eassumption.
Defined.

Lemma pre_cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t2 : C ->
    Σ ;;; Γ |-i u1 : A ->
    Σ;;; Γ,, svass nb (B {0 := u1}) |-i t2 {1 := u2} : C {1 := u1} ->
    Σ ;;; Γ |-i v1 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 hg ht hu hv ht2 hu1 hst2 hv1.
  eapply @full_cong_subst with (Δ := []).
  - assumption.
  - eapply @full_cong_subst with (Δ := [ svass nb B ]).
    + assumption.
    + exact ht.
    + assumption.
    + assumption.
    + assumption.
  - cbn. assumption.
  - cbn. assumption.
  - cbn. assumption.
Defined.

Inductive eqctx Σ : scontext -> scontext -> Type :=
| eqnil : eqctx Σ nil nil
| eqsnoc Γ na A Δ nb B s :
    eqctx Σ Γ Δ ->
    Σ ;;; Γ |-i A = B : sSort s ->
    eqctx Σ (Γ ,, svass na A) (Δ ,, svass nb B).

Fact eqctx_refl :
  forall {Σ Γ},
    wf Σ Γ ->
    eqctx Σ Γ Γ.
Proof.
  intros Σ Γ h.
  dependent induction Γ.
  - constructor.
  - dependent destruction h.
    econstructor.
    + now apply IHΓ.
    + now apply eq_reflexivity.
Defined.

(* Lemma ctx_conv : *)
(*   forall {Σ Γ Δ}, *)
(*     eqctx Σ Γ Δ -> *)
(*     forall {t A}, *)
(*       Σ ;;; Γ |-i t : A -> *)
(*       Σ ;;; Δ |-i t : A. *)
(* Proof. *)
  (* intros Σ Γ Δ eq. *)
  (* dependent induction eq ; intros t C h. *)
  (* - assumption. *)
  (* - dependent induction h. *)
  (*   + eapply type_Rel. *)
(* Admitted. *)

Lemma ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t : A.
Admitted.

Lemma eqctx_conv :
  forall {Σ Γ Δ t u A},
    Σ ;;; Γ |-i t = u : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t = u : A.
Admitted.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    ∑ s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (succ_sort (succ_sort s)). now apply type_Sort.
  - exists (succ_sort (max_sort s1 s2)). apply type_Sort. apply (typing_wf H).
  - exists (max_sort s1 s2). apply type_Prod.
    + assumption.
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * apply eqctx_refl. now apply (typing_wf H).
      * apply eq_reflexivity. eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst ; eassumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. now apply type_Eq.
  - exists s2.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + assumption.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.
  - eexists. eassumption.
  - exists (succ_sort (succ_sort s)). apply type_Sort. apply (typing_wf H).
  - exists s. apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq. all: try assumption.
    eapply type_Transport ; eassumption.
  - exists (succ_sort (succ_sort (max_sort s z))).
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
  - exists (succ_sort (max_sort s z)). apply type_Heq.
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
    + eapply type_Lambda ; eassumption.
    + eapply type_Lambda ; eassumption.
  - exists (succ_sort z). apply type_Heq.
    + change (sSort z) with ((sSort z){ 0 := v1 }).
      eapply typing_subst ; eassumption.
    + change (sSort z) with ((sSort z){ 0 := v2 }).
      eapply typing_subst ; eassumption.
    + eapply type_App ; eassumption.
    + eapply type_App ; eassumption.
  - exists (succ_sort (succ_sort s)). apply type_Heq.
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq.
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_Refl ; eassumption.
    + eapply type_Refl ; eassumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). eapply type_Eq ; try assumption.
    apply type_Sort. apply (typing_wf H).
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - exists (succ_sort s). apply type_Heq ; try assumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
  - destruct (typed_ind_type hg isdecl) as [s h].
    exists s.
    change (sSort s) with (lift #|Γ| #|@nil scontext_decl| (sSort s)).
    replace (sind_type decl)
      with (lift #|Γ| #|@nil scontext_decl| (sind_type decl))
      by (erewrite lift_ind_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - exists s. assumption.
Defined.

Lemma eq_typing :
  forall {Σ Γ t u T},
    type_glob Σ ->
    Σ ;;; Γ |-i t = u : T ->
    (Σ ;;; Γ |-i t : T) * (Σ ;;; Γ |-i u : T).
Proof.
  intros Σ Γ t u T hg h.
  induction h ;
    repeat match goal with
           | H : ?A * ?B |- _ => destruct H
           end ;
    split ; try (now constructor + easy).
  all: try (econstructor ; eassumption).
  - eapply type_conv.
    + econstructor ; try eassumption.
      eapply type_conv.
      * econstructor ; eassumption.
      * econstructor ; eassumption.
      * apply eq_reflexivity. constructor ; assumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
    + apply eq_reflexivity.
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
  - eapply typing_subst ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor. apply (typing_wf t1).
  - constructor ; try eassumption.
    eapply ctx_conv.
    + eassumption.
    + econstructor.
      * apply eqctx_refl. now apply (typing_wf pi1_0).
      * eassumption.
  - eapply type_conv.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- eapply eqctx_refl. now apply (typing_wf pi1_1).
        -- eassumption.
      * eapply ctx_conv.
        -- eapply type_conv ; eassumption.
        -- econstructor.
           ++ apply eqctx_refl. now apply (typing_wf pi1_1).
           ++ eassumption.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
    + apply eq_symmetry. apply cong_Prod.
      * assumption.
      * eapply eqctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
  - econstructor.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- econstructor.
           ++ eassumption.
           ++ eapply ctx_conv ; [ eassumption |].
              econstructor.
              ** apply eqctx_refl. now apply (typing_wf pi1_2).
              ** eassumption.
        -- eapply cong_Prod ; eassumption.
      * econstructor ; eassumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u1 }).
      eapply typing_subst ; eassumption.
    + change (sSort s2) with ((sSort s2){0 := u2}).
      eapply pre_cong_subst1.
      * assumption.
      * eapply eq_symmetry. eassumption.
      * eapply eq_symmetry. assumption.
      * assumption.
      * assumption.
  - constructor.
    + assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
  - eapply type_conv ; [ eapply type_Refl | .. ].
    + eassumption.
    + eapply type_conv ; eassumption.
    + constructor ; eassumption.
    + apply eq_symmetry. apply cong_Eq ; assumption.
  - eapply type_conv ; [ econstructor | .. ].
    1: eassumption.
    all: try (econstructor ; eassumption).
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * eapply cong_Eq.
        -- match goal with
           | |- _ ;;; _ |-i _ = _ : ?S =>
             change S with (lift0 1 S)
           end.
           eapply cong_lift01 ; eassumption.
        -- eapply cong_lift01 ; eassumption.
        -- apply eq_reflexivity.
           eapply type_conv ; [ eapply type_Rel | .. ].
           ++ econstructor.
              ** now apply (typing_wf pi1_2).
              ** eassumption.
           ++ instantiate (1 := s1).
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
           ++ cbn. apply eq_reflexivity.
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * econstructor.
        -- eassumption.
        -- eapply type_conv ; eassumption.
        -- eapply type_conv ; eassumption.
      * apply cong_Eq ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * instantiate (1 := s2).
        change (sSort s2) with ((sSort s2){ 1 := u2 }{ 0 := sRefl A2 u2 }).
        eapply typing_subst2.
        -- assumption.
        -- eassumption.
        -- eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_conv ; [ eapply type_Refl | .. ].
           ++ eassumption.
           ++ eapply type_conv ; eassumption.
           ++ eapply type_Eq ; eassumption.
           ++ apply eq_symmetry. apply cong_Eq.
              ** assumption.
              ** assumption.
              ** apply eq_reflexivity. assumption.
      * match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (S{1 := u1}{0 := sRefl A1 u1})
        end.
        eapply pre_cong_subst2.
        -- assumption.
        -- eassumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply cong_Refl ; eassumption.
        -- assumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply ctx_conv.
           ++ eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
              ** exact pi2_1.
              ** assumption.
              ** assumption.
           ++ cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
              econstructor.
              ** eapply eqctx_refl. eapply typing_wf. eassumption.
              ** eapply eq_symmetry. eapply cong_Eq.
                 all: try eapply eq_reflexivity.
                 all: eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_Refl ; eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply typing_subst2.
      * assumption.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
    + eapply eq_symmetry.
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply pre_cong_subst2.
      * assumption.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
      * assumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00.
        eapply ctx_conv.
        -- eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
           ++ exact pi2_1.
           ++ assumption.
           ++ assumption.
        -- cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
           econstructor.
           ++ eapply eqctx_refl. eapply typing_wf. eassumption.
           ++ eapply eq_symmetry. eapply cong_Eq.
              all: try eapply eq_reflexivity.
              all: eassumption.
      * cbn. rewrite !lift_subst, lift00.
        assumption.
  - eapply type_conv.
    + eapply type_Transport ; try eassumption.
      * eapply type_conv.
        -- eassumption.
        -- apply type_Eq.
           ++ apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
        -- eapply cong_Eq.
           ++ eapply eq_reflexivity.
              apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
      * eapply type_conv ; eassumption.
    + eassumption.
    + eapply eq_symmetry. assumption.
  - eapply type_Heq ; try assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
      Unshelve. 1-3: exact nAnon. cbn. omega.
  - eapply type_conv.
    + eapply type_HeqRefl ; try eassumption.
      eapply type_conv ; eassumption.
    + eapply type_Heq ; try assumption ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; assumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_conv.
    + eapply type_HeqTransport ; [ .. | eassumption ] ; eassumption.
    + eapply type_Heq ; try eassumption.
      eapply type_Transport ; eassumption.
    + eapply eq_symmetry.
      eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      eapply cong_Transport ; try eapply eq_reflexivity ; eassumption.
  - eapply type_conv.
    + eapply type_CongProd ; try eassumption.
      eapply type_conv ; try eassumption.
      * eapply type_Heq.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @typing_subst with (B := sSort z).
           ++ assumption.
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @typing_subst with (B := sSort z).
           ++ assumption.
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
      * eapply cong_Heq. all: try eapply eq_reflexivity.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ assumption.
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ assumption.
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
    + eapply type_Heq.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq. all: try eapply eq_reflexivity.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
  - eapply type_conv.
    + eapply type_CongLambda ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** assumption.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- eapply type_conv ; eassumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** assumption.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- eapply type_conv ; eassumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; eassumption.
      * eapply type_conv ; eassumption.
    + eapply type_Heq.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Lambda ; eassumption.
      * eapply type_Lambda ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
  - eapply type_conv.
    + eapply type_CongApp ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv.
        -- eassumption.
        -- eapply type_Heq.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_conv ; try exact t1.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
           ++ eapply type_conv ; try exact t2.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
        -- eapply cong_Heq.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
    + eapply type_Heq.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply type_App ; eassumption.
      * eapply type_App ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
        -- assumption.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
        -- assumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_conv.
    + eapply type_ProjTe with (A1 := A1) (A2 := A2) ; eassumption.
    + eapply type_Heq ; try eassumption.
      * eapply type_ProjT1 with (A2 := A2) ; eassumption.
      * eapply type_ProjT2 with (A1 := A1) ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      * eapply cong_ProjT1 with (A2 := A2) ; eassumption.
      * eapply cong_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_HeqToEq ; try eassumption.
    eapply type_HeqRefl ; eassumption.
Defined.

Corollary full_cong_subst' :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    type_glob Σ ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A hg ht hu.
  destruct (eq_typing hg ht) as [_ ht2].
  destruct (eq_typing hg hu) as [hu1 _].
  eapply eq_transitivity.
  - exact (cong_subst ht hg hu1).
  - exact (cong_substs ht2 hg hu hu1).
Defined.

Lemma cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n hg ht hu.
  eapply @full_cong_subst' with (Δ := []) ; eassumption.
Defined.

Lemma cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 hg ht hu hv.
  eapply @full_cong_subst' with (Δ := []).
  - assumption.
  - eapply @full_cong_subst' with (Δ := [ svass nb B ]).
    + assumption.
    + exact ht.
    + assumption.
  - cbn. assumption.
Defined.

Lemma sorts_in_sort :
  forall {Σ Γ s1 s2 s},
    Σ ;;; Γ |-i sSort s1 : sSort s ->
    Σ ;;; Γ |-i sSort s2 : sSort s ->
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s.
Admitted.

(* Fixpoint strengthen_sort' {Σ Γ s A} (h : Σ ;;; Γ |-i sSort s : A) {struct h} : *)
(*   forall {z B}, *)
(*     Σ ;;; Γ |-i A = B : sSort z -> *)
(*     Σ ;;; [] |-i B : sSort z -> *)
(*     Σ ;;; [] |-i sSort s : B *)

(* with strengthen_eqsort {Σ Γ s z A} *)
(*   (h : Σ ;;; Γ |-i sSort s = A : sSort z) {struct h} : *)
(*   Σ ;;; [] |-i A : sSort z -> *)
(*   Σ ;;; [] |-i sSort s = A : sSort z. *)
(* Proof. *)
(*   - dependent destruction h ; intros z C he hC. *)
(*     + pose proof (strengthen_eqsort _ _ _ _ _ he hC). *)
(*       eapply type_conv. *)
(*       * eapply type_Sort. constructor. *)
(*       * eassumption. *)
(*       * assumption. *)
(*     + cheat. *)
(*   - cheat. *)
(* Defined. *)

(* Lemma strengthen_sort' : *)
(*   forall {Σ Γ s A}, *)
(*     Σ ;;; Γ |-i sSort s : A -> *)
(*     forall {z B}, *)
(*       Σ ;;; Γ |-i A = B : sSort z -> *)
(*       Σ ;;; [] |-i B : sSort z -> *)
(*       Σ ;;; [] |-i sSort s : B. *)
(* Proof. *)
(*   intros Σ Γ s A hs. *)
(*   dependent induction hs ; intros z C he hA. *)
(*   - eapply type_Sort. constructor. *)
(*   - *)


Lemma strengthen_sort :
  forall {Σ Γ Δ s z},
    Σ ;;; Γ |-i sSort s : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s : sSort z.
Admitted.

Lemma strengthen_sort_eq :
  forall {Σ Γ Δ s1 s2 z},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s1 = sSort s2 : sSort z.
Admitted.

Lemma cong_succ_sort :
  forall {Σ Γ s1 s2 s3},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s3 ->
    Σ ;;; Γ |-i sSort (succ_sort s1) = sSort (succ_sort s2) : sSort (succ_sort s3).
Admitted.

(* Lemma uniqueness_ctx : *)
(*   forall {Σ Γ u A}, *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     forall {Δ} *)

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    ∑ s, Σ ;;; Γ |-i A = B : sSort s.
Proof.
  (* intros Σ Γ A B u hu1. *)
  (* dependent induction hu1 ; intros hu2 ; dependent induction hu2. *)
  (* - eexists. cheat. *)
  (* - destruct (IHhu2_1 w isdecl) as [s' h']. *)
  (*   eexists. eapply eq_transitivity. *)
  (*   + exact h'. *)
  (*   + eapply eq_conv. *)
  (*     * exact e. *)
  (*     * (* This bit I usually use uniqueness to conclude... *)
  (*          This means we might need a stronger induction hypothesis to go. *)
  (*        *) *)
  (*       cheat. *)
  (* - *)
Admitted.