(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

(** Checking equality *)

Section EqualityDec.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition hΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct hΣ, Hφ; now constructor.
  Defined.

  Definition conv_pb_relb pb :=
    match pb with
    | Conv => check_eqb_universe G
    | Cumul => check_leqb_universe G
    end.
  
  Definition eqb_termp_napp pb napp :=
    eqb_term_upto_univ_napp Σ (check_eqb_universe G) (conv_pb_relb pb) napp.

  Lemma eqb_termp_napp_spec pb napp t u :
    eqb_termp_napp pb napp t u ->
    eq_termp_napp pb Σ napp t u.
  Proof.
    pose proof hΣ'.
    apply eqb_term_upto_univ_impl.
    - intros u1 u2.
      eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
      + sq. now eapply wf_ext_global_uctx_invariants.
      + sq; now eapply global_ext_uctx_consistent.
      + assumption.
    - intros u1 u2.
      destruct pb.
      + eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq; now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
      + eapply (check_leqb_universe_spec' G (global_ext_uctx Σ)).
        * sq; now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
    - intros u1 u2.
      destruct pb.
      + eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq. now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
      + simpl.
        intros cu.
        eapply eq_universe_leq_universe.
        revert cu.
        eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq. now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
  Qed.

  Definition eqb_termp pb := (eqb_termp_napp pb 0).
  Definition eqb_term := (eqb_termp Conv).
  Definition leqb_term := (eqb_termp Cumul).

  Lemma leqb_term_spec t u :
    leqb_term t u ->
    leq_term Σ (global_ext_constraints Σ) t u.
  Proof.
    intros.
    now apply eqb_termp_napp_spec in H.
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma eqb_term_spec t u :
    eqb_term t u ->
    eq_term Σ t u.
  Proof.
    intros.
    now apply eqb_termp_napp_spec in H.
  Qed.

  Lemma eqb_term_refl :
    forall t, eqb_term t t.
  Proof.
    intro t. eapply eqb_term_upto_univ_refl.
    all: apply check_eqb_universe_refl.
  Qed.

  Fixpoint eqb_ctx (Γ Δ : context) : bool :=
    match Γ, Δ with
    | [], [] => true
    | {| decl_name := na1 ; decl_body := None ; decl_type := t1 |} :: Γ,
      {| decl_name := na2 ; decl_body := None ; decl_type := t2 |} :: Δ =>
      eqb_binder_annot na1 na2 && eqb_term t1 t2 && eqb_ctx Γ Δ
    | {| decl_name := na1 ; decl_body := Some b1 ; decl_type := t1 |} :: Γ,
      {| decl_name := na2 ; decl_body := Some b2 ; decl_type := t2 |} :: Δ =>
      eqb_binder_annot na1 na2 && eqb_term b1 b2 && eqb_term t1 t2 && eqb_ctx Γ Δ
    | _, _ => false
    end.

  Lemma eqb_binder_annot_spec {A} na na' : eqb_binder_annot (A:=A) na na' -> eq_binder_annot (A:=A) na na'.
  Proof. case: eqb_annot_reflect => //. Qed.

  Lemma eqb_ctx_spec :
    forall Γ Δ,
      eqb_ctx Γ Δ ->
      eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ.
  Proof.
    intros Γ Δ h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, h |- *.
    all: destruct Δ as [| [na' [b'|] A'] Δ].
    all: try discriminate.
    - constructor.
    - simpl in h. apply andb_andI in h as [[[h1 h2]%andb_and h3]%andb_and h4].
      constructor; auto; constructor; auto.
      + now apply eqb_binder_annot_spec in h1.
      + eapply eqb_term_spec. assumption.
      + eapply eqb_term_spec. assumption.
    - simpl in h. apply andb_and in h as [[h1 h2]%andb_and h3].
      constructor; auto; constructor.
      + now apply eqb_binder_annot_spec.
      + eapply eqb_term_spec. assumption.
  Qed.

  Definition eqb_opt_term (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term t u
    | None, None => true
    | _, _ => false
    end.

  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term false Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn => //.
    apply eqb_term_spec; tea.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_binder_annot d.(decl_name) d'.(decl_name) && 
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl false Σ (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. rtoProp. apply eqb_opt_term_spec in H1.
    eapply eqb_term_spec in H0; tea.
    eapply eqb_binder_annot_spec in H.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; simpl in * => //;
    repeat constructor; eauto.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context false Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_fold_All2.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

End EqualityDec.