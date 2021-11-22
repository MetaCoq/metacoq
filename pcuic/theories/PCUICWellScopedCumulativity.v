(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
     PCUICContextRelation PCUICSigmaCalculus PCUICContextReduction PCUICContextRelation
     PCUICParallelReduction PCUICParallelReductionConfluence
     PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICConfluence PCUICSubstitution.

Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
From Equations Require Import Equations.

(* We show that conversion/cumulativity starting from well-typed terms is transitive.
  We first use typing to decorate the reductions/comparisons with invariants 
  showing that all the considered contexts/terms are well-scoped. In a second step
  we use confluence of one-step reduction on well-scoped terms [ws_red_confluence], which also 
  commutes with alpha,universe-equivalence of contexts and terms [red1_eq_context_upto_l].
  We can drop the invariants on free variables at each step as reduction preserves free-variables,
  so we also have [red_confluence]: as long as the starting contexts and terms are well-scoped 
  confluence holds. *)

(** We can now derive transitivity of the conversion relation on *well-scoped* 
  terms. To deal with the closedness side condition we put them in the definition
  of conversion/cumulativity: as terms need to move between contexts, and
  we sometimes need to consider conversion in open contexts, we work with
  them in an unpacked style.
  This allows to state theorems about conversion/cumulativity of general terms
  and contexts without wrapping/unwrapping them constantly into subsets.
*)

Reserved Notation " Σ ;;; Γ ⊢ t ≤[ le ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤[ le ]  u").

Notation is_open_term Γ := (on_free_vars (shiftnP #|Γ| xpred0)).
Notation is_open_decl Γ := (on_free_vars_decl (shiftnP #|Γ| xpred0)).
Notation is_closed_context := (on_free_vars_ctx xpred0).

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Inductive equality {cf} (le : bool) (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| equality_compare (t u : term) : 
  is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
  compare_term le Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ ⊢ t ≤[le] u
| equality_red_l (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  red1 Σ Γ t v -> Σ ;;; Γ ⊢ v ≤[le] u -> Σ ;;; Γ ⊢ t ≤[le] u
| equality_red_r (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  Σ ;;; Γ ⊢ t ≤[le] v -> red1 Σ Γ u v -> Σ ;;; Γ ⊢ t ≤[le] u
where " Σ ;;; Γ ⊢ t ≤[ le ] u " := (equality le Σ Γ t u) : type_scope.
Derive Signature NoConfusion for equality.

Notation " Σ ;;; Γ ⊢ t ≤ u " := (equality true Σ Γ t u) (at level 50, Γ, t, u at next level,
    format "Σ  ;;;  Γ  ⊢  t  ≤  u") : type_scope.

Notation " Σ ;;; Γ ⊢ t = u " := (equality false Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  =  u") : type_scope.

#[global]
Instance compare_term_refl {cf} le Σ : Reflexive (compare_term le Σ Σ).
Proof.
  intros t; destruct le; unfold compare_term; cbn; reflexivity.
Qed.

#[global]
Instance compare_term_sym {cf} Σ : Symmetric (compare_term false Σ Σ).
Proof.
  now intros t u; unfold compare_term; cbn; symmetry.
Qed.

#[global]
Instance compare_term_trans {cf} le Σ : Transitive (compare_term le Σ Σ).
Proof.
  intros t u v; unfold compare_term; cbn; intros.
  destruct le; cbn in *; etransitivity; tea.
Qed.

Lemma equality_refl' {le} {cf} {Σ} (Γ : closed_context) (t : open_term Γ) : equality le Σ Γ t t.
Proof.
  constructor; eauto with fvs. reflexivity. 
Qed.

#[global]
Instance equality_sym {cf Σ Γ} : Symmetric (equality false Σ Γ).
Proof.
  move=> x y; elim.
  - move=> t u clΓ clt clu eq.
    constructor 1; eauto with fvs.
    cbn in *; now symmetry.
  - move=> t u v clΓ clt clu clv r c c'.
    econstructor 3; tea.
  - move=> t u v clΓ clt clu clv r c c'.
    econstructor 2; tea.
Qed.

Lemma red1_is_open_term {cf : checker_flags} {Σ} {wfΣ : wf Σ} {Γ : context} x y : 
  red1 Σ Γ x y ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  is_open_term Γ y.
Proof.
  intros. eapply red1_on_free_vars; eauto with fvs.
Qed.
#[global] Hint Immediate red1_is_open_term : fvs.

Lemma red_is_open_term {cf : checker_flags} {Σ} {wfΣ : wf Σ} {Γ : context} x y : 
  red Σ Γ x y ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  is_open_term Γ y.
Proof.
  intros. eapply red_on_free_vars; eauto with fvs.
Qed.
#[global] Hint Immediate red_is_open_term : fvs.

Lemma equality_is_open_term {cf : checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} : 
  equality le Σ Γ x y ->
  [&& is_closed_context Γ, is_open_term Γ x & is_open_term Γ y].
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma equality_is_closed_context {cf : checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} : 
  equality le Σ Γ x y -> is_closed_context Γ.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma equality_is_open_term_left {cf : checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ : context} {x y} : 
  equality le Σ Γ x y -> is_open_term Γ x.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1 ?i2.
Qed.

Lemma equality_is_open_term_right {cf : checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {x y} : 
  equality le Σ Γ x y -> is_open_term Γ y.
Proof.
  now induction 1; rewrite ?i ?i0 ?i1.
Qed.

#[global] Hint Resolve equality_is_closed_context equality_is_open_term_left equality_is_open_term_right : fvs.

Lemma equality_alt `{cf : checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} Γ t u :
  Σ ;;; Γ ⊢ t ≤[le] u <~> 
  ∑ v v',
    [× is_closed_context Γ, is_open_term Γ t, is_open_term Γ u,
      red Σ Γ t v, red Σ Γ u v' & compare_term le Σ (global_ext_constraints Σ) v v'].
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & [-> _ -> redv redv' leqv]).
      rewrite i0 /=.
      exists v', v''. split; auto. now eapply red_step.
    + destruct IHX as (v' & v'' & [-> -> cl redv redv' leqv ]).
      exists v', v''. split; auto. now eapply red_step.
  - intros (v' & v'' & [clΓ clt clu redv redv' leqv]).
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv in u, v'', redv', leqv, clt, clu |- *.
    * induction redv' in x, leqv, clt, clu |- *.
    ** constructor; auto.
    ** econstructor 3; tas. 2:eapply IHredv'. all:tea; eauto with fvs.
    * econstructor 2; revgoals. eapply IHredv; cbn; eauto with fvs. all:eauto with fvs.
Qed.

Lemma equality_forget {cf:checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  equality le Σ Γ x y -> if le then cumul Σ Γ x y else conv Σ Γ x y.
Proof.
  induction 1.
  - destruct le; simpl in *; constructor; auto.
  - destruct le; econstructor 2; eauto.
  - destruct le; econstructor 3; eauto.
Qed.

Lemma equality_forget_cumul {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  equality true Σ Γ x y -> cumul Σ Γ x y.
Proof. apply (equality_forget (le:=true)). Qed.

Lemma equality_forget_conv {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {x y} :
  equality false Σ Γ x y -> conv Σ Γ x y.
Proof. apply (equality_forget (le:=false)). Qed.
#[global] Hint Resolve equality_forget_cumul equality_forget_conv : pcuic.

#[global]
Instance equality_trans {cf:checker_flags} {le} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} :
  Transitive (equality le Σ Γ).
Proof.
  move=> t u v /equality_alt [t' [u' [clΓ clt clu tt' uu' eq]]]
    /equality_alt[u'' [v' [_ clu' clv uu'' vv' eq']]].
  eapply equality_alt.
  destruct (red_confluence (Γ := exist Γ clΓ) (t:=exist u clu) uu' uu'') as [u'nf [ul ur]].
  destruct le; cbn in *.
  { eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; try tc.
    eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; try tc.
    exists tnf, unf.
    split; auto; eauto with fvs.
    - now transitivity t'.
    - now transitivity v'.
    - now transitivity u'nf. }
  { eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; try tc.
    eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; try tc.
    exists tnf, unf.
    split; eauto with fvs.
    - now transitivity t'.
    - now transitivity v'.
    - now transitivity u'nf. }
Qed.

Arguments wt_equality_dom {le cf Σ Γ T U}.
Arguments wt_equality_codom {le cf Σ Γ T U}.
Arguments wt_equality_eq {le cf Σ Γ T U}.

Section EqualityLemmas.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma isType_open {Γ T} : isType Σ Γ T -> on_free_vars (shiftnP #|Γ| xpred0) T.
  Proof.
    move/isType_closedPT. now rewrite closedP_shiftnP.
  Qed.

  Lemma wf_local_closed_context {Γ} : wf_local Σ Γ -> on_free_vars_ctx xpred0 Γ.
  Proof.
    move/PCUICClosed.closed_wf_local.
    now rewrite closed_ctx_on_ctx_free_vars on_free_vars_ctx_on_ctx_free_vars_closedP.
  Qed.

  Lemma into_equality {le} {Γ : context} {T U} : 
    (if le then Σ;;; Γ |- T <= U else Σ;;; Γ |- T = U) ->
    is_closed_context Γ -> is_open_term Γ T ->
    is_open_term Γ U ->
    Σ ;;; Γ ⊢ T ≤[le] U.
  Proof.
    destruct le.
    { induction 1.
      - constructor; auto.
      - intros. econstructor 2 with v; cbn; eauto with fvs.
      - econstructor 3 with v; cbn; eauto with fvs. }
    { induction 1.
      - constructor; auto.
        - econstructor 2 with v; cbn; eauto with fvs.
        - econstructor 3 with v; cbn; eauto with fvs. }
  Qed.

  Lemma isType_equality_refl {le} Γ T : isType Σ Γ T -> Σ ;;; Γ ⊢ T ≤[le] T.
  Proof. 
    intros H.
    pose proof (isType_wf_local H).
    eapply (equality_refl' (exist Γ (wf_local_closed_context X)) (exist T (isType_open H))).
  Qed.

  (** From well-typed to simply well-scoped equality. *)
  Lemma wt_equality_equality {le} {Γ : context} {T U} : 
    wt_equality le Σ Γ T U ->
    equality le Σ Γ T U.
  Proof.
    move=> [] dom codom equiv; cbn.
    generalize (wf_local_closed_context (isType_wf_local dom)).
    generalize (isType_open dom) (isType_open codom). clear -wfΣ equiv.
    intros. apply into_equality => //.
  Qed.

  Lemma wt_equality_trans le Γ :
    Transitive (wt_equality le Σ Γ).
  Proof.
    intros x y z cum cum'.
    have wscum := (wt_equality_equality cum).
    have wscum' := (wt_equality_equality cum').
    generalize (transitivity wscum wscum'). clear wscum wscum'.
    destruct cum, cum'; split=> //.
    apply equality_forget in X. now cbn in X.
  Qed.

  Global Instance conv_trans Γ : Transitive (wt_conv Σ Γ).
  Proof. apply wt_equality_trans. Qed.
  
  Global Instance cumul_trans Γ : Transitive (wt_cumul Σ Γ).
  Proof. apply wt_equality_trans. Qed.

End EqualityLemmas.

#[global] Hint Immediate isType_equality_refl : pcuic.

Record closed_relation {R : context -> term -> term -> Type} {Γ T U} :=
  { clrel_ctx : is_closed_context Γ;
    clrel_src : is_open_term Γ T;
    clrel_rel : R Γ T U }.
Arguments closed_relation : clear implicits.

#[global] Hint Immediate clrel_ctx clrel_src : fvs.

Definition closed_red1 Σ := (closed_relation (red1 Σ)).
Definition closed_red1_red1 {Σ Γ T U} (r : closed_red1 Σ Γ T U) := clrel_rel r.
#[global] Hint Resolve closed_red1_red1 : fvs.
Coercion closed_red1_red1 : closed_red1 >-> red1.

Lemma closed_red1_open_right {cf} {Σ Γ T U} {wfΣ : wf Σ} (r : closed_red1 Σ Γ T U) : is_open_term Γ U.
Proof.
  destruct r. eauto with fvs.
Qed.

Definition closed_red Σ := (closed_relation (red Σ)).
Definition closed_red_red {Σ Γ T U} (r : closed_red Σ Γ T U) := clrel_rel r.
#[global] Hint Immediate closed_red_red : fvs.
Coercion closed_red_red : closed_red >-> red.

Lemma closed_red_open_right {cf} {Σ Γ T U} {wfΣ : wf Σ} (r : closed_red Σ Γ T U) : is_open_term Γ U.
Proof.
  destruct r. eauto with fvs.
Qed.

From Equations.Type Require Import Relation_Properties.

(* \rightsquigarrow *)
Notation "Σ ;;; Γ ⊢ t ⇝ u" := (closed_red Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ⇝  u").

Lemma closed_red1_red {Σ Γ t t'} : closed_red1 Σ Γ t t' -> Σ ;;; Γ ⊢ t ⇝ t'.
Proof.
  intros []. split => //.
  now eapply red1_red.
Qed.

Lemma biimpl_introT {T} {U} : Logic.BiImpl T U -> T -> U.
Proof. intros [] => //. Qed.

Hint View for move/ biimpl_introT|2.

Lemma equality_refl {cf} {Σ} {le Γ t} : is_closed_context Γ -> is_open_term Γ t -> Σ ;;; Γ ⊢ t ≤[le] t.
Proof.
  move=> clΓ clt.
  constructor; cbn; eauto with fvs. destruct le; cbn; reflexivity.
Qed.
#[global] Hint Immediate equality_refl : pcuic.

Section RedConv.
  Context {cf} {Σ} {wfΣ : wf Σ}.

  Lemma red_conv {le Γ t u} : Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ≤[le] u.
  Proof.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r.
    - now apply equality_refl.
    - econstructor 2. 5:tea.
      all:eauto with fvs.
  Qed.

  Lemma red_equality_left {le Γ} {t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ u ≤[le] v -> Σ ;;; Γ ⊢ t ≤[le] v.
  Proof.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r; auto.
    econstructor 2. 5:tea. all:eauto with fvs.
  Qed.

  Lemma red_equality_right {le Γ t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ v ≤[le] u -> Σ ;;; Γ ⊢ v ≤[le] t.
  Proof.
    move=> [clΓ clT /clos_rt_rt1n_iff r].
    induction r; auto.
    econstructor 3. 5:eapply IHr. all:eauto with fvs.
  Qed.

  (* synonym of red_conv *)
  Lemma red_equality {le Γ t u} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ≤[le] u.
  Proof.
    move=> r; eapply red_equality_left; tea.
    eapply equality_refl; eauto with fvs.
  Qed.

  Lemma red_equality_inv {le Γ t u} :
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ u ≤[le] t.
  Proof.
    move=> r; eapply red_equality_right; tea.
    eapply equality_refl; eauto with fvs.
  Qed.
End RedConv.

#[global] Hint Resolve red_conv red_equality red_equality_inv : pcuic.

Set SimplIsCbn.

Ltac inv_on_free_vars :=
  repeat match goal with
  | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
  | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => unfold on_free_vars_decl, test_decl in H
  | [ H : is_true (_ && _) |- _ ] => 
    move/andP: H => []; intros
  | [ H : is_true (on_free_vars ?P ?t) |- _ ] => 
    progress (cbn in H || rewrite on_free_vars_mkApps in H);
    (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] || 
      eapply forallb_All in H); intros
  | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
    move/andP: H => []; rewrite ?shiftnP_xpredT; intros
  | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
    rewrite -> test_context_k_closed_on_free_vars_ctx in H
  end.

Notation byfvs := (ltac:(cbn; eauto with fvs)) (only parsing).


Definition conv_cum {cf:checker_flags} le Σ Γ T T' :=
  if le then Σ ;;; Γ |- T <= T' else Σ ;;; Γ |- T = T'.

Notation ws_decl Γ d := (on_free_vars_decl (shiftnP #|Γ| xpred0) d).
  
Definition equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) d d' :=
  (if le then cumul_decls else conv_decls) Σ Γ Γ' d d'.

Definition open_decl (Γ : context) := { d : context_decl | ws_decl Γ d }.
Definition open_decl_proj {Γ : context} (d : open_decl Γ) := proj1_sig d.
Coercion open_decl_proj : open_decl >-> context_decl.

Definition vass_open_decl {Γ : closed_context} (na : binder_annot name) (t : open_term Γ) : open_decl Γ :=
  exist (vass na t) (proj2_sig t).

(* Definition vdef_open_decl {Γ : closed_context} (na : binder_annot name) (b t : open_term Γ) : open_decl Γ :=
  exist (vdef na b t) (introT andP (conj (proj2_sig b) (proj2_sig t))). *)
  
Inductive All_decls_alpha_le {le} {P : bool -> term -> term -> Type} :
  context_decl -> context_decl -> Type :=
| all_decls_alpha_vass {na na' : binder_annot name} {t t' : term}
  (eqna : eq_binder_annot na na')
  (eqt : P le t t') :
  All_decls_alpha_le (vass na t) (vass na' t')

| all_decls_alpha_vdef {na na' : binder_annot name} {b t b' t' : term}
  (eqna : eq_binder_annot na na')
  (eqb : P false b b')
  (eqt : P le t t') :
  All_decls_alpha_le (vdef na b t) (vdef na' b' t').
Derive Signature NoConfusion for All_decls_alpha_le.
Arguments All_decls_alpha_le : clear implicits.
  
Definition equality_open_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext)
  (Γ : context) (d : context_decl) (d' : context_decl) :=
  All_decls_alpha_le le (fun le => @equality cf le Σ Γ) d d'.

Lemma equality_open_decls_wf_decl_left {cf} {le} {Σ} {wfΣ : wf Σ} {Γ d d'} :
  equality_open_decls le Σ Γ d d' -> ws_decl Γ d.
Proof.
  intros []; cbn; eauto with fvs.
Qed.

Lemma equality_open_decls_wf_decl_right {cf} {le} {Σ} {wfΣ : wf Σ} {Γ d d'} :
  equality_open_decls le Σ Γ d d' -> ws_decl Γ d'.
Proof.
  intros []; cbn; eauto with fvs.
Qed.
#[global] Hint Immediate equality_open_decls_wf_decl_left equality_open_decls_wf_decl_right : fvs.
 
Lemma equality_open_decls_equality_decls {cf : checker_flags} (le : bool) {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} {d d'} :
  equality_open_decls le Σ Γ d d' -> 
  equality_decls le Σ Γ Γ' d d'.
Proof.
  intros. intuition eauto with fvs.
  destruct X; destruct le; constructor; pcuic.
Qed.

(* Definition equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) : context_decl -> context_decl -> Type :=
  fun d d' => 
    #|Γ| = #|Γ'| × equality_decls le Σ Γ Γ' d d' ×
    [&& on_free_vars_ctx xpred0 Γ, on_free_vars_ctx xpred0 Γ', ws_decl Γ d & ws_decl Γ' d']. *)

Lemma into_equality_open_decls {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ}
  (Γ Γ' : context) d d' :
  equality_decls le Σ Γ Γ' d d' -> 
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ d' ->
  equality_open_decls le Σ Γ d d'.
Proof.
  case: le; move=> eq clΓ clΓ' isd isd'; 
    destruct eq; cbn; constructor; auto; try inv_on_free_vars; eauto with fvs.
  all:try apply: into_equality; tea; eauto 3 with fvs.
Qed.
 
Lemma equality_open_decls_inv {cf} (le : bool) {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} {d d'} :
  equality_open_decls le Σ Γ d d' -> 
  [× on_free_vars_ctx xpred0 Γ, is_open_decl Γ d, is_open_decl Γ d' & equality_decls le Σ Γ Γ' d d'].
Proof.
  intros. split; eauto with fvs.
  - destruct X; now destruct eqt.
  - now eapply equality_open_decls_equality_decls.
Qed.
(* 
Lemma equality_open_decls_forget {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} {d d' : context_decl} :
  equality_open_decls le Σ Γ d d' ->
  #|Γ| = #|Γ'| ->
  is_closed_context Γ' ->
  equality_decls le Σ Γ Γ' d d'. 
Proof.
  rewrite /equality_open_decls /equality_decls => a hlen; split => //.
  rewrite -hlen.
  split.
  2:{ destruct a; apply/and4P; split; intuition eauto with fvs.
      destruct w; auto.
      destruct w; auto. }
  destruct a. simpl. red.
  eapply equality_forget in w.
  destruct le; constructor; auto.
  eapply equality_forget in w.
  eapply equality_forget in w0.
  destruct le; constructor; auto.
Qed.
   *)
#[global]
Instance equality_open_decls_trans {cf : checker_flags} (le : bool) {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} :
  Transitive (equality_open_decls le Σ Γ).
Proof.
  intros d d' d''.
  rewrite /equality_open_decls.
  intros ond ond'; destruct ond; depelim ond'.
  econstructor; now etransitivity.
  econstructor; etransitivity; tea.
Qed.
(* 
Instance equality_decls_trans {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ'} : Transitive (equality_decls le Σ Γ Γ').
Proof.
  intros Δ Δ' Δ''.
  move=> a; move: a.1 => HΓ. move: a.2.2 => /and4P[] _ onΓ' _ _. move: a.
  move/into_equality_open_decls => [onΓ [isd [isde' eq]]].
  move/into_equality_open_decls => [onΓ'' [isd' [isde'' eq']]].
  assert (eq'' := transitivity eq eq').
  eapply equality_open_decls_forget in eq''; tea.
Qed. *)
(* (* 
Lemma into_equality_decls {cf : checker_flags} {le : bool} {Σ : global_env_ext}
  {Γ Γ'} {d d' : context_decl} (c : equality_decls le Σ Γ Γ' d d') :
  #|Γ| = #|Γ'| ->
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ' d' ->
  equality_decls le Σ Γ Γ' d d'.
Proof.
  rewrite /equality_decls => len onΓ onΓ' ond ond'. 
  repeat split => //.
  now rewrite onΓ onΓ' ond ond'.
Qed. *)

Lemma equality_decls_trans {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ'} (d d' d'' : context_decl) (c : equality_decls le Σ Γ Γ' d d')
  (c' : equality_decls le Σ Γ Γ' d' d'') : 
  #|Γ| = #|Γ'| ->
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ' d' ->
  is_open_decl Γ' d'' ->
  equality_decls le Σ Γ Γ' d d''.
Proof.
  move=> len onΓ onΓ' ond ond' ond''.
  move: (into_equality_decls c len onΓ onΓ' ond ond') => l.
  rewrite -len in ond'.
  move: (into_equality_decls c' len onΓ onΓ' ond' ond'') => r.
  apply (transitivity l r).
Qed. *)

Inductive wt_equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) : context_decl -> context_decl -> Type :=
| wt_equality_vass {na na' : binder_annot name} {T T' : term} :
    isType Σ Γ T -> isType Σ Γ' T' ->
    conv_cum le Σ Γ T T' ->
    eq_binder_annot na na' ->
    wt_equality_decls le Σ Γ Γ' (vass na T) (vass na' T')
| wt_equality_vdef {na na' : binder_annot name} {b b' T T'} :
    eq_binder_annot na na' ->
    isType Σ Γ T -> isType Σ Γ' T' ->
    Σ ;;; Γ |- b : T -> Σ ;;; Γ' |- b' : T' ->
    Σ ;;; Γ |- b = b' ->
    conv_cum le Σ Γ T T' ->
    wt_equality_decls le Σ Γ Γ' (vdef na b T) (vdef na' b' T').
Derive Signature for wt_equality_decls.

(* Definition ws_context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) :=
  All2_fold (equality_decls le Σ). *)

(* Notation ws_cumul_context Σ := (ws_context_equality true Σ).
Notation ws_conv_context Σ := (ws_context_equality false Σ). *)
    
Definition context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) :=
  All2_fold (fun Γ Γ' => equality_open_decls le Σ Γ) Γ Γ'.

(* 
Lemma ws_context_equality_closed_right {cf:checker_flags} {le : bool} {Σ : global_env_ext} {Γ Γ'}:
  ws_context_equality le Σ Γ Γ' -> is_closed_context Γ'.
Proof.
  intros X. red in X.
  induction X; auto.
  destruct p as [? []].
  rewrite on_free_vars_ctx_snoc IHX /=.
  now move/and4P: i => [].
Qed.

Lemma ws_context_equality_closed_left {cf:checker_flags} {le : bool} {Σ : global_env_ext} {Γ Γ'}:
  ws_context_equality le Σ Γ Γ' -> is_closed_context Γ.
Proof.
  intros X. red in X.
  induction X; auto.
  destruct p as [? []].
  rewrite on_free_vars_ctx_snoc IHX /=.
  now move/and4P: i => [].
Qed. *)

Lemma context_equality_closed_right {cf:checker_flags} {le : bool} {Σ} {wfΣ : wf Σ} {Γ Γ'}:
  context_equality le Σ Γ Γ' -> is_closed_context Γ'.
Proof.
  intros X. red in X.
  induction X; auto.
  rewrite on_free_vars_ctx_snoc IHX /= //.
  rewrite -(All2_fold_length X); eauto with fvs.
Qed.

Lemma context_equality_closed_left {cf:checker_flags} {le : bool} {Σ} {wfΣ : wf Σ} {Γ Γ'}:
  context_equality le Σ Γ Γ' -> is_closed_context Γ.
Proof.
  intros X. red in X.
  induction X; auto.
  rewrite on_free_vars_ctx_snoc IHX /=.
  eauto with fvs.
Qed.

#[global] Hint Resolve context_equality_closed_left context_equality_closed_right : fvs.

(* Lemma into_context_equality {cf:checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} :
  ws_context_equality le Σ Γ Γ' ->
  context_equality le Σ Γ Γ'.
Proof.
  rewrite /ws_context_equality /context_equality.
  intros a. eapply PCUICContextRelation.All2_fold_impl_ind; tea.
  clear -wfΣ; intros Γ Δ d d' wseq IH hd.
  now destruct (into_equality_open_decls le hd) as [clΓ [isd [isd' eq]]].
Qed.

Lemma from_context_equality {cf:checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} :
  context_equality le Σ Γ Γ' ->
  ws_context_equality le Σ Γ Γ'.
Proof.
  rewrite /ws_context_equality /context_equality.
  intros a; eapply PCUICContextRelation.All2_fold_impl_ind; tea.
  clear -wfΣ; intros Γ Δ d d' wseq IH hd. cbn in hd.
  destruct hd.
  rewrite /equality_decls. split => //.
  apply (All2_fold_length IH). split.
  rewrite /equality_decls.
  destruct le; constructor; auto; now apply equality_forget in w.
  destruct w; cbn; rewrite -(All2_fold_length wseq); rtoProp; eauto with fvs.
  pose proof (All2_fold_length wseq).
  destruct le; constructor; auto. now apply equality_forget in w.
  destruct w; cbn; rewrite -(All2_fold_length wseq); rtoProp; eauto with fvs.


  apply equality_forget in w. apply equality_forget in w0.
  destruct le; constructor; auto.
  now rewrite clΓ clΔ isd /= -(All2_fold_length IH) isd'.
Qed. *)



Definition wt_context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) :=
  All2_fold (wt_equality_decls le Σ).

Notation wt_cumul_context Σ := (wt_context_equality true Σ).
Notation wt_conv_context Σ := (wt_context_equality false Σ).

Definition compare_universe {cf} le Σ :=
  if le then leq_universe Σ else eq_universe Σ.

Section WtContextConversion.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Definition wt_decl Γ d := 
    match d with
    | {| decl_body := None; decl_type := ty |} => isType Σ Γ ty
    | {| decl_body := Some b; decl_type := ty |} => isType Σ Γ ty × Σ ;;; Γ |- b : ty
    end.

  Lemma wf_local_All_fold Γ : 
    wf_local Σ Γ <~>
    All_fold wt_decl Γ.
  Proof.
    split.
    - induction 1; constructor; auto.
      red in t0, t1. cbn. split; auto.
    - induction 1; [constructor|].
      destruct d as [na [b|] ty]; cbn in p; constructor; intuition auto.
  Qed.

  Lemma wt_context_equality_forget {le} {Γ Γ' : context} :
    wt_context_equality le Σ Γ Γ' ->
    [× wf_local Σ Γ, wf_local Σ Γ' &
      if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'].
  Proof.
    move=> wteq.
    apply (All2_fold_impl (Q:=fun Γ Γ' d d' => wt_decl Γ d × wt_decl Γ' d' × 
      (if le then cumul_decls Σ Γ Γ' d d' else conv_decls Σ Γ Γ' d d'))) in wteq.
    2:{ intros ???? []; intuition (cbn; try constructor; auto).
        all:cbn in *; destruct le; constructor; auto. }
    eapply All2_fold_All_fold_mix_inv in wteq as [wteq [wfΓ wfΓ']].
    eapply wf_local_All_fold in wfΓ. eapply wf_local_All_fold in wfΓ'.
    split; auto.
    destruct le; auto.
  Qed.

  Lemma into_wt_context_equality {le} {Γ Γ' : context} {T U : term} :
    wf_local Σ Γ -> wf_local Σ Γ' ->
    (if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ') ->
    wt_context_equality le Σ Γ Γ'.
  Proof.
    move=> /wf_local_All_fold wfΓ /wf_local_All_fold wfΓ'.
    destruct le=> eq.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
  Qed.

  Lemma wt_ws_context_equality {le} {Γ Γ' : context} {T U : term} :
    wt_context_equality le Σ Γ Γ' ->
    context_equality le Σ Γ Γ'.
  Proof.
    intros a; eapply All2_fold_impl_ind; tea.
    intros ???? wt ws eq; 
    pose proof (All2_fold_length wt).
    destruct eq.
    - pose proof (isType_wf_local i).
      eapply wf_local_closed_context in X.
      eapply isType_open in i. apply isType_open in i0.
      eapply into_equality_open_decls with Δ; eauto with fvs. rewrite /equality_decls.
      destruct le; constructor; auto.
      rewrite (All2_fold_length ws) //.
    - pose proof (isType_wf_local i).
      eapply wf_local_closed_context in X.
      eapply isType_open in i. apply isType_open in i0.
      eapply PCUICClosed.subject_closed in t.
      eapply PCUICClosed.subject_closed in t0.
      eapply (@closedn_on_free_vars xpred0) in t.
      eapply (@closedn_on_free_vars xpred0) in t0.
      eapply into_equality_open_decls with Δ; eauto with fvs. rewrite /equality_decls.
      destruct le; constructor; auto.
      rewrite (All2_fold_length ws) //; eauto with fvs.
  Qed.

  Lemma context_equality_inv {le} {Γ Γ' : context} :
    context_equality le Σ Γ Γ' ->
    [× on_free_vars_ctx xpred0 Γ, on_free_vars_ctx xpred0 Γ' &
      if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'].
  Proof.
    move=> wteq.
    split; eauto with fvs.
    destruct le. eapply All2_fold_impl; tea; move=> ???? []; constructor; eauto with pcuic.
    all:try now eapply equality_forget in p.
    all:try now eapply equality_forget in p0.
    eapply All2_fold_impl; tea; move=> ???? []; constructor; eauto with pcuic.
    all:try now eapply equality_forget in p.
    all:try now eapply equality_forget in p0.
  Qed.
  
  #[global]
  Instance equality_open_decls_sym Γ : Symmetric (equality_open_decls false Σ Γ).
  Proof.
    move=> x y [na na' T T' eqan cv|na na' b b' T T' eqna eqb eqT];
    constructor; now symmetry.
  Qed.

  Lemma context_equality_forget {le Γ Γ'} : 
    context_equality le Σ Γ Γ' ->
    if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'.
  Proof.
    now move/context_equality_inv => [].
  Qed.
  
  Lemma context_equality_refl le Γ : is_closed_context Γ -> context_equality le Σ Γ Γ.
  Proof.
    move=> onΓ. cbn.
    move/on_free_vars_ctx_All_fold: onΓ => a.
    eapply (All_fold_All2_fold_impl a). clear -wfΣ.
    move=> Γ d a IH ond.
    move/on_free_vars_ctx_All_fold: a => clΓ.
    eapply (into_equality_open_decls _ Γ).
    rewrite /equality_decls.
    destruct le. reflexivity. reflexivity.
    all:eauto with fvs.
  Qed.
  
End WtContextConversion.


(** 
The "natural" definition of conversion is given by [conv0]. It is the reflexive
symmetric transitive closure of beta redution + equality modulo universes.
It turns out to be equivalent to [conv1]: only beta reduction needs to be symmetrized.
Cumulativity is defined in the same style ([cumul1]), not symmetrizing [leq_term] because
it is oriented.

Those definitions are NOT used in the definition of typing. Instead we use [cumul] and
[conv] which are defined as "reducing to a common term". It turns out to be equivalent
to [conv1] and [cumul1] by confluence. It will be shown afterward, in PCUICConversion.v.
*)

Section ConvCumulDefs.
  Context {cf:checker_flags} (Σ : global_env_ext) (Γ : context).

  Definition conv0 : relation term
    := clos_refl_sym_trans (relation_disjunction (closed_red1 Σ Γ) (eq_term Σ Σ)).

  Definition genconv1 le : relation term
    := clos_refl_trans (relation_disjunction (clos_sym (closed_red1 Σ Γ)) (compare_term le Σ.1 (global_ext_constraints Σ))).

  Definition conv1 : relation term := genconv1 false.
  Definition cumul1 : relation term := genconv1 true.

  Lemma conv0_conv1 M N :
    conv0  M N <~> conv1 M N.
  Proof.
    split; intro H.
    - induction H.
      + constructor. now destruct r; [left; left|right].
      + reflexivity.
      + now apply clos_rt_trans_Symmetric.
      + etransitivity; eassumption.
    - induction H.
      + destruct r as [[]|].
        * now constructor; left.
        * now symmetry; constructor; left.
        * now constructor; right.
      + reflexivity.
      + etransitivity; eassumption.
  Defined.

End ConvCumulDefs.
