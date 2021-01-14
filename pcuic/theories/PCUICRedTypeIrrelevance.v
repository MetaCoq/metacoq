From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICLiftSubst 
  PCUICReduction PCUICContextRelation.

From Coq Require Import CRelationClasses.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Lemma context_relation_nth {P n Γ Γ' d} :
context_relation P Γ Γ' -> nth_error Γ n = Some d ->
{ d' & ((nth_error Γ' n = Some d') *
        let Γs := skipn (S n) Γ in
        let Γs' := skipn (S n) Γ' in
        context_relation P Γs Γs' *
        P Γs Γs' d d')%type }.
Proof.
induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
- depelim Hrel.
  simpl. eexists; intuition eauto.
  eexists; intuition eauto.
- depelim Hrel.
  destruct (IHn _ _ _ Hrel H).
  cbn -[skipn] in *.
  eexists; intuition eauto.
  destruct (IHn _ _ _ Hrel H).
  eexists; intuition eauto.
Qed.

Lemma context_relation_nth_ass {P n Γ Γ' d} :
context_relation P Γ Γ' -> nth_error Γ n = Some d ->
assumption_context Γ ->
{ d' & ((nth_error Γ' n = Some d') *
        let Γs := skipn (S n) Γ in
        let Γs' := skipn (S n) Γ' in
        context_relation P Γs Γs' *
        (d.(decl_body) = None) *
        P Γs Γs' d d')%type }.
Proof.
induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
- depelim Hrel. intro ass. 
  simpl. eexists; intuition eauto.
  eexists; intuition eauto.
  depelim H.
- intros ass. depelim Hrel.
  destruct (IHn _ _ _ Hrel H).
  now depelim ass.
  cbn -[skipn] in *.
  eexists; intuition eauto.
  destruct (IHn _ _ _ Hrel H).
  now depelim ass.
  eexists; intuition eauto.
Qed.

Lemma context_relation_nth_r {P n Γ Γ' d'} :
context_relation P Γ Γ' -> nth_error Γ' n = Some d' ->
{ d & ((nth_error Γ n = Some d) *
        let Γs := skipn (S n) Γ in
        let Γs' := skipn (S n) Γ' in
        context_relation P Γs Γs' *
        P Γs Γs' d d')%type }.
Proof.
induction n in Γ, Γ', d' |- *; destruct Γ'; intros Hrel H; noconf H.
- depelim Hrel.
  simpl. eexists; intuition eauto.
  eexists; intuition eauto.
- depelim Hrel.
  destruct (IHn _ _ _ Hrel H).
  cbn -[skipn] in *.
  eexists; intuition eauto.
  destruct (IHn _ _ _ Hrel H).
  eexists; intuition eauto.
Qed.

(** Types of variables are irrelevant during reduction *)

Section ContextChangeTypesReduction.
Context {cf : checker_flags}.
Context (Σ : global_env).

Inductive change_decl_type : context_decl -> context_decl -> Type :=
| change_vass_type : forall (na na' : aname) (T T' : term),
    change_decl_type (vass na T) (vass na' T')
| change_vdef_type : forall (na na' : aname) (b T T'  : term),
    change_decl_type (vdef na b T) (vdef na' b T').

Derive Signature for change_decl_type.

Global Instance change_decl_type_refl : Reflexive change_decl_type.
Proof. intros [? [|]]; constructor; reflexivity. Qed.

Global Instance change_decl_type_sym : Symmetric change_decl_type.
Proof.
  intros x y rel.
  depelim rel; constructor; now symmetry.
Qed.

Global Instance change_decl_type_trans : Transitive change_decl_type.
Proof.
  intros x y z xy yz.
  depelim xy; depelim yz; constructor; now etransitivity.
Qed.

Global Instance change_decl_type_equiv : Equivalence change_decl_type.
Proof. constructor; typeclasses eauto. Qed.

Lemma OnOne2All_All3 {A B} (P Q : A -> B -> B -> Type) l l' l'' :
  OnOne2All P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  All3 Q l l' l''.
Proof.
  intros H ? ?. induction H; constructor; auto.
  induction tl in bs, e |- *; destruct bs; simpl in e; try constructor; auto; try congruence.
Qed.

Lemma context_change_decl_types_red1 Γ Γ' s t :
  context_relation (fun _ _ => change_decl_type) Γ Γ' -> red1 Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros HT X0. induction X0 using red1_ind_all in Γ', HT |- *; eauto.
  all:pcuic.
  - econstructor. econstructor.
    rewrite <- H.
    induction HT in i |- *; destruct i; eauto.
    now inv p.
  - eapply PCUICReduction.red_abs. eapply IHX0; eauto.  eauto.
  - eapply PCUICReduction.red_abs. eauto. eapply IHX0. eauto.
    eauto. econstructor. eauto. econstructor.
  -
    eapply PCUICReduction.red_letin. eapply IHX0; eauto.
    all:eauto.
  -
    eapply PCUICReduction.red_letin; eauto.
  -
    eapply PCUICReduction.red_letin; eauto. eapply IHX0; eauto.
    econstructor. eauto. econstructor.
    
  - eapply PCUICReduction.red_case_pars; eauto.
    simpl. eapply OnOne2_All2; eauto. simpl. intuition auto.
  - eapply PCUICReduction.red_case_p; eauto. eapply IHX0.
    eapply context_relation_app; eauto.
    now eapply context_relation_refl.
  - eapply PCUICReduction.red_case_c; eauto.
  - eapply PCUICReduction.red_case_brs; eauto.
    eapply OnOne2_All2; eauto. simpl.
    intros. intuition auto. eapply b0.
    eapply context_relation_app; auto.
    now apply context_relation_refl.
  -
    eapply PCUICReduction.red_proj_c. eauto.
  -
    eapply PCUICReduction.red_app; eauto.
  -     eapply PCUICReduction.red_app; eauto.
  -
    eapply PCUICReduction.red_prod; eauto.
  -
    eapply PCUICReduction.red_prod; eauto. eapply IHX0. eauto. eauto.
    econstructor.
    eauto. econstructor. 
  - eapply PCUICReduction.red_evar; eauto.
    induction X; eauto. econstructor. eapply p; eauto.
    induction tl; eauto.
  - eapply PCUICReduction.red_fix_one_ty.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
  - eapply PCUICReduction.red_fix_one_body.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
    eapply ih ; auto.
    clear - HT.
    induction (fix_context mfix0) as [| [na [b|] ty] Δ ihΔ].
    + auto.
    + simpl. constructor ; eauto.
      constructor. 
    + simpl. constructor ; eauto.
      constructor. 
  - eapply PCUICReduction.red_cofix_one_ty.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
  - eapply PCUICReduction.red_cofix_one_body.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
    eapply ih ; auto.
    clear - HT.
    induction (fix_context mfix0) as [| [na [b|] ty] Δ ihΔ].
    + auto.
    + simpl. constructor ; eauto.
      constructor. 
    + simpl. constructor ; eauto.
      constructor. 
Qed.

Lemma context_change_decl_types_red Γ Γ' s t :
  context_relation (fun _ _ => change_decl_type) Γ Γ' -> red Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros. induction X0 using red_rect'; eauto.
  etransitivity. eapply IHX0.
  eapply context_change_decl_types_red1; eauto.
Qed.
End ContextChangeTypesReduction.

Lemma fix_context_change_decl_types Γ mfix mfix' :
  #|mfix| = #|mfix'| ->
  context_relation (fun _ _ => change_decl_type) (Γ,,, fix_context mfix) (Γ,,, fix_context mfix').
Proof.
  intros len.
  apply context_relation_app.
  - now rewrite !fix_context_length.
  - apply context_relation_refl.
    intros.
    destruct x.
    destruct decl_body; constructor;
    reflexivity.
  - unfold fix_context, mapi.
    generalize 0 at 2 4.
    induction mfix in mfix', len |- *; intros n.
    + destruct mfix'; [|cbn in *; discriminate len].
      constructor.
    + destruct mfix'; cbn in *; [discriminate len|].
      apply context_relation_app.
      * now rewrite !List.rev_length, !mapi_rec_length.
      * constructor; [constructor|].
        constructor.
      * apply IHmfix; lia.
Qed.
