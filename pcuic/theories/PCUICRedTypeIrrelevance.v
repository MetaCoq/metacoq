From Coq Require Import ssreflect. 
From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICLiftSubst 
  PCUICReduction PCUICContextRelation PCUICContextReduction.

From Coq Require Import CRelationClasses.

(** Types and names of variables are irrelevant during reduction. 
    More precisely, we only need to preserve bodies of let declarations
    in contexts for reductions to be preserved.
*)

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Lemma All2_fold_nth_ass {P n Γ Γ' d} :
  All2_fold P Γ Γ' -> nth_error Γ n = Some d ->
  assumption_context Γ ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          All2_fold P Γs Γs' *
          (d.(decl_body) = None) *
          P Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel. intro ass. 
    simpl. eexists; intuition eauto.
    now depelim ass.
  - intros ass. depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    now depelim ass.
    cbn -[skipn] in *.
    eexists; intuition eauto.
Qed.

(** Types of variables and names are irrelevant during reduction:
  Only bodies of let-bindings should be preserved to get the same reductions.
*)

Section ContextChangeTypesReduction.

  Context {cf : checker_flags}.
  Context (Σ : global_env).

Definition pres_let_bodies (c : context_decl) (c' : context_decl) : Type :=
  match c.(decl_body) with 
  | None => unit
  | Some b => decl_body c' = Some b
  end.

Global Instance pres_let_bodies_refl : Reflexive pres_let_bodies.
Proof. intros [? [|]]; constructor; reflexivity. Qed.

(* Global Instance pres_let_bodies_sym : Symmetric pres_let_bodies.
Proof.
  intros x y rel.
  depelim rel; constructor; now symmetry.
Qed. *)

Global Instance pres_let_bodies_trans : Transitive pres_let_bodies.
Proof.
  intros x y z; unfold pres_let_bodies.
  now destruct decl_body => // ->.
Qed.

(* Global Instance pres_let_bodies_equiv : Equivalence pres_let_bodies.
Proof. constructor; typeclasses eauto. Qed. *)

Lemma OnOne2All_All3 {A B} (P Q : A -> B -> B -> Type) l l' l'' :
  OnOne2All P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  All3 Q l l' l''.
Proof.
  intros H ? ?. induction H; constructor; auto.
  induction tl in bs, e |- *; destruct bs; simpl in e; try constructor; auto; try congruence.
Qed.

Lemma context_pres_let_bodiess_red1 Γ Γ' s t :
  All2_fold (fun _ _ => pres_let_bodies) Γ Γ' -> red1 Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros HT X0. induction X0 using red1_ind_all in Γ', HT |- *; eauto.
  all:pcuic.
  - econstructor. econstructor.
    move: H; case: nth_error_spec => [x hnth hi|hi] /= // [=] hbod.
    eapply All2_fold_nth in HT as [d' [hnth' [_ pres]]]; eauto.
    rewrite /pres_let_bodies hbod in pres.
    now rewrite hnth' /= pres.
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
  - eapply PCUICReduction.red_case_pcontext.
    eapply OnOne2_local_env_impl; tea.
    intros Δ x y.
    eapply on_one_decl_impl; intros Γ'' t t' IH; simpl.
    eapply IH. eapply All2_fold_app; auto.
    eapply All2_fold_refl.
    intros; reflexivity.
  - eapply PCUICReduction.red_case_p; eauto. eapply IHX0.
    eapply All2_fold_app; eauto.
    now eapply All2_fold_refl.
  - eapply PCUICReduction.red_case_c; eauto.
  - eapply PCUICReduction.red_case_brs; eauto.
    eapply OnOne2_All2; eauto. simpl.
    * unfold on_Trel; intros br br'. intuition eauto.
      + eapply b0. eapply All2_fold_app; auto.
        now apply All2_fold_refl.
      + rewrite b. reflexivity.
      + rewrite b0; reflexivity.
      + eapply red_one_decl_red_ctx_rel.
        eapply OnOne2_local_env_impl; tea.
        intros Δ x y.
        eapply on_one_decl_impl; intros Γ'' t t' IH; simpl.
        eapply IH. eapply All2_fold_app; auto.
        eapply All2_fold_refl.
        intros; reflexivity.
    * intros br; unfold on_Trel. split; auto.
      reflexivity.
  - eapply PCUICReduction.red_proj_c. eauto.
  - eapply PCUICReduction.red_app; eauto.
  - eapply PCUICReduction.red_app; eauto.
  - eapply PCUICReduction.red_prod; eauto.
  - eapply PCUICReduction.red_prod; eauto. eapply IHX0. eauto. eauto.
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

Lemma context_pres_let_bodiess_red Γ Γ' s t :
  All2_fold (fun _ _ => pres_let_bodies) Γ Γ' -> red Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros. induction X0 using red_rect'; eauto.
  etransitivity. eapply IHX0.
  eapply context_pres_let_bodiess_red1; eauto.
Qed.
End ContextChangeTypesReduction.

Lemma fix_context_pres_let_bodiess Γ mfix mfix' :
  #|mfix| = #|mfix'| ->
  All2_fold (fun _ _ => pres_let_bodies) (Γ,,, fix_context mfix) (Γ,,, fix_context mfix').
Proof.
  intros len.
  apply All2_fold_app.
  - now rewrite !fix_context_length.
  - apply All2_fold_refl.
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
      apply All2_fold_app.
      * now rewrite !List.rev_length !mapi_rec_length.
      * constructor; [constructor|].
        constructor.
      * apply IHmfix; lia.
Qed.
