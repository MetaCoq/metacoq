From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICSigmaCalculus PCUICRename PCUICOnFreeVars PCUICClosed.

From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping.

Require Import ssreflect ssrbool.
Require Import Coq.Program.Equality.

Lemma All_sigT {A B : Type} (P : A -> B -> Type) l :
  All (fun x => ∑ y, P x y) l ->
  ∑ l', All2 P l l'.
Proof.
  induction 1.
  1: eexists ; constructor.
  destruct p, IHX.
  eexists.
  by constructor ; eauto.
Qed.


Lemma strengthenP_unlift (p : nat -> bool) n k t : 
  on_free_vars (strengthenP k n p) t ->
  ∑ t', t = lift n k t' × on_free_vars p t'.
Proof.
  intros ofv.
  remember (strengthenP k n p) as q eqn:Heqq.
  assert (q =1 strengthenP k n p) by now subst.
  clear Heqq.
  revert n k p H.
  pattern q, t.
  revert ofv.
  eapply term_on_free_vars_ind.
  
  - intros.
    rewrite H0 /strengthenP in H.
    destruct (Nat.ltb_spec0 i k).
    1: exists (tRel i) ; split ; cbn ; [destruct (Nat.leb_spec0 k i) ; [lia|auto]|auto].
    destruct (Nat.ltb_spec0 i (k + n)).
    1: congruence.
    exists (tRel (i - n)) ; split ; cbn.
    2: auto.
    destruct (Nat.leb_spec0 k (i - n)).
    2: lia.
    f_equal.
    lia.
  
  - intros. exists (tVar i) ; auto.
  
  - intros.
    eapply All_impl in X0.
    2: intros ? H1 ; apply H1 ; tea.
    apply All_sigT in X0 as [l' a].
    apply All2_prod_inv in a as [a a'].
    apply All2_right in a'.
    eexists (tEvar _ _) ; split.
    + cbn ; f_equal.
      eapply All2_eq, All2_map_right ; eauto.
    + by apply All_forallb.

  - intros ; eexists (tSort _) ; split ; eauto ; reflexivity.
  
  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H1 ; reflexivity.
    }
    subst.
    eexists (tProd _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.

  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H1 ; reflexivity.
    }
    subst.
    eexists (tLambda _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.
    
  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    edestruct X1 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H2 ; reflexivity.
    }
    subst.
    eexists (tLetIn _ _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by repeat (apply andb_true_iff ; split).

  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    subst.
    eexists (tApp _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.

  - intros.
    eexists (tConst _ _) ; split ; eauto.
    reflexivity.

  - intros.
    eexists (tInd _ _) ; split ; eauto.
    reflexivity.

  - intros.
    eexists (tConstruct _ _ _) ; split ; eauto.
    reflexivity.

  - intros.
    admit.
    
  - intros.
    edestruct X as [? []] ; eauto.
    subst.
    eexists (tProj _ _) ; split.
    1: reflexivity.
    auto.

  - intros.
    admit.
    
  - intros.
    admit.
    
Admitted.

Lemma strengthening_leq_term `{cf : checker_flags} (Σ : global_env_ext) (Γ' Γ'' : context) t u :
  leq_term Σ Σ (lift #|Γ''| #|Γ'| t) (lift #|Γ''| #|Γ'| u) ->
  leq_term Σ Σ t u.
Proof.
Admitted.

Lemma strengthening_red `{cf : checker_flags} Σ (wfΣ : wf Σ) Γ Γ' Γ'' t u :
  red Σ (Γ ,,, Γ'' ,,, (lift_context #|Γ''| 0 Γ')) (lift #|Γ''| #|Γ'| t) u ->
  ∑ u', u = lift #|Γ''| #|Γ'| u' × red Σ (Γ ,,, Γ') t u'.
Proof.
Admitted.

Lemma rename_context_lift_context n k Γ :
  rename_context (lift_renaming n k) Γ = lift_context n k Γ.
Proof.
  rewrite /rename_context /lift_context.
  apply fold_context_k_ext.
  intros i.
  rewrite shiftn_lift_renaming.
  symmetry.
  intro.
  by apply lift_rename.
Qed.

Lemma unlift_mkApps t args n k u:
  mkApps t args = lift n k u ->
  ∑ t' args', t = lift n k t' × args = map (lift n k) args' × u = mkApps t' args'.
Proof.
  intros.
  induction args in t, u, H |- *.
  - cbn in *.
    eexists ; exists [] ; by repeat split.
  - cbn in *.
    edestruct IHargs as (t'&?&e&?&?) ; tea.
    destruct t' ; inversion e ; subst ; clear e. 
    subst.
    eexists ; eexists (_ :: _) ; repeat split.
Qed.


Section BDStrengthening.

  (** We work in a fixed, well-formed global environment*)

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Let Pinfer Γ t T :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ T',
    T = lift #|Δ''| #|Δ'| T' × Σ ;;; Δ ,,, Δ' |- t' ▹ T'.

  Let Psort Γ t u :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    Σ ;;; Δ ,,, Δ' |- t' ▹□ u.

  Let Pprod Γ t na A B :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ A' B',
    A = lift #|Δ''| #|Δ'| A' × B = lift #|Δ''| (S #|Δ'|) B' × Σ ;;; Δ ,,, Δ' |- t' ▹Π (na,A',B').

  Let Pind Γ ind t u args :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ args',
    args = map (lift #|Δ''| #|Δ'|) args' × Σ ;;; Δ ,,, Δ' |- t' ▹{ind} (u,args').

  Let Pcheck Γ t T :=
    forall Δ Δ' Δ'' t' T',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    T = lift #|Δ''| #|Δ'| T' ->
    Σ ;;; Δ ,,, Δ' |- t' ◃ T'.
  
  Let PΓ (Γ : context) :=
    forall Δ Δ' Δ'',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    wf_local_bd Σ (Δ ,,, Δ').

  Theorem bidirectional_strengthening : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ.
  Proof.
    apply bidir_ind_env.

    - intros. red. intros.
      subst.
      apply All_local_env_app ; split.
      1: by clear X ; repeat apply All_local_env_app_inv in wfΓ as [wfΓ _].
      induction Δ' as [|[? [] ?] ].
      + constructor.
      + rewrite -/(snoc Δ' _) lift_context_snoc Nat.add_0_r !app_context_cons in wfΓ, X.
        inversion X ; subst.
        constructor.
        * eauto.
        * eexists.
          eauto.
        * eapply X1 ; eauto.
      + rewrite -/(snoc Δ' _) lift_context_snoc Nat.add_0_r !app_context_cons in wfΓ, X.
        inversion X ; subst.
        constructor ; eauto.
        eexists ; eauto. 
    
    - intros. red. intros.
      subst.
      destruct t' ; cbn in H1 ; inversion H1 ; subst ; clear H1.
      destruct (Nat.leb_spec0 #|Δ'| n0).
      + rewrite /app_context /lift_context -nth_error_ge // in H.
        eexists ; split.
        2: constructor ; tea.
        rewrite simpl_lift.
        3: f_equal.
        all: lia.
      + rewrite /app_context /lift_context nth_error_app_context_lt in H.
        1: by rewrite fold_context_k_length ; lia.
        fold (lift_context #|Δ''| 0 Δ') in H.
        rewrite -rename_context_lift_context in H.
        rewrite nth_error_rename_context in H.
        remember (nth_error Δ' n0) as decl'.
        destruct decl' ; cbn in * ; inversion H ; subst ; clear H.
        eexists ; split.
        2:{
          constructor.
          rewrite nth_error_app_context_lt ; eauto.
          lia.
        }
        cbn.
        rewrite shiftn_lift_renaming Nat.add_0_r -lift_rename permute_lift.
        2: f_equal.
        all: lia.


    - intros. red. intros. subst.
      destruct t' ; cbn in H1 ; inversion H1 ; subst ; clear H1.
      eexists ; split.
      2: by constructor.
      reflexivity.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      eexists ; split.
      2:{ constructor ; eauto.
        rewrite -app_context_cons.
        eapply X2 ; eauto.
        by rewrite -app_context_cons lift_context_snoc Nat.add_0_r.
      }
      by reflexivity.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X2 as (?&?&?).
      2: change (S #|Δ'|) with (#|Δ' ,, vass na t'1|) ; reflexivity.
      1: rewrite -app_context_cons lift_context_snoc Nat.add_0_r ; reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      cbn.
      by f_equal.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X4 as (?&?&?).
      2: change (S #|Δ'|) with (#|Δ' ,, vdef na t'1 t'2|) ; reflexivity.
      1: rewrite -app_context_cons lift_context_snoc Nat.add_0_r ; reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      cbn.
      by f_equal.
    
    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X0 as (?&?&?&?&?).
      1-2: reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      subst.
      by rewrite distr_lift_subst10.
      
    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: constructor ; tea.
      erewrite <- (lift_closed _ _ (cst_type _)) at 1.
      1: by eapply subst_instance_lift.
      eapply closed_upwards.
      1: eapply declared_constant_closed_type ; tea.
      lia.
    
    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: econstructor ; tea.
      erewrite <- (lift_closed _ _ (ind_type _)) at 1.
      1: by eapply subst_instance_lift.
      eapply closed_upwards.
      1: eapply declared_inductive_closed_type ; tea.
      lia.

    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: econstructor ; tea.
      erewrite <- (lift_closed _ _ (type_of_constructor _ _ _ _)) at 1.
      1: reflexivity.
      eapply closed_upwards.
      1: eapply declared_constructor_closed_type ; tea.
      lia.
    
    - admit.
    
    - admit.
    
    - admit.
    
    - admit.
    
    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      destruct u' ; inversion e ; subst.
      econstructor ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      destruct u' ; inversion e ; subst.
      repeat eexists ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      apply unlift_mkApps in e as (?&?&?&?&?).
      destruct x0 ; inversion e.
      subst.
      repeat eexists ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      econstructor ; tea.
      apply cumul_alt.
      apply cumul_alt in X1 as (?&?&(r&r')&?).
      apply strengthening_red in r as (?&?&?).
      apply strengthening_red in r' as (?&?&?).
      all: tea.
      subst.
      do 2 eexists ; split.
      1: split ; tea.
      eapply strengthening_leq_term ; tea.

  Admitted.
