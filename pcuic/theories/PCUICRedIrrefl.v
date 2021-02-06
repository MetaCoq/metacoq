
(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSigmaCalculus (* for smash_context lemmas, to move *)
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence
     PCUICContextConversion PCUICContextSubst PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives PCUICValidity.

From Equations Require Import Equations.
Derive Subterm for term.

Require Import ssreflect.

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Hint Rewrite reln_length : len.

Ltac substu := autorewrite with substu => /=.

Tactic Notation "substu" "in" hyp(id) :=
  autorewrite with substu in id; simpl in id.

  From MetaCoq.PCUIC Require Import PCUICContextRelation.
Proposition leq_term_equiv `{checker_flags} Σ t t' :
  leq_term Σ.1 Σ t t' -> leq_term Σ.1 Σ t' t -> eq_term Σ.1 Σ t t'.
  Admitted.

Lemma cum_cum_trans {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T U V} : 
  Σ ;;; Γ |- T <= U ->
  Σ ;;; Γ |- U <= V ->
  ∑ T' U' V', 
    red Σ Γ T T' ×
    red Σ Γ U U' ×
    red Σ Γ V V' ×
    leq_term Σ Σ T' U' ×
    leq_term Σ Σ U' V'.
Proof.
  move/cumul_alt; intros (T' & U' & (redTT' & redUU') & leqT'U').
  move/cumul_alt; intros (U'' & V' & (redUU'' & redVV') & leqU''V').
  destruct (red_confluence wfΣ redUU' redUU'') as [Unf [redU'nf redU''nf]].
  destruct (red_eq_term_upto_univ_l Σ _ leqU''V' redU''nf) as [v'nf [redV'nf lequnf]].
  destruct (red_eq_term_upto_univ_r Σ _ leqT'U' redU'nf) as [T'nf [redT'nf leqTnf]].
  exists T'nf, Unf, v'nf.
  intuition auto.
  - now transitivity T'.
  - now transitivity U'.
  - now transitivity V'.
Qed.

Hint Constructors term_direct_subterm : term.

Lemma leq_term_size {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} T T' :
  leq_term Σ Σ T T' ->
  PCUICSize.size T = PCUICSize.size T'.
Proof.
  induction 1; simpl; auto; try lia.
  f_equal. admit.
  f_equal. rewrite IHX. admit.
Admitted.
  
Lemma lift_irrefl_direct n k t x :
   term_direct_subterm t x ->
   lift n k t <> x.
Proof.
  intros ts H. subst x.
  revert ts.
  induction t using term_forall_list_ind in n, k |- *; simpl; 
    try solve [intros H; depelim H].
  * intros H. depelim H.
    eapply IHt2; rewrite -> H. constructor.
    eapply IHt1; rewrite -> H. constructor.
  * intros H. depelim H.
    eapply IHt2; rewrite -> H. constructor.
    eapply IHt1; rewrite -> H. constructor.
  * intros H; depelim H.
    eapply IHt3; rewrite -> H; eauto with term.
    eapply IHt2; rewrite -> H; eauto with term.
    eapply IHt1; rewrite -> H; eauto with term.
  * intros H; depelim H.
    eapply IHt2; rewrite -> H; eauto with terms.
    constructor.
    eapply IHt1; rewrite -> H; constructor.
  * intros H; depelim H.
    eapply IHt. rewrite -> H. constructor.
  * intros H; depelim H.
    eapply IHt; rewrite -> H. constructor.
Qed.

Lemma lift_irrefl n k t :
   term_subterm t (lift n k t) -> False.
Proof.
  intros H; depind H.
  now eapply lift_irrefl_direct.
  eapply IHclos_trans2.
Admitted.


Lemma nocycle {A} {R} {wfR : Equations.Prop.Classes.WellFounded R} :
  forall x : A, R x x -> False.
Proof.
  intros x Ryy. red in wfR.
  induction (wfR x) as [y accy IHy].
  apply (IHy _ Ryy Ryy).
Qed.

Instance term_direct_subterm_wf : WellFounded term_direct_subterm.
Proof.
  intros x. induction x;
  constructor; intros y H; depelim H; auto.
Qed.

Lemma term_direct_subterm_irrefl x : term_direct_subterm x x -> False.
Proof.
  intros H.
  now apply nocycle in H.
Qed.


Lemma term_subterm_irrefl x : term_subterm x x -> False.
Proof.
  intros H.
  now apply nocycle in H.
Qed.
(*
Lemma subst_irrefl s k b x :
  term_subterm b x -> All (fun a => term_subterm a x) s ->
  subst s k b <> x.
Proof.
  intros ts hs H; subst x.
  revert ts.
  induction b using term_forall_list_ind in k, s, hs |- *; simpl; try (split; congruence).
  all:try apply term_subterm_irrefl.
  * destruct (leb_spec_Set k n).
    case: nth_error_spec => /= // [t hnth hn|hn].
    eapply nth_error_all in hs; tea => /=. simpl in hs.
    destruct (leb_spec_Set k n);try lia.
    rewrite hnth in hs.
    now eapply lift_irrefl in hs.
    intros. admit.
     (* depelim ts. *)
    apply term_subterm_irrefl.
  * intros. admit.
  * intros ts.
    depelim ts. simpl in hs.
    depelim H.
    eapply IHb2.
    2:{ rewrite -> H. constructor. constructor. }
    eapply (All_impl hs).
    intros. depelim H0.
    rewrite H.
  

Admitted.
    
Lemma beta_irrefl b a na ty :
  b {0 := a} <> tApp (tLambda na ty b) a.
Proof.
  intros H.
  forward (subst_irrefl [a] 0 b (tApp (tLambda na ty b) a)).
  eapply Relation_Operators.t_trans with (tLambda na ty b).
  repeat constructor.
  repeat constructor.
  intros. forward H0.
  constructor. 2:constructor.
  constructor. constructor.
  rewrite /subst1 in H. congruence.
Qed.

Lemma red_leq_sym {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T T' T''} : 
  red1 Σ Γ T T' ->
  red1 Σ Γ T T'' ->
  (T' = T'') + (leq_term Σ Σ T' T'' -> False).
  (* leq_term Σ Σ T'' T'. *)
Proof.
  intros red red'.
  (* eapply (eq_term_upto_univ_napp_flip _ _ (fun x y => leq_universe Σ y x)); eauto. all:tc.
  - intros x. reflexivity.
  - intros x y z ? ?. etransitivity; tea.
  - intros x y e. apply eq_universe_leq_universe. now symmetry.
  - *) 
  
  induction red using red1_ind_all in T'', red' |- *; try depelim red'.
  all:try solve_discr.
  all:try (left; reflexivity).
  * depelim red'; try solve_discr.
    right. intros leq. admit.
    right. intros leq.
Abort.*)
 
From MetaCoq.PCUIC Require Import PCUICParallelReduction PCUICParallelReductionConfluence PCUICEquality PCUICSubstitution.
(*
Lemma red_leq_sym {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} 
  {Γ Γ' Γ'' T T' T''} {Re Rle : Universe.t -> Universe.t -> Prop} {equ lequ napp} : 
  (forall u u' : Universe.t, reflectT (Re u u') (equ u u')) ->
  (forall u u' : Universe.t, reflectT (Rle u u') (lequ u u')) ->
  pred1 Σ Γ Γ' T T' ->
  pred1 Σ Γ Γ'' T T'' ->
  eq_term_upto_univ_napp Σ Re Rle napp T' T'' ->
  eq_term_upto_univ_napp Σ Re Re napp T' T''.
Proof.
  intros requ rlequ.
  intros red red'.
  pose proof (pred1_diamond wfΣ red red') as [].


  revert Γ Γ' T T' red napp lequ Rle rlequ Γ'' T'' red'.
  apply: pred1_ind_all_ctx.
  intros. exact X. intros.
  exact X3.
  all:intros.
  - depelim red'; try solve_discr.
    * specialize (X0 napp lequ Rle rlequ _ _ red'2).
      destruct (reflect_eq_term_upto_univ Σ equ lequ Re Rle 0 requ rlequ a1 a3).
      apply eq_term_upto_univ_substs; tc.
      apply X0. admit.
      constructor. 2:constructor.
      now apply (X4 0 lequ Rle rlequ _ _ red'3).
      admit.
      (* Implies a1, a3 not part of b1 {0 := a1} ... *)
    * specialize (X4 napp lequ Rle rlequ _ _ red'2).


  apply clos_refl_trans_out in red.
  apply clos_red_rel_out in red; eauto.
  apply clos_refl_trans_out in red'.
  apply clos_red_rel_out in 
*)
(*Lemma red_leq_sym {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T T' T''} : 
  red Σ Γ T T' ->
  red Σ Γ T T'' ->
  leq_term Σ Σ T' T'' ->
  leq_term Σ Σ T'' T'.
Proof.
  intros red red'.
  apply clos_refl_trans_out in red.
  apply clos_red_rel_out in red; eauto.
  apply clos_refl_trans_out in red'.
  apply clos_red_rel_out in red'; eauto.
  assert (eq_term Σ Σ T T) by reflexivity.
  intros leq. pose proof (fill_eq Σ X red red').
  pose proof (red_confluence wfΣ red red').*)

(* From MetaCoq.PCUIC Require Import PCUICEqualityDec. *)


Lemma cum_cum_conv {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T U } : 
  Σ ;;; Γ |- T <= U ->
  Σ ;;; Γ |- U <= T ->
  Σ ;;; Γ |- T = U.
Proof.
  intros cuml cumr.
  destruct (cum_cum_trans cuml cumr) as (T' & U' & T'' & redTT' & redUU' & redTT'' & leql & leqr).
  apply conv_alt_red.
  assert (eq_term Σ Σ T T) by reflexivity.
  pose proof (fill_eq Σ X redTT' redTT'') as (T'eq & T''eq & (redT'eq & redT''eq) & eqeqs).
  epose proof (red_eq_term_upto_univ_r Σ _ leqr redT''eq) as [U'eq [redU'eq eqU']].
  epose proof (red_eq_term_upto_univ_l Σ _ leql redT'eq) as [U'eq' [redU'eq' eqU'']].
  change (leq_term Σ Σ T'eq U'eq') in eqU''.
  change (leq_term Σ Σ U'eq T''eq) in eqU'.
  assert (leq_term Σ Σ U'eq T'eq).
  { transitivity T''eq => //. now apply eq_term_leq_term; symmetry. }
  assert ()


  exists T'eq, U'eq'.
  intuition auto.
  - transitivity T' => //.
  - transitivity U' => //.
  - 
    apply leq_term_equiv; auto.
    assert (leq_term Σ Σ U'eq U'eq').
    now transitivity T'eq.
    assert (leq_term Σ.1 Σ U'eq' T'eq -> False). admit.

    epose proof (reflect_eq_term_upto_univ Σ _ _ (eq_universe Σ) (leq_universe Σ) 0 _ _  U'eq T'eq).



    transitivity T''eq. now apply eq_term_leq_term.

      apply eqU''.
      now transitivity U'.
  assert (leq_term Σ Σ T' T''). by transitivity U'.
  clear leql leqr redUU' cuml cumr U U'.
  pose proof fill_eq.
  pose prood (red_eq_term_upto_univ_l Σ _ )
  
  admit.
  exists T', U'. intuition auto.
  apply leq_term_equiv; auto.
  transitivity T''. auto. symmetry in X.
  now apply eq_term_leq_term.
  
