From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICClosed PCUICEquality PCUICWeakeningEnv.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

(** * Theory of σ-calculus operations *)

Open Scope sigma_scope.

Hint Rewrite @lift_rename Nat.add_0_r : sigma.
Hint Rewrite @subst_consn_nil @subst_consn_tip : sigma.
Hint Rewrite idsn_length : len.

Instance ren_ext : Morphisms.Proper (`=1` ==> `=1`)%signature ren.
Proof.
  reduce_goal. unfold ren. now rewrite H.
Qed.

Lemma shiftn0 r : shiftn 0 r =1 r.
Proof.
  intros x.
  unfold shiftn. destruct (Nat.ltb_spec x 0); try lia.
  rewrite Nat.sub_0_r. lia.
Qed.

Lemma shiftnS n r : shiftn (S n) r =1 shiftn 1 (shiftn n r).
Proof.
  intros x. unfold shiftn.
  destruct x.
  - simpl. auto.
  - simpl. rewrite Nat.sub_0_r.
    destruct (Nat.ltb_spec x n);
    destruct (Nat.ltb_spec (S x) (S n)); auto; lia.
Qed.

Lemma subst_consn_shiftn n (l : list term) σ : #|l| = n -> ↑^n ∘s (l ⋅n σ) =1 σ.
Proof.
  induction n in l |- *; simpl; intros; autorewrite with sigma.
  - destruct l; try discriminate. simpl; autorewrite with sigma. reflexivity.
  - destruct l; try discriminate. simpl in *.
    rewrite subst_consn_subst_cons.
    simpl; autorewrite with sigma. apply IHn. lia.
Qed.

Lemma shiftn_consn_idsn n σ : ↑^n ∘s ⇑^n σ =1 σ ∘s ↑^n.
Proof.
  unfold Upn. rewrite subst_consn_shiftn; [reflexivity|].
  now rewrite idsn_length.
Qed.
Hint Rewrite shiftn_consn_idsn: sigma.

Lemma subst_consn_compose l σ' σ : l ⋅n σ' ∘s σ =1 (map (inst σ) l ⋅n (σ' ∘s σ)).
Proof.
  induction l; simpl.
  - now sigma.
  - rewrite subst_consn_subst_cons. sigma.
    rewrite IHl. now rewrite subst_consn_subst_cons.
Qed.

Lemma map_idsn_spec (f : term -> term) (n : nat) :
  map f (idsn n) = Nat.recursion [] (fun x l => l ++ [f (tRel x)]) n.
Proof.
  induction n; simpl.
  - reflexivity.
  - simpl. rewrite map_app. now rewrite -IHn.
Qed.

Lemma nat_recursion_ext {A} (x : A) f g n :
  (forall x l', x < n -> f x l' = g x l') ->
  Nat.recursion x f n = Nat.recursion x g n.
Proof.
  intros.
  generalize (le_refl n). 
  induction n at 1 3 4; simpl; auto. 
  intros. simpl. rewrite IHn0; try lia. now rewrite H.
Qed.

Lemma id_nth_spec {A} (l : list A) :
  l = Nat.recursion [] (fun x l' =>
                          match nth_error l x with
                          | Some a => l' ++ [a]
                          | None => l'
                          end) #|l|.
Proof.
  induction l using rev_ind; simpl; try reflexivity.
  rewrite app_length. simpl. rewrite Nat.add_1_r. simpl.
  rewrite nth_error_app_ge; try lia. rewrite Nat.sub_diag. simpl.
  f_equal. rewrite {1}IHl. eapply nat_recursion_ext. intros.
  now rewrite nth_error_app_lt.
Qed.

Lemma Upn_comp n l σ : n = #|l| -> ⇑^n σ ∘s (l ⋅n ids) =1 l ⋅n σ.
Proof.
  intros ->. rewrite Upn_eq; simpl.
  rewrite !subst_consn_compose. sigma.
  rewrite subst_consn_shiftn ?map_length //. sigma.
  eapply subst_consn_proper; try reflexivity.
  rewrite map_idsn_spec.
  rewrite {3}(id_nth_spec l).
  eapply nat_recursion_ext. intros.
  simpl. destruct (nth_error_spec l x).
  - unfold subst_consn. rewrite e. reflexivity.
  - lia.
Qed.

Lemma shift_Up_comm σ : ↑ ∘s ⇑ σ =1 σ ∘s ↑.
Proof. reflexivity. Qed.

Lemma shiftk_compose n m : ↑^n ∘s ↑^m =1 ↑^(n + m).
Proof.
  induction n; simpl; sigma; auto.
  - reflexivity.
  - rewrite -subst_compose_assoc.
    rewrite -shiftk_shift shiftk_shift_l.
    now rewrite subst_compose_assoc IHn -shiftk_shift shiftk_shift_l.
Qed.

Lemma Upn_compose n σ σ' : ⇑^n σ ∘s ⇑^n σ' =1 ⇑^n (σ ∘s σ').
Proof.
  induction n.
  - unfold Upn. simpl.
    now rewrite !subst_consn_nil !shiftk_0 !compose_ids_r.
  - rewrite !Upn_S. autorewrite with sigma. now rewrite IHn.
Qed.

Lemma up_ext_closed k' k s s' :
  (forall i, i < k' -> s i = s' i) -> 
  forall i, i < k + k' ->
  up k s i = up k s' i.
Proof.
  unfold up. intros Hs t. elim (Nat.leb_spec k t) => H; auto.
  intros. f_equal. apply Hs. lia.
Qed.

Lemma subst_consn_eq s0 s1 s2 s3 x : 
  x < #|s0| -> #|s0| = #|s2| ->
  subst_fn s0 x = subst_fn s2 x ->
  (s0 ⋅n s1) x = (s2 ⋅n s3) x.
Proof.
  unfold subst_fn; intros Hx Heq Heqx.
  unfold subst_consn. 
  destruct (nth_error s0 x) eqn:Heq';
  destruct (nth_error s2 x) eqn:Heq''; auto;
  (apply nth_error_None in Heq''|| apply nth_error_None in Heq'); lia.
Qed.

Lemma shift_subst_instance_constr :
  forall u t k,
    (subst_instance_constr u t).[⇑^k ↑] = subst_instance_constr u t.[⇑^k ↑].
Proof.
  intros u t k.
  induction t in k |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: autorewrite with sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_length 
    ?map_predicate_map_predicate ?map_branch_map_branch; unfold map_branch.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - unfold Upn, shift, subst_compose, subst_consn.
    destruct (Nat.ltb_spec0 n k).
    + rewrite nth_error_idsn_Some. 1: assumption.
      reflexivity.
    + rewrite nth_error_idsn_None. 1: lia.
      reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1 IHt2. specialize (IHt3 (S k)). autorewrite with sigma in IHt3.
    rewrite IHt3. reflexivity.
  - f_equal.
    * destruct X. solve_all.
      now rewrite -Upn_Upn e.
    * apply IHt.
    * solve_all. f_equal.
      now rewrite up_Upn -Upn_Upn H.
  - f_equal.
    red in X.
    eapply All_map_eq. eapply (All_impl X).
    intros x [IH IH'].
    apply map_def_eq_spec. 
    * apply IH.
    * specialize (IH' (#|m| + k)).
      autorewrite with sigma.
      now rewrite - !up_Upn up_up !up_Upn.
  - f_equal.
    autorewrite with len.
    red in X.
    eapply All_map_eq. eapply (All_impl X).
    intros x [IH IH'].
    apply map_def_eq_spec. 
    * apply IH.
    * specialize (IH' (#|m| + k)). sigma.
      now rewrite - !up_Upn up_up !up_Upn.
Qed.

Lemma shiftn_add n m f : shiftn n (shiftn m f) =1 shiftn (n + m) f.
Proof.
  intros i.
  unfold shiftn.
  destruct (Nat.ltb_spec i n).
  - destruct (Nat.ltb_spec i (n + m)); try lia.
  - destruct (Nat.ltb_spec i (n + m)); try lia;
    destruct (Nat.ltb_spec (i - n) m); try lia.
    rewrite Nat.add_assoc. f_equal. f_equal. lia.  
Qed.

Ltac nat_compare_specs :=
  match goal with
  | |- context [?x <=? ?y] =>
    destruct (Nat.leb_spec x y); try lia
  | |- context [?x <? ?y] =>
    destruct (Nat.ltb_spec x y); try lia
  end.

Instance shiftn_proper : Proper (Logic.eq ==> `=1` ==> `=1`) shiftn.
Proof.
  intros x y -> f g Hfg.
  unfold shiftn; intros i.
  nat_compare_specs. now rewrite Hfg.
Qed.

Instance map_decl_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) map_decl.
Proof.
  intros f g Hfg x y ->. now apply map_decl_ext.
Qed.

Lemma nth_error_idsn_eq_Some n k i : nth_error (idsn n) k = Some i -> i = tRel k.
Proof.
  intros hnth.
  move: (nth_error_Some_length hnth).
  len. move/nth_error_idsn_Some.
  now rewrite hnth => [= ->].
Qed.