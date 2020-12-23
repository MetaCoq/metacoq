From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

(** * Theory of σ-calculus operations *)

Declare Scope sigma_scope.
Delimit Scope sigma_scope with sigma.
Local Open Scope sigma_scope.
Ltac sigma := autorewrite with sigma.
Tactic Notation "sigma" "in" hyp(id) := autorewrite with sigma in id.

Definition substitution := nat -> term.
Bind Scope sigma_scope with substitution.

Hint Rewrite Nat.add_0_r : sigma.

Ltac nat_compare_specs :=
  match goal with
  | |- context [?x <=? ?y] =>
    destruct (Nat.leb_spec x y); try lia
  | |- context [?x <? ?y] =>
    destruct (Nat.ltb_spec x y); try lia
  end.

(* Sigma calculus*)

Lemma shiftn_ext n f f' : (forall i, f i = f' i) -> forall t, shiftn n f t = shiftn n f' t.
Proof.
  intros.
  unfold shiftn. destruct Nat.ltb; congruence.
Qed.

Instance shiftn_proper : Proper (Logic.eq ==> `=1` ==> `=1`) shiftn.
Proof.
  intros x y -> f g Hfg ?. now apply shiftn_ext.
Qed.

Lemma rename_ext f f' : (forall i, f i = f' i) -> (forall t, rename f t = rename f' t).
Proof.
  intros. revert f f' H.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all; eauto using shiftn_ext].
  - f_equal; solve_all.
    * now apply e, shiftn_ext.
    * apply map_branch_eq_spec; solve_all; eauto using shiftn_ext.
  - f_equal; auto. red in X. solve_all.
    eapply map_def_eq_spec; auto. now apply b, shiftn_ext.
  - f_equal; auto. red in X. solve_all.
    eapply map_def_eq_spec; auto. now apply b, shiftn_ext.
Qed.

Instance rename_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) rename.
Proof. intros f f' Hff' t t' ->. now apply rename_ext. Qed.

Instance rename_proper_pointwise : Proper (`=1` ==> pointwise_relation _ Logic.eq) rename.
Proof. intros f f' Hff' t. now apply rename_ext. Qed.


Definition lift_renaming n k :=
  fun i =>
    if Nat.leb k i then (* Lifted *) n + i
    else i.

Lemma shiftn_lift_renaming n m k :
  shiftn m (lift_renaming n k) =1 lift_renaming n (m + k).
Proof.
  unfold lift_renaming, shiftn. intros i.
  repeat (nat_compare_specs; try lia).
Qed.

Lemma lift_rename n k t : lift n k t = rename (lift_renaming n k) t.
Proof.
  revert n k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try reflexivity;
    try (rewrite ?H ?H0 ?H1; reflexivity);
    try solve [f_equal; solve_all].
  - f_equal; eauto.
    now rewrite H0 shiftn_lift_renaming.
  - f_equal; eauto.
    now rewrite H0 shiftn_lift_renaming.
  - f_equal; eauto.
    rewrite H1. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    * solve_all. now rewrite e shiftn_lift_renaming.
    * solve_all. apply map_branch_eq_spec. now rewrite H0 shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all. apply map_def_eq_spec; auto.
    rewrite b. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all. apply map_def_eq_spec; auto.
    rewrite b. now rewrite shiftn_lift_renaming.
Qed.
Hint Rewrite @lift_rename : sigma.

Definition up k (s : nat -> term) :=
  fun i =>
    if k <=? i then rename (Nat.add k) (s (i - k))
    else tRel i.

Lemma shiftn_compose n f f' : shiftn n f ∘ shiftn n f' =1 shiftn n (f ∘ f').
Proof.
  unfold shiftn. intros x.
  elim (Nat.ltb_spec x n) => H.
  - now rewrite (proj2 (Nat.ltb_lt x n)).
  - destruct (Nat.ltb_spec (n + f' (x - n)) n).
    * lia.
    * assert (n + f' (x - n) - n = f' (x - n)) as ->; lia.
Qed.

Lemma map_branches_shiftn (fn : (nat -> nat) -> term -> term) f f' l : 
  map_branches_shift fn f (map_branches_shift fn f' l) = 
  List.map (fun i => map_branch (fn (shiftn #|bcontext i| f) ∘ (fn (shiftn #|bcontext i| f'))) i) l.
Proof.
  rewrite map_map_compose. apply map_ext => i.
  rewrite map_branch_map_branch.
  simpl. now apply map_branch_eq_spec.
Qed.

Lemma rename_compose f f' : rename f ∘ rename f' =1 rename (f ∘ f').
Proof.
  intros x.
  induction x in f, f' |- * using term_forall_list_ind; simpl; 
    rewrite ?map_branch_map_branch ?map_predicate_map_predicate;
    f_equal;
    auto; solve_all.

  - rewrite map_map_compose. apply All_map_eq. solve_all.
  - rewrite IHx2. apply rename_ext, shiftn_compose.
  - rewrite IHx2. apply rename_ext, shiftn_compose.
  - rewrite IHx3. apply rename_ext, shiftn_compose.
  - rewrite /rename_predicate map_predicate_map_predicate.
    solve_all; len. rewrite e.
    apply rename_ext, shiftn_compose. 
  - rewrite map_branches_shiftn. solve_all. apply map_branch_eq_spec.
    rewrite H. apply rename_ext, shiftn_compose.
  - rewrite map_map_compose; apply All_map_eq. solve_all.
    rewrite map_def_map_def map_length.
    apply map_def_eq_spec; auto.
    rewrite b. apply rename_ext, shiftn_compose.
  - rewrite map_map_compose; apply All_map_eq. solve_all.
    rewrite map_def_map_def map_length.
    apply map_def_eq_spec; auto.
    rewrite b. apply rename_ext, shiftn_compose.
Qed.

Lemma up_up k k' s : up k (up k' s) =1 up (k + k') s.
Proof.
  red. intros x. unfold up.
  elim (Nat.leb_spec k x) => H.
  - elim (Nat.leb_spec (k + k') x) => H'.
    + elim (Nat.leb_spec k' (x - k)) => H''.
      ++ rewrite Nat.sub_add_distr.
         rewrite -> rename_compose. apply rename_ext. intros. lia.
      ++ simpl. lia.
    + edestruct (Nat.leb_spec k' (x - k)); simpl; lia_f_equal.
  - elim (Nat.leb_spec (k + k') x) => H'; lia_f_equal.
Qed.

Fixpoint inst s u :=
  match u with
  | tRel n => s n
  | tEvar ev args => tEvar ev (List.map (inst s) args)
  | tLambda na T M => tLambda na (inst s T) (inst (up 1 s) M)
  | tApp u v => tApp (inst s u) (inst s v)
  | tProd na A B => tProd na (inst s A) (inst (up 1 s) B)
  | tLetIn na b ty b' => tLetIn na (inst s b) (inst s ty) (inst (up 1 s) b')
  | tCase ind p c brs =>
    let p' := map_predicate id (inst s) (inst (up #|p.(pcontext)| s)) p in
    let brs' := map (fun br => map_branch (inst (up #|br.(bcontext)| s)) br) brs in
    tCase ind p' (inst s c) brs'
  | tProj p c => tProj p (inst s c)
  | tFix mfix idx =>
    let mfix' := map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Definition subst_fn (l : list term) :=
  fun i =>
    match List.nth_error l i with
    | None => tRel (i - List.length l)
    | Some t => t
    end.

Lemma up_ext k s s' : s =1 s' -> up k s =1 up k s'.
Proof.
  unfold up. intros Hs t. elim (Nat.leb_spec k t) => H; auto.
  f_equal. apply Hs.
Qed.

Lemma inst_ext s s' : s =1 s' -> inst s =1 inst s'.
Proof.
  intros Hs t. revert s s' Hs.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all; eauto using up_ext].
  - f_equal; solve_all.
    * now apply e, up_ext.
    * apply map_branch_eq_spec; solve_all; eauto using up_ext.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; auto. now apply b, up_ext.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; auto. now apply b, up_ext.
Qed.

Instance proper_inst : Proper (`=1` ==> Logic.eq ==> Logic.eq) inst.
Proof.
  intros f f' Hff' t t' ->. now apply inst_ext.
Qed.

Instance proper_inst' : Proper (`=1` ==> pointwise_relation _ Logic.eq) inst.
Proof.
  intros f f' Hff' t. now apply inst_ext.
Qed.

Instance up_proper k : Proper (`=1` ==> `=1`) (up k).
Proof. reduce_goal. now apply up_ext. Qed.

Definition ren (f : nat -> nat) : nat -> term :=
  fun i => tRel (f i).

Instance ren_ext : Morphisms.Proper (`=1` ==> `=1`)%signature ren.
Proof.
  reduce_goal. unfold ren. now rewrite H.
Qed.
  
Lemma ren_shiftn n f : up n (ren f) =1 ren (shiftn n f).
Proof.
  unfold ren, up, shiftn.
  intros i.
  elim (Nat.ltb_spec i n) => H; elim (Nat.leb_spec n i) => H'; try lia; trivial.
Qed.

Lemma rename_inst f : rename f =1 inst (ren f).
Proof.
  intros t. revert f.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; eauto. now rewrite H0 -ren_shiftn.
  - f_equal; eauto. now rewrite H0 -ren_shiftn.
  - f_equal; eauto. now rewrite H1 -ren_shiftn.
  - f_equal; eauto; solve_all.
    * now rewrite e -ren_shiftn.
    * apply map_branch_eq_spec. now rewrite H0 -ren_shiftn.
  - f_equal; eauto. solve_all. apply map_def_eq_spec; auto.
    now rewrite b ren_shiftn.
  - f_equal; eauto. solve_all. apply map_def_eq_spec; auto.
    now rewrite b ren_shiftn.
Qed.

Hint Rewrite @rename_inst : sigma.

(** Show the σ-calculus equations.

    Additional combinators: [idsn n] for n-identity, [consn] for consing a parallel substitution.
 *)

Notation "t '.[' σ ]" := (inst σ t) (at level 6, format "t .[ σ ]") : sigma_scope.

Definition subst_cons (t : term) (f : nat -> term) :=
  fun i =>
    match i with
    | 0 => t
    | S n => f n
    end.

Notation " t ⋅ s " := (subst_cons t s) (at level 70) : sigma_scope.

Instance subst_cons_proper : Proper (Logic.eq ==> `=1` ==> `=1`) subst_cons.
Proof. intros x y -> f f' Hff'. intros i. destruct i; simpl; trivial. Qed.

Definition shift : nat -> term := tRel ∘ S.
Notation "↑" := shift : sigma_scope.

Definition subst_compose (σ τ : nat -> term) :=
  fun i => (σ i).[τ].

Infix "∘s" := subst_compose (at level 40) : sigma_scope.

Instance subst_compose_proper : Proper (`=1` ==> `=1` ==> `=1`) subst_compose.
Proof.
  intros f f' Hff' g g' Hgg'. intros x. unfold subst_compose.
  now rewrite Hgg' Hff'.
Qed.

Definition Up σ : substitution := tRel 0 ⋅ (σ ∘s ↑).
Notation "⇑ s" := (Up s) (at level 20).

Instance Up_ext : Proper (`=1` ==> `=1`) Up.
Proof.
  unfold Up. reduce_goal. unfold subst_compose, subst_cons.
  destruct a => //. now rewrite H.
Qed.

Lemma up_Up σ : up 1 σ =1 ⇑ σ.
Proof.
  unfold up.
  intros i.
  elim (Nat.leb_spec 1 i) => H.
  - unfold subst_cons, shift. destruct i.
    -- lia.
    -- simpl. rewrite Nat.sub_0_r.
       unfold subst_compose.
       now rewrite rename_inst.
  - red in H. destruct i; [|lia]. reflexivity.
Qed.

(** Simplify away [up 1] *)
Hint Rewrite up_Up : sigma.

Definition ids (x : nat) := tRel x.

Definition ren_id (x : nat) := x.

Lemma ren_id_ids : ren ren_id =1 ids.
Proof. reflexivity. Qed.

Lemma shiftn_id n : shiftn n ren_id =1 ren_id.
Proof.
  intros i; unfold shiftn.
  elim (Nat.ltb_spec i n) => H //.
  unfold ren_id. lia.
Qed.

Lemma rename_ren_id : rename ren_id =1 id.
Proof.
  intros t. unfold id.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal; auto. now rewrite shiftn_id.
  - f_equal; auto. now rewrite shiftn_id.
  - f_equal; auto. now rewrite shiftn_id.
  - setoid_rewrite shiftn_id. f_equal; solve_all. 
    now rewrite shiftn_id.
  - f_equal; auto. solve_all.
    apply map_def_id_spec; auto.
    now rewrite shiftn_id.
  - f_equal; auto. solve_all.
    apply map_def_id_spec; auto.
    now rewrite shiftn_id.
Qed.

Lemma subst_ids t : t.[ids] = t.
Proof.
  now rewrite -ren_id_ids -rename_inst rename_ren_id.
Qed.

Hint Rewrite subst_ids : sigma.

Lemma compose_ids_r σ : σ ∘s ids =1 σ.
Proof.
  unfold subst_compose. intros i; apply subst_ids.
Qed.

Lemma compose_ids_l σ : ids ∘s σ =1 σ.
Proof. reflexivity. Qed.

Hint Rewrite compose_ids_r compose_ids_l : sigma.

Definition shiftk (k : nat) (x : nat) := tRel (k + x).
Notation "↑^ k" := (shiftk k) (at level 30, k at level 2, format "↑^ k") : sigma_scope.

Lemma shiftk_0 : shiftk 0 =1 ids.
Proof.
  intros i. reflexivity.
Qed.

Definition subst_consn {A} (l : list A) (σ : nat -> A) :=
  fun i =>
    match List.nth_error l i with
    | None => σ (i - List.length l)
    | Some t => t
    end.

Notation " t ⋅n s " := (subst_consn t s) (at level 40) : sigma_scope.

Lemma subst_consn_nil {A} (σ : nat -> A) : nil ⋅n σ =1 σ.
Proof.
  intros i. unfold subst_consn. rewrite nth_error_nil.
  now rewrite Nat.sub_0_r.
Qed.
Hint Rewrite @subst_consn_nil : sigma.

Lemma subst_consn_subst_cons t l σ : (t :: l) ⋅n σ =1 (t ⋅ subst_consn l σ).
Proof.
  intros i. unfold subst_consn. induction i; simpl; trivial.
Qed.

Lemma subst_consn_tip t σ : [t] ⋅n σ =1 (t ⋅ σ).
Proof. now rewrite subst_consn_subst_cons subst_consn_nil. Qed.
Hint Rewrite @subst_consn_tip : sigma.

Instance subst_consn_proper {A} : Proper (Logic.eq ==> `=1` ==> `=1`) (@subst_consn A).
Proof.
  intros ? l -> f f' Hff' i.
  unfold subst_consn. destruct nth_error eqn:Heq; auto.
Qed.

Instance subst_consn_proper_ext {A} : Proper (Logic.eq ==> `=1` ==> Logic.eq ==> Logic.eq) (@subst_consn A).
Proof.
  intros ? l -> f f' Hff' i i' <-.
  unfold subst_consn. destruct nth_error eqn:Heq; auto.
Qed.

Fixpoint idsn n : list term :=
  match n with
  | 0 => []
  | S n => idsn n ++ [tRel n]
  end.

Definition subst_cons_gen {A} (t : A) (f : nat -> A) :=
  fun i =>
    match i with
    | 0 => t
    | S n => f n
    end.

Instance subst_cons_gen_proper {A} : Proper (Logic.eq ==> `=1` ==> `=1`) (@subst_cons_gen A).
Proof. intros x y <- f g Hfg i. destruct i; simpl; auto. Qed.

Lemma subst_consn_subst_cons_gen {A} (t : A) l σ : subst_consn (t :: l) σ =1 (subst_cons_gen t (l ⋅n σ)).
Proof.
  intros i. unfold subst_consn. induction i; simpl; trivial.
Qed.

Lemma subst_consn_app {A} {l l' : list A} {σ} : (l ++ l') ⋅n σ =1 l ⋅n (l' ⋅n σ).
Proof.
  induction l; simpl; auto.
  - now rewrite subst_consn_nil.
  - now rewrite !subst_consn_subst_cons_gen IHl.
Qed.

Lemma subst_consn_ge {A} {l : list A} {i σ} : #|l| <= i -> (l ⋅n σ) i = σ (i - #|l|).
Proof.
  induction l in i, σ |- *; simpl.
  - now rewrite subst_consn_nil.
  - rewrite subst_consn_subst_cons_gen.
    intros H. destruct i; [lia|]. simpl.
    apply IHl. lia.
Qed.

Lemma subst_consn_lt {A} {l : list A} {i} :
  i < #|l| ->
  ∑ x, (List.nth_error l i = Some x) /\ (forall σ, (l ⋅n σ) i = x)%type.
Proof.
  induction l in i |- *; simpl.
  - intros H; elimtype False; lia.
  - intros H.
    destruct i.
    + simpl. exists a. split; auto.
    + specialize (IHl i). forward IHl.
      * lia.
      * destruct IHl as [x [Hnth Hsubst_cons]].
        exists x. simpl. split; auto.
Qed.

Lemma idsn_length n : #|idsn n| = n.
Proof.
  induction n; simpl; auto. rewrite app_length IHn; simpl; lia.
Qed.
Hint Rewrite idsn_length : len.

Lemma idsn_lt {n i} : i < n -> nth_error (idsn n) i = Some (tRel i).
Proof.
  induction n in i |- *; simpl; auto.
  - intros H; lia.
  - intros H. destruct (Compare_dec.le_lt_dec n i).
    -- assert (n = i) by lia; subst.
       rewrite nth_error_app_ge idsn_length ?Nat.sub_diag; trea.
    -- rewrite nth_error_app_lt ?idsn_length //. apply IHn; lia.
Qed.

Lemma nth_error_idsn_Some :
  forall n k,
    k < n ->
    nth_error (idsn n) k = Some (tRel k).
Proof.
  intros n k h.
  induction n in k, h |- *.
  - inversion h.
  - simpl. destruct (Nat.ltb_spec0 k n).
    + rewrite nth_error_app1.
      * rewrite idsn_length. auto.
      * eapply IHn. assumption.
    + assert (k = n) by lia. subst.
      rewrite nth_error_app2.
      * rewrite idsn_length. auto.
      * rewrite idsn_length. replace (n - n) with 0 by lia.
        simpl. reflexivity.
Qed.

Lemma nth_error_idsn_None :
  forall n k,
    k >= n ->
    nth_error (idsn n) k = None.
Proof.
  intros n k h.
  eapply nth_error_None.
  rewrite idsn_length. auto.
Qed.


Lemma subst_cons_0 t σ : (tRel 0).[t ⋅ σ] = t. Proof. reflexivity. Qed.
Lemma subst_cons_shift t σ : ↑ ∘s (t ⋅ σ) = σ. Proof. reflexivity. Qed.
Hint Rewrite subst_cons_0 subst_cons_shift : sigma.

Lemma shiftk_shift n : ↑^(S n) =1 ↑^n ∘s ↑. Proof. reflexivity. Qed.

Lemma shiftk_shift_l n : ↑^(S n) =1 ↑ ∘s ↑^n.
Proof.
  intros i.
  unfold shiftk. unfold subst_compose, shift.
  simpl. f_equal. lia.
Qed.

Lemma subst_subst_consn s σ τ : (s ⋅ σ) ∘s τ =1 (s.[τ] ⋅ σ ∘s τ).
Proof.
  intros i.
  destruct i; simpl; reflexivity.
Qed.

Hint Rewrite subst_subst_consn : sigma.

Definition Upn n σ := idsn n ⋅n (σ ∘s ↑^n).
Notation "⇑^ n σ" := (Upn n σ) (at level 30, n at level 2, format "⇑^ n  σ") : sigma_scope.

Instance Upn_ext n : Proper (`=1` ==> `=1`) (Upn n).
Proof.
  unfold Upn. reduce_goal. now rewrite H.
Qed.

Lemma Upn_0 σ : ⇑^0 σ =1 σ.
Proof.
  unfold Upn. simpl.
  now rewrite subst_consn_nil shiftk_0 compose_ids_r.
Qed.

Lemma Upn_1_Up σ : ⇑^1 σ =1 ⇑ σ.
Proof.
  unfold Upn.
  intros i. destruct i; auto.
  simpl. rewrite subst_consn_ge; simpl; auto with arith.
Qed.
Hint Rewrite Upn_1_Up : sigma.

Lemma Upn_eq n σ : Upn n σ = idsn n ⋅n (σ ∘s ↑^n).
Proof. reflexivity. Qed.

Lemma Upn_proper : Proper (Logic.eq ==> `=1` ==> `=1`) Upn.
Proof. intros ? ? -> f g Hfg. unfold Upn. now rewrite Hfg. Qed.

(** The σ-calculus equations for Coq *)

Lemma inst_app {s t σ} : (tApp s t).[σ] = tApp s.[σ] t.[σ].
Proof. reflexivity. Qed.

Lemma inst_lam {na t b σ} : (tLambda na t b).[σ] = tLambda na t.[σ] b.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma inst_prod {na t b σ} : (tProd na t b).[σ] = tProd na t.[σ] b.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma inst_letin {na t b b' σ} : (tLetIn na t b b').[σ] = tLetIn na t.[σ] b.[σ] b'.[⇑ σ].
Proof.
  simpl. now rewrite up_Up.
Qed.

Lemma up_Upn {n σ} : up n σ =1 ⇑^n σ.
Proof.
  unfold up, Upn.
  intros i.
  elim (Nat.leb_spec n i) => H.
  - rewrite rename_inst.
    rewrite subst_consn_ge; rewrite idsn_length; auto.
  - assert (Hle: i < #|idsn n|) by (rewrite idsn_length; lia).
    edestruct (subst_consn_lt Hle) as [x [Hnth Hsubst_cons]].
    rewrite Hsubst_cons. rewrite idsn_lt in Hnth; auto. congruence.
Qed.

Lemma inst_fix {mfix idx σ} : (tFix mfix idx).[σ] =
                              tFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec => //.
  now rewrite up_Upn.
Qed.

Lemma inst_cofix {mfix idx σ} : (tCoFix mfix idx).[σ] =
                                tCoFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec => //.
  now rewrite up_Upn.
Qed.

Lemma inst_mkApps :
  forall t l σ,
    (mkApps t l).[σ] = mkApps t.[σ] (map (inst σ) l).
Proof.
  intros t l σ.
  induction l in t, σ |- *.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Hint Rewrite @inst_app @inst_lam @inst_prod @inst_letin @inst_fix @inst_cofix
     @inst_mkApps : sigma.


Lemma ren_shift : ↑ =1 ren S.
Proof. reflexivity. Qed.

Lemma compose_ren f g : ren f ∘s ren g =1 ren (g ∘ f).
Proof.
  intros i.
  destruct i; simpl; reflexivity.
Qed.

Lemma subst_cons_ren i f : (tRel i ⋅ ren f) =1 ren (subst_cons_gen i f).
Proof.
  intros x; destruct x; auto.
Qed.

Fixpoint ren_ids (n : nat) :=
  match n with
  | 0 => []
  | S n => ren_ids n ++ [n]
  end.

Lemma ren_ids_length n : #|ren_ids n| = n.
Proof. induction n; simpl; auto. rewrite app_length IHn; simpl; lia. Qed.

Lemma ren_ids_lt {n i} : i < n -> nth_error (ren_ids n) i = Some i.
Proof.
  induction n in i |- *; simpl; auto.
  - intros H; lia.
  - intros H. destruct (Compare_dec.le_lt_dec n i).
    -- assert (n = i) by lia; subst.
       rewrite nth_error_app_ge ren_ids_length ?Nat.sub_diag; trea.
    -- rewrite nth_error_app_lt ?ren_ids_length //. apply IHn; lia.
Qed.

Infix "=2" := (Logic.eq ==> (pointwise_relation _ Logic.eq))%signature (at level 80).

Definition compose2 {A B C} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Infix "∘'" := compose2 (at level 90).

Delimit Scope program_scope with prog.

Lemma subst_consn_subst_cons' {A} (t : A) l : subst_consn (t :: l) =2 ((subst_cons_gen t) ∘ (subst_consn l)).
Proof. red.
  intros x y <-. apply subst_consn_subst_cons_gen.
Qed.

Lemma subst_consn_ids_ren n f : (idsn n ⋅n ren f) =1 ren (ren_ids n ⋅n f).
Proof.
  intros i.
  destruct (Nat.leb_spec n i).
  - rewrite subst_consn_ge idsn_length; auto.
    unfold ren. f_equal. rewrite subst_consn_ge ren_ids_length; auto.
  - assert (Hr:i < #|ren_ids n|) by (rewrite ren_ids_length; lia).
    assert (Hi:i < #|idsn n|) by (rewrite idsn_length; lia).
    destruct (subst_consn_lt Hi) as [x' [Hnth He]].
    destruct (subst_consn_lt Hr) as [x'' [Hnth' He']].
    rewrite (idsn_lt H) in Hnth.
    rewrite (ren_ids_lt H) in Hnth'.
    injection Hnth as <-. injection Hnth' as <-. rewrite He.
    unfold ren. now rewrite He'.
Qed.

Lemma ren_shiftk n : ↑^n =1 ren (Nat.add n).
Proof. reflexivity. Qed.

(** Specific lemma for the fix/cofix cases where we are subst_cons'ing a list of ids in front
    of the substitution. *)
Lemma ren_subst_consn_comm:
  forall (f : nat -> nat) (σ : nat -> term) (n : nat),
    ren (subst_consn (ren_ids n) (Init.Nat.add n ∘ f)) ∘s subst_consn (idsn n) (σ ∘s ↑^n) =1
    subst_consn (idsn n) (ren f ∘s σ ∘s ↑^n).
Proof.
  intros f σ m i.
  destruct (Nat.leb_spec m i).
  -- unfold ren, subst_compose. simpl.
     rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length; try lia.
     rewrite [subst_consn (ren_ids _) _ i]subst_consn_ge ?ren_ids_length; try lia.
     rewrite subst_consn_ge ?idsn_length; lia_f_equal.
  -- assert (Hr:i < #|ren_ids m |) by (rewrite ren_ids_length; lia).
     assert (Hi:i < #|idsn m |) by (rewrite idsn_length; lia).
     destruct (subst_consn_lt Hi) as [x' [Hnth He]].
     rewrite He.
     unfold ren, subst_compose. simpl.
     destruct (subst_consn_lt Hr) as [x'' [Hnth' He']].
     rewrite He'. rewrite (idsn_lt H) in Hnth. injection Hnth as <-.
     rewrite (ren_ids_lt H) in Hnth'. injection Hnth' as <-.
     rewrite He. reflexivity.
Qed.

(** Simplify away iterated up's *)
Hint Rewrite @up_Upn : sigma.

Lemma rename_inst_assoc t f σ : t.[ren f].[σ] = t.[ren f ∘s σ].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. sigma.
    unfold Up.
    simpl. rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto; solve_all; sigma.
    * rewrite map_predicate_map_predicate; solve_all.
      rewrite !ren_shiftn e -ren_shiftn.
      rewrite !up_Upn. unfold Upn.
      rewrite !compose_ren !subst_consn_ids_ren.
      apply inst_ext. apply ren_subst_consn_comm.
    * rewrite map_map_compose. solve_all.
      rewrite map_branch_map_branch. apply map_branch_eq_spec.
      sigma.
      unfold Upn. rewrite !compose_ren !subst_consn_ids_ren H0.
      apply inst_ext, ren_subst_consn_comm.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite map_def_map_def map_length. apply map_def_eq_spec; solve_all.
    sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext. apply ren_subst_consn_comm.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite map_def_map_def map_length. apply map_def_eq_spec; solve_all.
    sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext, ren_subst_consn_comm.
Qed.

Lemma inst_rename_assoc_n:
  forall (f : nat -> nat) (σ : nat -> term) (n : nat),
    subst_consn (idsn n) (σ ∘s ↑^n) ∘s ren (subst_consn (ren_ids n) (Init.Nat.add n ∘ f)) =1
    subst_consn (idsn n) (σ ∘s ren f ∘s ↑^n).
Proof.
  intros f σ m. rewrite ren_shiftk.
  intros i.
  destruct (Nat.leb_spec m i).
  -- rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length; try lia.
     unfold subst_compose.
     rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length; try lia.
     rewrite !rename_inst_assoc !compose_ren.
     apply inst_ext. intros i'.
     unfold ren. f_equal. rewrite subst_consn_ge ?ren_ids_length; try lia.
     now assert (m + i' - m = i') as -> by lia.
  -- assert (Hr:i < #|ren_ids m |) by (rewrite ren_ids_length; lia).
     assert (Hi:i < #|idsn m |) by (rewrite idsn_length; lia).
     destruct (subst_consn_lt Hi) as [x' [Hnth He]].
     rewrite He.
     unfold subst_compose. simpl.
     rewrite (idsn_lt H) in Hnth. injection Hnth as <-. rewrite He.
     simpl. unfold ren. f_equal.
     destruct (subst_consn_lt Hr) as [x'' [Hnth' He']].
     rewrite (ren_ids_lt H) in Hnth'. injection Hnth' as <-. now rewrite He'.
Qed.

Lemma inst_rename_assoc t f σ : t.[σ].[ren f] = t.[σ ∘s ren f].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto. simpl.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto; solve_all; sigma.
    * rewrite map_predicate_map_predicate. apply map_predicate_eq_spec => //.
      + solve_all.
      + rewrite !up_Upn. unfold Upn; rewrite !compose_ren subst_consn_ids_ren e /=.
        apply inst_ext, inst_rename_assoc_n.
    * rewrite map_map_compose; solve_all; rewrite map_branch_map_branch; 
      apply map_branch_eq_spec. sigma.
      unfold Upn; rewrite !compose_ren subst_consn_ids_ren H0 /=.
      apply inst_ext, inst_rename_assoc_n.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite map_def_map_def map_length. apply map_def_eq_spec; solve_all.
    sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext. apply inst_rename_assoc_n.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite map_def_map_def map_length. apply map_def_eq_spec; solve_all.
    sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext, inst_rename_assoc_n.
Qed.

Lemma rename_subst_compose1 r s s' : ren r ∘s (s ∘s s') =1 ren r ∘s s ∘s s'.
Proof. unfold subst_compose. simpl. intros i. reflexivity. Qed.

Lemma rename_subst_compose2 r s s' : s ∘s (ren r ∘s s') =1 s ∘s ren r ∘s s'.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite rename_inst_assoc. reflexivity.
Qed.

Lemma rename_subst_compose3 r s s' : s ∘s (s' ∘s ren r) =1 s ∘s s' ∘s ren r.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite inst_rename_assoc. reflexivity.
Qed.

Lemma Up_Up_assoc:
  forall s s' : nat -> term, (⇑ s) ∘s (⇑ s') =1 ⇑ (s ∘s s').
Proof.
  intros s s'.
  unfold Up.
  rewrite ren_shift.
  rewrite subst_subst_consn.
  simpl. apply subst_cons_proper => //.
  rewrite - rename_subst_compose2.
  rewrite - rename_subst_compose3.
  now apply subst_compose_proper; auto.
Qed.

Hint Rewrite Up_Up_assoc : sigma.

Lemma up_up_assoc:
  forall (s s' : nat -> term) (n : nat), up n s ∘s up n s' =1 up n (s ∘s s').
Proof.
  intros s s' n i.
  unfold up, subst_compose. simpl.
  destruct (Nat.leb_spec n i).
  - rewrite !(rename_inst (Nat.add n) (s (i - n))).
    rewrite rename_inst_assoc.
    rewrite !(rename_inst (Nat.add n) _).
    rewrite inst_rename_assoc.
    apply inst_ext.
    intros i'. unfold subst_compose.
    unfold ren. simpl.
    destruct (Nat.leb_spec n (n + i')).
    * rewrite rename_inst.
      now assert (n + i' - n = i') as -> by lia.
    * lia.
  - simpl.
    destruct (Nat.leb_spec n i); lia_f_equal.
Qed.

Lemma inst_assoc t s s' : t.[s].[s'] = t.[s ∘s s'].
Proof.
  revert s s'.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. sigma.
    now rewrite H1 Up_Up_assoc.
  - f_equal; auto.
    * rewrite map_predicate_map_predicate; solve_all.
      now rewrite e up_up_assoc.
    * rewrite map_map_compose; solve_all.
      rewrite map_branch_map_branch. apply map_branch_eq_spec; solve_all.
      now rewrite H0 up_up_assoc.
  - f_equal; auto. sigma.
    rewrite map_map_compose; solve_all.
    rewrite map_def_map_def.
    apply map_def_eq_spec; auto.
    rewrite b.
    now rewrite map_length up_up_assoc.
  - f_equal; auto. sigma.
    rewrite map_map_compose; solve_all.
    rewrite map_def_map_def.
    apply map_def_eq_spec; auto.
    rewrite b.
    now rewrite map_length up_up_assoc.
Qed.

Hint Rewrite inst_assoc : sigma.

Lemma subst_compose_assoc s s' s'' : (s ∘s s') ∘s s'' =1 s ∘s (s' ∘s s'').
Proof.
  intros i; unfold subst_compose at 1 3 4.
  now rewrite inst_assoc.
Qed.

Hint Rewrite subst_compose_assoc : sigma.

Lemma subst_cons_0_shift : (tRel 0 ⋅ ↑) =1 ids.
Proof. intros i. destruct i; reflexivity. Qed.

Hint Rewrite subst_cons_0_shift : sigma.

Lemma subst_cons_0s_shifts σ : ((σ 0) ⋅ (↑ ∘s σ)) =1 σ.
Proof.
  intros i. destruct i; auto.
Qed.

Hint Rewrite subst_cons_0s_shifts : sigma.

Lemma Upn_Up σ n : ⇑^(S n) σ =1 ⇑^n ⇑ σ.
Proof.
  intros i. unfold Upn.
  simpl. rewrite subst_consn_app.
  rewrite subst_consn_tip. unfold Up. apply subst_consn_proper; auto.
  rewrite shiftk_shift_l.
  intros i'. unfold subst_cons, subst_compose.
  destruct i' => //; auto; simpl. 
  - unfold shiftk. now rewrite Nat.add_0_r.
  - simpl. now rewrite inst_assoc.
Qed.

Lemma Upn_1 σ : ⇑^1 σ =1 ⇑ σ.
Proof. now rewrite Upn_Up Upn_0. Qed.

Lemma Upn_S σ n : ⇑^(S n) σ =1 ⇑ ⇑^n σ.
Proof.
  rewrite Upn_Up. induction n in σ |- *.
  * rewrite !Upn_0. now eapply Up_ext.
  * rewrite Upn_Up. rewrite IHn. eapply Up_ext. now rewrite Upn_Up.
Qed.
Hint Rewrite Upn_0 Upn_S : sigma.

(* Print Rewrite HintDb sigma. *)

Lemma subst_inst_aux s k t : subst s k t = inst (up k (subst_fn s)) t.
Proof.
  revert s k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - unfold subst_fn, up.
    elim (Nat.leb_spec k n) => //.
    intros H.
    destruct nth_error eqn:Heq.
    * apply lift_rename.
    * simpl. eapply nth_error_None in Heq. lia_f_equal.
  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H1. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    * apply map_predicate_eq_spec; auto; solve_all.
      rewrite e. now rewrite (up_up #|pcontext p| k).
    * solve_all. apply map_branch_eq_spec.
      now rewrite (up_up #|bcontext x| k).
  - f_equal; eauto; solve_all; auto. apply map_def_eq_spec; auto.
    rewrite b. apply inst_ext. intros t'; now rewrite (up_up #|m| k).
  - f_equal; eauto.
    solve_all; auto. apply map_def_eq_spec; auto.
    rewrite b. apply inst_ext. intros t'; now rewrite (up_up #|m| k).
Qed.

Lemma subst_fn_subst_consn s : subst_fn s =1 subst_consn s ids.
Proof. reflexivity. Qed.

Theorem subst_inst s k t : subst s k t = inst (⇑^k (subst_consn s ids)) t.
Proof.
  rewrite subst_inst_aux up_Upn. apply inst_ext.
  unfold Upn. now rewrite subst_fn_subst_consn.
Qed.

(** Simplify away [subst] to the σ-calculus [inst] primitive. *)
Hint Rewrite @subst_inst : sigma.
Hint Rewrite @subst_consn_nil : sigma.

Hint Rewrite shiftk_shift_l shiftk_shift : sigma.
(* Hint Rewrite Upn_eq : sigma. *)


Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

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
  induction n in l |- *; simpl; intros; sigma.
  - destruct l; try discriminate. now sigma. 
  - destruct l; try discriminate. simpl in *.
    rewrite subst_consn_subst_cons.
    simpl; sigma. apply IHn. lia.
Qed.

Lemma shiftn_consn_idsn n σ : ↑^n ∘s ⇑^n σ =1 σ ∘s ↑^n.
Proof.
  unfold Upn. rewrite subst_consn_shiftn; [reflexivity|].
  now rewrite idsn_length.
Qed.
(* Hint Rewrite shiftn_consn_idsn: sigma. *)

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

Lemma Upn_Upn k k' σ : ⇑^(k + k') σ =1 ⇑^k (⇑^k' σ).
Proof.
  setoid_rewrite <- up_Upn. rewrite -(@up_Upn k').
  symmetry; apply up_up.
Qed.
Hint Rewrite Upn_Upn : sigma.

Lemma Upn_compose n σ σ' : ⇑^n σ ∘s ⇑^n σ' =1 ⇑^n (σ ∘s σ').
Proof.
  induction n.
  - unfold Upn. simpl.
    now rewrite !subst_consn_nil !shiftk_0 !compose_ids_r.
  - setoid_rewrite Upn_S. sigma. now rewrite IHn.
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
  all: sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_length 
    ?map_predicate_map_predicate ?map_branch_map_branch; unfold map_branch.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - unfold Upn, shift, subst_compose, subst_consn.
    destruct (Nat.ltb_spec0 n k).
    + rewrite nth_error_idsn_Some. 1: assumption.
      reflexivity.
    + rewrite nth_error_idsn_None. 1: lia.
      reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)).
    setoid_rewrite Upn_S in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)).
    setoid_rewrite Upn_S in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1 IHt2. specialize (IHt3 (S k)).
    setoid_rewrite Upn_S in IHt3.
    rewrite IHt3. reflexivity.
  - f_equal.
    * destruct X. solve_all. sigma.
      setoid_rewrite <-Upn_Upn.
      now rewrite e.
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
      sigma.
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

Lemma nth_error_idsn_eq_Some n k i : nth_error (idsn n) k = Some i -> i = tRel k.
Proof.
  intros hnth.
  move: (nth_error_Some_length hnth).
  len. move/nth_error_idsn_Some.
  now rewrite hnth => [= ->].
Qed.