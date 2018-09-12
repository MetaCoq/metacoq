(* Distributed under the terms of the MIT license.   *)

Require Import List Program.
From Template Require Import Ast AstUtils.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Require Import Template.Induction.

(** * Lifting and substitution for the AST

  Along with standard commutation lemmas.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Set Asymmetric Patterns.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (List.map (lift n k) v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tCast c kind t => tCast (lift n k c) kind (lift n k t)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (lift n k)) brs in
    tCase ind (lift n k p) (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.


Notation lift0 n := (lift n 0).
Definition up := lift 1 0.

(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)

Fixpoint parsubst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (parsubst s k) args)
  | tLambda na T M => tLambda na (parsubst s k T) (parsubst s (S k) M)
  | tApp u v => mkApps (parsubst s k u) (List.map (parsubst s k) v)
  | tProd na A B => tProd na (parsubst s k A) (parsubst s (S k) B)
  | tCast c kind ty => tCast (parsubst s k c) kind (parsubst s k ty)
  | tLetIn na b ty b' => tLetIn na (parsubst s k b) (parsubst s k ty) (parsubst s (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (parsubst s k)) brs in
    tCase ind (parsubst s k p) (parsubst s k c) brs'
  | tProj p c => tProj p (parsubst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (parsubst s k) (parsubst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (parsubst s k) (parsubst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation parsubst0 t := (parsubst t 0).
Definition subst t k u := parsubst [t] k u.
Notation subst0 t := (subst t 0).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity).

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Definition substl s := parsubst s 0.

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && List.forallb (closedn k) v
  | tCast c kind t => closedn k c && closedn k t
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let brs' := List.forallb (test_snd (closedn k)) brs in
    closedn k p && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | x => true
  end.

Notation closed t := (closedn 0 t).

Create HintDb terms.

Ltac easy0 :=
  let rec use_hyp H :=
   (match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try (solve [ inversion H ])
    end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro)
  in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end)
  in
  let do_atom := (solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ]) in
  let rec do_ccl := (try do_atom; repeat (do_intro; try do_atom); (solve [ split; do_ccl ])) in
  (solve [ do_atom | use_hyps; do_ccl ]) || fail "Cannot solve this goal".
Require Import Omega.
Hint Extern 100 => omega : terms.

Ltac easy ::= easy0 || solve [eauto 7 with core arith terms].

Notation subst_rec N M k := (subst N k M) (only parsing).

Require Import PeanoNat.
Import Nat.

Lemma lift_rel_ge :
  forall k n p, p <= n -> lift k p (tRel n) = tRel (k + n).
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma lift_rel_lt : forall k n p, p > n -> lift k p (tRel n) = tRel n.
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma lift_rel_alt : forall n k i, lift n k (tRel i) = tRel (if Nat.leb k i then n + i else i).
Proof.
  intros; simpl. now destruct leb.
Qed.

Lemma subst_rel_lt : forall u n k, k > n -> parsubst u k (tRel n) = tRel n.
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n); intro Hcomp; easy.
Qed.

Require Import Lia.

Lemma subst_rel_gt :
  forall u n k, n >= k + length u -> parsubst u k (tRel n) = tRel (n - length u).
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n). intros. destruct nth_error eqn:Heq.
  assert (n - k < length u) by (apply nth_error_Some; congruence). lia. reflexivity.
  lia.
Qed.

Lemma subst_rel_eq :
  forall (u : list term) n i t p,
    List.nth_error u i = Some t -> p = n + i ->
    parsubst u n (tRel p) = lift0 n t.
Proof.
  intros; simpl in |- *. subst p.
  elim (leb_spec n (n + i)). intros. assert (n + i - n = i) by lia. rewrite H1, H.
  reflexivity. intros. lia.
Qed.

Lemma lift0_id : forall M k, lift 0 k M = M.
Proof.
  intros M.
  elim M using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy).

  - now elim (leb k n).
  - f_equal. rewrite <- map_id. now eapply (forall_map_spec H).
  - f_equal. auto. rewrite <- map_id. now eapply (forall_map_spec H0).
  - f_equal; auto. rewrite <- map_id. eapply (forall_map_spec H1).
    intros. destruct x; unfold on_snd. simpl. rewrite H2. reflexivity.

  - f_equal. transitivity (map (map_def id id) m). eapply (tfix_map_spec H); auto.
    rewrite <- map_id. f_equal. extensionality x. destruct x; reflexivity.
  - f_equal. transitivity (map (map_def id id) m). eapply (tfix_map_spec H); auto.
    rewrite <- map_id. f_equal. extensionality x. destruct x; reflexivity.
Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
  intros; unfold lift in |- *.
  apply lift0_id; easy.
Qed.

Lemma simpl_lift :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift p i (lift n k M) = lift (p + n) k M.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try (rewrite H, ?H0, ?H1; auto); try (f_equal; apply_spec);
        try rewrite ?map_length; try easy.

  - elim (leb_spec k n); intros.
    now rewrite lift_rel_ge.
    now rewrite lift_rel_lt.
Qed.

Lemma simpl_lift0 : forall M n, lift0 (S n) M = lift0 1 (lift0 n M).
  now intros; rewrite simpl_lift.
Qed.

Lemma permute_lift :
  forall M n k p i,
    i <= k ->
    lift p i (lift n k M) = lift n (p + k) (lift p i M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec);
      unfold compose; intros;
        try rewrite ?map_length; try easy ;
        try (rewrite H, H0; f_equal; try easy; now f_equal);
        try (rewrite H, H0, H1; f_equal; try easy; now f_equal);
        try (rewrite H1; now f_equal).
  
  - elim (leb_spec k n); intros;
    elim (leb_spec i n); intros; try easy.
    + rewrite 2!lift_rel_ge; try easy.
    + rewrite lift_rel_ge, lift_rel_lt; try easy.
    + rewrite 2!lift_rel_lt; try easy.
Qed.

Lemma permute_lift0 :
  forall M k, lift0 1 (lift 1 k M) = lift 1 (S k) (lift0 1 M).
  intros.
  change (lift 1 0 (lift 1 k M) = lift 1 (1 + k) (lift 1 0 M))
    in |- *.
  apply permute_lift; easy.
Qed.

Lemma lift_isApp n k t : ~ isApp t = true -> ~ isApp (lift n k t) = true.
Proof.
  induction t; auto.
  intros.
  simpl. destruct leb; auto.
Qed.

Lemma map_non_nil {A B} (f : A -> B) l : l <> nil -> map f l <> nil.
Proof.
  intros. intro.
  destruct l; try discriminate.
  contradiction.
Qed.

Lemma wf_lift n k t : wf t -> wf (lift n k t).
Proof.
  intros wft; revert t wft k.
  apply (term_wf_forall_list_ind (fun t => forall k, wf (lift n k t))) ; simpl; intros; try constructor; auto.

  destruct leb; constructor.
  apply Forall_map.
  induction H; constructor; auto.
  now apply lift_isApp.
  now apply map_non_nil.
  apply Forall_map. eapply Forall_impl. eauto. eauto.
  apply Forall_map. eapply Forall_impl. apply H1.
  intros [n' t]. simpl. repeat red; simpl; auto.
  apply Forall_map. red in H.
  apply (Forall_mix _ _ _ H) in H0.
  eapply Forall_impl. apply H0.
  simpl. intros. red; intuition (simpl; auto).
  destruct (dbody x); try discriminate. auto.
  apply Forall_map. eapply Forall_impl. apply H.
  simpl. intros. red; intuition (simpl; auto).
Qed.

Lemma mkApps_tApp t l :
  ~ isApp t = true -> l <> nil -> mkApps t l = tApp t l.
Proof.
  intros.
  destruct l. simpl. contradiction.
  destruct t; simpl; try reflexivity.
  simpl in H. contradiction.
Qed.

Hint Unfold compose.
Hint Transparent compose.

Lemma simpl_subst_rec :
  forall M (H : wf M) N n p k,
    p <= n + k ->
    k <= p -> parsubst N p (lift (List.length N + n) k M) = lift n k M.
Proof.
  intros M wfM. induction wfM using term_wf_forall_list_ind;
    intros; simpl; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec); intros;
        try rewrite ?map_length; try easy ||
      (try rewrite H, H0; f_equal; try easy; now f_equal).
  
  - elim (leb_spec k n); intros.
    + rewrite subst_rel_gt; f_equal; lia.
    + rewrite subst_rel_lt; try easy.

  - rewrite IHwfM; auto.
    apply (lift_isApp n k) in H.
    rewrite mkApps_tApp; auto using map_non_nil.
    f_equal. eapply forall_map_spec. apply H2; simpl; auto.
    simpl; intros. typeclasses eauto with core.
Qed.

Lemma simpl_subst :
  forall N M (H : wf M) n p, p + length N < n -> parsubst N p (lift0 (length N + n) M) = lift0 n M.
  intros; now apply simpl_subst_rec.
Qed.

Lemma mkApps_tRel n a l : mkApps (tRel n) (a :: l) = tApp (tRel n) (a :: l).
Proof.
  simpl. reflexivity.
Qed.

Lemma lift_mkApps n k t l : lift n k (mkApps t l) = mkApps (lift n k t) (map (lift n k) l).
Proof.
  revert n k t; induction l; intros n k t; destruct t; try reflexivity.
  rewrite lift_rel_alt. rewrite !mkApps_tRel.
  simpl lift.
  simpl map. rewrite !mkApps_tRel.
  f_equal. destruct leb; auto.

  simpl. f_equal.
  now rewrite map_app.
Qed.

Inductive nth_error_spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_some a : nth_error l n = Some a -> n < length l -> nth_error_spec l n (Some a)
| nth_error_none : nth_error l n = None -> length l <= n -> nth_error_spec l n None.

Lemma nth_error_elim {A} (l : list A) n : nth_error_spec l n (nth_error l n).
Proof.
  destruct (nth_error l n) eqn:Heq.
  constructor; auto. apply nth_error_Some. congruence.
  constructor; auto; apply nth_error_None. congruence.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
    k <= p ->
    lift n k (parsubst N p M) = parsubst N (n + p) (lift n k M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec);
      unfold compose; intros;
        try rewrite ?map_length; try easy ;
        try (rewrite H, H0; f_equal; try easy; now f_equal);
        try (rewrite H, H0, H1; f_equal; try easy; now f_equal);
        try (rewrite H1; now f_equal).
  
  - elim (leb_spec p n); elim (leb_spec k n); intros; subst; try easy.
    + destruct (nth_error_elim N (n - p)).
      ++ rewrite simpl_lift by easy.
         erewrite subst_rel_eq; eauto. lia.
      ++ rewrite lift_rel_ge by lia.
         rewrite subst_rel_gt; f_equal; lia.
    + rewrite subst_rel_lt by lia.
      rewrite lift_rel_ge; congruence.
    + rewrite lift_rel_lt; auto.
      rewrite subst_rel_lt; auto. lia.

  - rewrite lift_mkApps. f_equal. auto.
    rewrite map_map_compose. apply_spec. intros.
    now apply H2.
Qed.

Lemma commut_lift_subst :
  forall M N k, parsubst N (S k) (lift0 1 M) = lift0 1 (parsubst N k M).
  now intros; rewrite commut_lift_subst_rec.
Qed.

Lemma distr_lift_subst_rec :
  forall M N n p k,
    lift n (p + k) (parsubst N p M) =
    parsubst (List.map (lift n k) N) p (lift n (p + length N + k) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => cbn -[plus]
            end; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec);
      unfold compose; intros;
        try rewrite ?map_length; try easy ;
        try (erewrite H, <- H0; f_equal; try easy; now f_equal);
        try (erewrite H, <- H0, <- H1; f_equal; try easy; now f_equal);
        try (erewrite H1; now f_equal).
  
  - unfold parsubst at 1. unfold lift at 4.
    elim (leb_spec p n); intros; try easy;
    elim (leb_spec (p + length N + k) n); intros; subst; try easy.
    
    + destruct (nth_error_elim N (n - p)).
      ++ rewrite <- permute_lift by lia.
         erewrite subst_rel_eq; eauto.
         rewrite nth_error_map; eauto. rewrite e. reflexivity.
         lia.
      ++ rewrite lift_rel_ge; try easy.
         rewrite subst_rel_gt; rewrite map_length; f_equal; lia.
    + destruct (nth_error_elim N (n - p)).
      ++ rewrite <- permute_lift by lia.
         erewrite subst_rel_eq; eauto.
         rewrite nth_error_map. rewrite e. reflexivity. lia.
      ++ rewrite lift_rel_lt; try easy.
         rewrite subst_rel_gt; rewrite map_length; auto. lia.
    + rewrite lift_rel_lt; try easy.
      now rewrite subst_rel_lt.
  - rewrite lift_mkApps. f_equal; auto.
    rewrite map_map_compose; apply_spec; simpl.
    intros. apply H1.
  - rewrite add_assoc, H0. f_equal. now f_equal.
  - rewrite add_assoc, H0. f_equal. now f_equal.
Qed.

Lemma distr_lift_subst :
  forall M N n k,
    lift n k (subst0 N M) = subst0 (lift n k N) (lift n (S k) M).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma mkApp_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l; destruct f; destruct l'; simpl; rewrite ?app_nil_r; auto.
  f_equal. now rewrite <- app_assoc.
Qed.

Lemma parsubst_mkApps u k t l :
  parsubst u k (mkApps t l) = mkApps (parsubst u k t) (map (parsubst u k) l).
Proof.
  revert u k t; induction l; intros u k t; destruct t; try reflexivity.
  intros. simpl mkApps at 1. simpl parsubst at 1 2. rewrite map_app. now rewrite mkApp_nested.
Qed.

Lemma subst_mkApps u k t l : subst u k (mkApps t l) = mkApps (subst u k t) (map (subst u k) l).
Proof.
  apply parsubst_mkApps.
Qed.

Lemma distr_subst_rec :
  forall M N (P : list term) (wfP : Forall wf P) n p,
    parsubst P (p + n) (parsubst N p M) =
    parsubst (map (parsubst P n) N) p (parsubst P (p + length N + n) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => simpl
            end; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec);
      unfold compose; intros;
        try rewrite ?map_length; try easy ;
        try (erewrite H, <- H0; f_equal; try easy; now f_equal);
        try (erewrite H, <- H0, <- H1; f_equal; try easy; now f_equal);
        try (erewrite H1; now f_equal).
  
  - unfold parsubst at 2.
    elim (leb_spec p n); intros; try easy.
    
    + destruct (nth_error_elim N (n - p)).
      ++ rewrite subst_rel_lt by lia.
         erewrite subst_rel_eq; try easy.
         2:rewrite nth_error_map, e; reflexivity.
         now rewrite <- commut_lift_subst_rec.
      ++ unfold parsubst at 4.
         elim (leb_spec (p + length N + n0) n); intros; subst; try easy.
         destruct (nth_error_elim P (n - (p + length N + n0))).
         +++ erewrite subst_rel_eq. 2:eauto. 2:lia.
             assert (p + length N + n0 = length (map (parsubst P n0) N) + (p + n0))
               by (rewrite map_length; lia).
             rewrite H1. rewrite simpl_subst_rec; eauto; try lia.
             eapply nth_error_forall in e0; eauto.
         +++ rewrite !subst_rel_gt; rewrite ?map_length; try lia. f_equal; lia.
         +++ rewrite subst_rel_lt; try easy.
             rewrite subst_rel_gt; rewrite map_length. trivial. lia.
    + rewrite !subst_rel_lt; try easy.

  - rewrite !parsubst_mkApps. rewrite H; auto. f_equal.
    rewrite !map_map_compose. apply_spec. intros.
    unfold compose. auto.
  - rewrite add_assoc, H0; auto. f_equal. now f_equal.
  - rewrite add_assoc, H0; auto. f_equal. now f_equal.
Qed.

Lemma distr_subst :
  forall P (wfP : Forall Ast.wf P) N M k,
    parsubst P k (parsubst0 N M) = parsubst0 (map (parsubst P k) N) (parsubst P (length N + k) M).
Proof.
  intros.
  pattern k at 1 3 in |- *.
  change k with (0 + k). hnf.
  apply distr_subst_rec. auto.
Qed.

Lemma lift_closed n k t : closedn k t = true -> lift n k t = t.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try easy;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
    try rewrite ?map_length; try easy.
  - rewrite lift_rel_lt; auto.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
  - simpl lift; f_equal.
    rewrite <- map_id. 
    apply_spec; eauto.
  - simpl lift. rewrite andb_true_iff in H1. f_equal; intuition eauto.
  - simpl lift; rewrite andb_true_iff in H1. f_equal; intuition eauto.
  - simpl lift; rewrite andb_true_iff in H1. f_equal; intuition eauto.
  - simpl lift. rewrite !andb_true_iff in H2. f_equal; intuition eauto.
  - simpl lift. rewrite !andb_true_iff in H1. f_equal; intuition eauto.
    rewrite <- map_id; apply_spec; eauto.
  - simpl lift. rewrite !andb_true_iff in H2. f_equal; intuition eauto.
    transitivity (map (on_snd id) l). apply_spec; eauto.
    rewrite <- map_id. f_equal. unfold on_snd. extensionality p. now destruct p.
  - simpl lift. f_equal; eauto.
  - simpl lift. f_equal.
    transitivity (map (map_def id id) m). apply_spec; eauto.
    now autorewrite with core.
  - simpl lift. f_equal.
    transitivity (map (map_def id id) m). apply_spec; eauto.
    now autorewrite with core.
Qed.

Lemma closed_upwards k t : closedn k t = true -> forall k', k' >= k -> closedn k' t = true.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try lia;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (try f_equal; simpl; apply_spec; eauto); simpl closed in *;
        try (apply_spec; eauto with arith);
        try (rewrite ?andb_true_iff in *; intuition eauto 4 with arith).

  - elim (ltb_spec n k'); auto. intros.
    apply ltb_lt in H. lia.

  - apply_spec. eauto with arith.
  - red in H1. apply_spec. intros. destruct x; unfold test_snd; simpl in *. eauto with arith.
  - red in H. apply_spec. intros. destruct x; unfold test_def in *; simpl in *.
    rewrite andb_true_iff in *; intuition eauto with arith.
  - red in H. apply_spec. intros. destruct x; unfold test_def in *; simpl in *.
    rewrite andb_true_iff in *; intuition eauto with arith.
Qed.

Lemma mkApps_mkApp u a v : wf u -> mkApps (mkApp u a) v = mkApps u (a :: v).
Proof.
  induction v. simpl.
  destruct u; simpl; try reflexivity.
  intros. simpl.
  destruct u; simpl; try reflexivity.
  inversion_clear H. simpl in H0. f_equal.
  now rewrite <- app_assoc.
Qed.

Lemma wf_mkApp u a : wf u -> wf a -> wf (mkApp u a).
Proof.
  intros H H'.
  inversion_clear H; try constructor; simpl; auto; try congruence; try constructor; auto.
  intro. destruct u0; simpl in *; congruence.
  apply Forall_app_inv. split; auto.
Qed.

Lemma wf_mkApps u a : wf u -> List.Forall wf a -> wf (mkApps u a).
Proof.
  intros H H'.
  induction a; simpl; auto.
  inversion_clear H; try constructor; simpl; auto; try congruence; try constructor; auto.
  intro. destruct u0; simpl in *; congruence.
  apply Forall_app_inv. split; auto.
Qed.

Lemma wf_parsubst ts k u : List.Forall wf ts -> wf u -> wf (parsubst ts k u).
Proof.
  intros wfts wfu.
  induction wfu in k using term_wf_forall_list_ind; simpl; intros; try constructor; auto.

  - unfold parsubst. destruct (leb_spec k n).
    destruct nth_error eqn:Heq. apply (nth_error_forall Heq) in wfts.
    apply wf_lift; auto. constructor. constructor.
  - apply Forall_map. eapply Forall_impl; eauto.
  - apply wf_mkApps; auto. apply Forall_map. eapply Forall_impl; eauto.
  - apply Forall_map. eapply Forall_impl; eauto. intros. apply H0.
  - merge_Forall. apply Forall_map. eapply Forall_impl; eauto. intros.
    destruct x; simpl in *. red; simpl; intuition auto.
    induction dbody; try discriminate. reflexivity.
  - apply Forall_map. eapply Forall_impl; eauto. intros.
    destruct x; simpl in *. red; simpl; intuition auto.
Qed.

Lemma wf_subst t k u : wf t -> wf u -> wf (subst t k u).
Proof.
  intros wft wfu. apply wf_parsubst. constructor; auto. auto.
Qed.

Definition substl' l t :=
  List.fold_left (fun t u => subst0 u t) l t.

Lemma wf_substl' ts u : List.Forall wf ts -> wf u -> wf (substl' ts u).
Proof.
  intros wfts wfu.
  induction wfts in u, wfu; simpl; intros; try constructor; auto.
  apply IHwfts. now apply wf_subst.
Qed.

Lemma parsubst_empty k a : Ast.wf a -> parsubst [] k a = a.
Proof.
  induction 1 in k |- * using term_wf_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; apply_spec; eauto].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (n - k > 0) by lia.
    assert (exists n', n - k = S n'). exists (pred (n - k)). lia.
    destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
  - rewrite IHwf. rewrite mkApps_tApp; eauto with wf.
    f_equal; apply_spec. auto.
  - rewrite IHwf, IHwf0. f_equal. red in H. apply_spec. intros; eauto.
    destruct x; unfold on_snd; simpl in *; congruence.
  - f_equal. clear H0. red in H; apply_spec. intuition auto.
    destruct x; unfold map_def; simpl in *; congruence.
  - f_equal. red in H; apply_spec. intuition auto.
    destruct x; unfold map_def; simpl in *; congruence.
Qed.
