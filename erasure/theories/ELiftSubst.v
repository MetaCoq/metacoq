(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program BinPos Arith.Compare_dec Bool Lia.
From MetaCoq.Template Require Import Ast AstUtils utils.
From MetaCoq.Erasure Require Import EAst EInduction.


(** * Lifting and substitution for the AST

  Along with standard commutation lemmas.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Set Asymmetric Patterns.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na M => tLambda na (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tLetIn na b b' => tLetIn na (lift n k b) (lift n (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (on_snd (lift n k)) brs in
    tCase ind (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tCoFix mfix' idx
  | tBox => t
  | tVar _ => t
  | tConst _ => t
  | tConstruct _ _ => t
  end.


Notation lift0 n := (lift n 0).
Definition up := lift 1 0.

(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na M => tLambda na (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tLetIn na b b' => tLetIn na (subst s k b) (subst s (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (on_snd (subst s k)) brs in
    tCase ind (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ M => closedn (S k) M
  | tApp u v => closedn k u && closedn k v
  | tLetIn na b b' => closedn k b && closedn (S k) b'
  | tCase ind c brs =>
    let brs' := List.forallb (test_snd (closedn k)) brs in
    closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k')) mfix
  | x => true
  end.

Notation closed t := (closedn 0 t).

Create HintDb terms.

Ltac arith_congr := repeat (try lia; progress f_equal).

Ltac easy0 :=
  let rec use_hyp H :=
   (match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ * _ => exact H || destruct_hyp H
    | _ => try (solve [ inversion H ])
    end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro)
  in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ * _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end)
  in
  let do_atom := (solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction | congruence]) in
  let rec do_ccl := (try do_atom; repeat (do_intro; try do_atom); try arith_congr; (solve [ split; do_ccl ])) in
  (solve [ do_atom | use_hyps; do_ccl ]) || fail "Cannot solve this goal".


Hint Extern 10 (_ < _)%nat => lia : terms.
Hint Extern 10 (_ <= _)%nat => lia : terms.
Hint Extern 10 (@eq nat _ _) => lia : terms.

Ltac easy ::= easy0 || solve [intuition eauto 3 with core terms].

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

Lemma subst_rel_lt : forall u n k, k > n -> subst u k (tRel n) = tRel n.
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n); intro Hcomp; easy.
Qed.

Lemma subst_rel_gt :
  forall u n k, n >= k + length u -> subst u k (tRel n) = tRel (n - length u).
Proof.
  simpl in |- *; intros.
  elim (leb_spec k n). intros. destruct nth_error eqn:Heq.
  assert (n - k < length u) by (apply nth_error_Some; congruence). lia. reflexivity.
  lia.
Qed.

Lemma subst_rel_eq :
  forall (u : list term) n i t p,
    List.nth_error u i = Some t -> p = n + i ->
    subst u n (tRel p) = lift0 n t.
Proof.
  intros; simpl in |- *. subst p.
  elim (leb_spec n (n + i)). intros. assert (n + i - n = i) by lia. rewrite H1, H.
  reflexivity. intros. lia.
Qed.

Hint Extern 0 (_ = _) => progress f_equal : all.
Hint Unfold on_snd snd : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Proof.
  destruct x; simpl; unfold on_snd; simpl. split; congruence.
Qed.
Hint Resolve -> on_snd_eq_id_spec : all.

Lemma map_def_eq_spec (f g : term -> term) (x : def term) :
  f (dbody x) = g (dbody x) ->
  map_def f x = map_def g x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec (f : term -> term) (x : def term) :
  f (dbody x) = (dbody x) ->
  map_def f x = x.
Proof.
  intros. rewrite (map_def_eq_spec f id); auto. destruct x; auto.
Qed.
Hint Resolve map_def_id_spec : all.

Lemma compose_map_def (f g : term -> term) :
  compose (map_def f) (map_def g) = map_def (compose f g).
Proof. reflexivity. Qed.

Hint Extern 10 (_ < _)%nat => lia : all.
Hint Extern 10 (_ <= _)%nat => lia : all.
Hint Extern 10 (@eq nat _ _) => lia : all.

Ltac change_Sk :=
  repeat match goal with
    |- context [S (?x + ?y)] => progress change (S (x + y)) with (S x + y)
  end.

Ltac all_simpl :=
  progress (unfold compose; simpl).

Hint Extern 10 => all_simpl : all.

Ltac solve_all :=
  unfold tCaseBrsProp, tFixProp in *;
  repeat toAll; try All_map; try close_Forall;
  change_Sk; auto with all;
  intuition eauto 4 with all.

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; intros; simpl
  | |- context [nth_error ?l ?n] => elim (nth_error_spec l n); rewrite -> ?app_length, ?map_length;
                                    try lia; intros; simpl
  | H : context[nth_error (?l ++ ?l') ?n] |- _ =>
    (rewrite -> (AstUtils.nth_error_app_ge l l' n) in H by lia) ||
    (rewrite -> (AstUtils.nth_error_app_lt l l' n) in H by lia)
  | H : nth_error ?l ?n = Some _, H' : nth_error ?l ?n' = Some _ |- _ =>
    replace n' with n in H' by lia; rewrite -> H in H'; injection H'; intros; subst
  | _ => lia || congruence || solve [repeat (f_equal; try lia)]
  end.

Lemma lift0_id : forall M k, lift 0 k M = M.
Proof.
  intros M.
  elim M using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try (f_equal; auto; solve_all).

  - now elim (leb k n).
Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
  intros; unfold lift in |- *.
  apply lift0_id; easy.
Qed.

Hint Extern 10 => progress unfold compose : all.

Hint Extern 10 => apply_spec : all.

Hint Resolve -> on_snd_eq_spec : all.

Lemma simpl_lift :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift p i (lift n k M) = lift (p + n) k M.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
      try (rewrite -> H, ?H0, ?H1; auto); try (f_equal; auto; solve_all).

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
    lift p i (lift n k M) = lift n (k + p) (lift p i M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.
Qed.

Lemma permute_lift0 :
  forall M k, lift0 1 (lift 1 k M) = lift 1 (S k) (lift0 1 M).
  intros.
  change (lift 1 0 (lift 1 k M) = lift 1 (1 + k) (lift 1 0 M))
    in |- *.
  rewrite permute_lift; easy.
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

Lemma isLambda_lift n k (bod : term) :
  isLambda bod = true -> isLambda (lift n k bod) = true.
Proof. destruct bod; simpl; try congruence. Qed.

Hint Resolve lift_isApp map_non_nil isLambda_lift : all.

Hint Unfold compose.
Hint Transparent compose.

Lemma simpl_subst_rec :
  forall M N n p k,
    p <= n + k ->
    k <= p -> subst N p (lift (List.length N + n) k M) = lift n k M.
Proof.
  intros M. induction M using term_forall_list_ind;
    intros; simpl;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
      try solve [f_equal; auto; solve_all]; repeat nth_leb_simpl.
Qed.

Lemma simpl_subst :
  forall N M n p, p <= n -> subst N p (lift0 (length N + n) M) = lift0 n M.
Proof. intros. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

Lemma lift_mkApps n k t l : lift n k (mkApps t l) = mkApps (lift n k t) (map (lift n k) l).
Proof.
  revert n k t; induction l; intros n k t. auto.
  simpl. rewrite (IHl n k (tApp t a)). reflexivity.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
    k <= p ->
    lift n k (subst N p M) = subst N (p + n) (lift n k M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - repeat nth_leb_simpl.
    rewrite -> simpl_lift by easy. f_equal; lia.
Qed.

Lemma commut_lift_subst :
  forall M N k, subst N (S k) (lift0 1 M) = lift0 1 (subst N k M).
  now intros; rewrite commut_lift_subst_rec.
Qed.

Lemma distr_lift_subst_rec :
  forall M N n p k,
    lift n (p + k) (subst N p M) =
    subst (List.map (lift n k) N) p (lift n (p + length N + k) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => cbn -[plus]
            end; try easy;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 1. unfold lift at 4.
    repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    revert e0. intros [= <-].
    now rewrite (permute_lift x n0 k p 0).
Qed.

Lemma distr_lift_subst :
  forall M N n k,
    lift n k (subst0 N M) = subst0 (map (lift n k) N) (lift n (length N + k) M).
Proof.
  intros. pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma distr_lift_subst10 :
  forall M N n k,
    lift n k (subst10 N M) = subst10 (lift n k N) (lift n (S k) M).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.

Lemma subst_mkApps u k t l :
  subst u k (mkApps t l) = mkApps (subst u k t) (map (subst u k) l).
Proof.
  revert u k t; induction l; intros u k t; auto.
  intros. simpl mkApps at 1. simpl subst at 1 2.
  now rewrite IHl.
Qed.

Lemma subst1_mkApps u k t l : subst1 u k (mkApps t l) = mkApps (subst1 u k t) (map (subst1 u k) l).
Proof.
  apply subst_mkApps.
Qed.

Lemma distr_subst_rec :
  forall M N (P : list term) n p,
    subst P (p + n) (subst N p M) =
    subst (map (subst P n) N) p (subst P (p + length N + n) M).
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; match goal with
              |- context [tRel _] => idtac
            | |- _ => simpl
            end; try easy;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - unfold subst at 2.
    repeat nth_leb_simpl.
    erewrite <- simpl_subst. f_equal. rewrite map_length. arith_congr. lia.
    rewrite nth_error_map in e0. rewrite e in e0.
    simpl in e0. injection e0 as <-.
    rewrite commut_lift_subst_rec. arith_congr. lia.
Qed.

Lemma distr_subst :
  forall P N M k,
    subst P k (subst0 N M) = subst0 (map (subst P k) N) (subst P (length N + k) M).
Proof.
  intros.
  pattern k at 1 3 in |- *.
  change k with (0 + k). hnf.
  apply distr_subst_rec.
Qed.

Lemma lift_closed n k t : closedn k t -> lift n k t = t.
Proof.
  revert k.
  elim t using term_forall_list_ind; intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl lift; simpl closed; f_equal; auto; toProp; solve_all]; try easy.
  - rewrite lift_rel_lt; auto.
    revert H. elim (Nat.ltb_spec n0 k); intros; try easy.
Qed.

Lemma closed_upwards {k t} k' : closedn k t -> k' >= k -> closedn k' t.
Proof.
  revert k k'.
  elim t using term_forall_list_ind; intros; try lia;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    simpl closed in *; unfold test_snd, test_def in *;
      try solve [(try f_equal; simpl; repeat (toProp; solve_all); eauto)].

  - elim (ltb_spec n k'); auto. intros.
    apply ltb_lt in H. lia.
Qed.

Lemma subst_empty k a : subst [] k a = a.
Proof.
  induction a in k |- * using term_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; solve_all].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (n - k > 0) by lia.
    assert (exists n', n - k = S n'). exists (pred (n - k)). lia.
    destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
Qed.

(* Lemma lift_to_extended_list_k Γ k : forall k', *)
(*  to_extended_list_k Γ (k' + k) = map (lift0 k') (to_extended_list_k Γ k). *)
(* Proof. *)
(*   unfold to_extended_list_k. *)
(*   intros k'. rewrite !reln_alt_eq, !app_nil_r. *)
(*   induction Γ in k, k' |- *; simpl; auto. *)
(*   destruct a as [na [body|] ty]. *)
(*   now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'). *)
(*   simpl. now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'), map_app. *)
(* Qed. *)

Lemma simpl_subst_k (N : list term) (M : term) :
  forall k p, p = #|N| -> subst N k (lift p k M) = M.
Proof.
  intros. subst p. rewrite <- (Nat.add_0_r #|N|).
  rewrite -> simpl_subst_rec, lift0_id; auto.
Qed.

Lemma subst_app_decomp l l' k t :
  subst (l ++ l') k t = subst l' k (subst (List.map (lift0 (length l')) l) k t).
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
         eauto; solve_all).

  - repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0; intros <-.
    rewrite -> permute_lift by auto.
    rewrite <- (Nat.add_0_r #|l'|).
    rewrite -> simpl_subst_rec, lift0_id; auto with wf; try lia.
Qed.

Lemma subst_app_simpl l l' k t :
  subst (l ++ l') k t = subst l k (subst l' (k + length l) t).
Proof.
  induction t in k |- * using term_forall_list_ind; simpl; eauto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
         eauto; solve_all; eauto).

  - repeat nth_leb_simpl.
    rewrite -> Nat.add_comm, simpl_subst; eauto.
Qed.

Lemma isLambda_subst (s : list term) k (bod : term) :
  isLambda bod = true -> isLambda (subst s k bod) = true.
Proof.
  intros. destruct bod; try discriminate. reflexivity.
Qed.
