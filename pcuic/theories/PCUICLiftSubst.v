(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction.
From Coq Require Import BinPos Arith.Compare_dec Bool Lia.
Require Import PeanoNat.
Import Nat.
Require Import ssreflect.

(** * Lifting and substitution for the AST

  Along with standard commutation lemmas.
  Definition of [closedn] (boolean) predicate for checking if
  a term is closed. *)

Set Asymmetric Patterns.

(** Shift a renaming [f] by [k]. *)
Definition shiftn k f :=
  fun n => if Nat.ltb n k then n else k + (f (n - k)).

Fixpoint rename f t : term :=
  match t with
  | tRel i => tRel (f i)
  | tEvar ev args => tEvar ev (List.map (rename f) args)
  | tLambda na T M => tLambda na (rename f T) (rename (shiftn 1 f) M)
  | tApp u v => tApp (rename f u) (rename f v)
  | tProd na A B => tProd na (rename f A) (rename (shiftn 1 f) B)
  | tLetIn na b t b' => tLetIn na (rename f b) (rename f t) (rename (shiftn 1 f) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (rename f)) brs in
    tCase ind (rename f p) (rename f c) brs'
  | tProj p c => tProj p (rename f c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
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
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst s k)) brs in
    tCase ind (subst s k p) (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
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
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && closedn k v
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
  elim (leb_spec n (n + i)). intros. assert (n + i - n = i) by lia. rewrite H1 H.
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
Hint Resolve -> on_snd_eq_spec : all.

Lemma map_def_eq_spec {A B : Set} (f f' g g' : A -> B) (x : def A) :
  f (dtype x) = g (dtype x) ->
  f' (dbody x) = g' (dbody x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec {A : Set} (f f' : A -> A) (x : def A) :
  f (dtype x) = (dtype x) ->
  f' (dbody x) = (dbody x) ->
  map_def f f' x = x.
Proof.
  intros. rewrite (map_def_eq_spec _ _ id id); auto. destruct x; auto.
Qed.
Hint Resolve map_def_id_spec : all.

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
  repeat toAll; try All_map; try close_All;
  change_Sk; auto with all;
  intuition eauto 4 with all.

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; intros; simpl
  | |- context [nth_error ?l ?n] => elim (nth_error_spec l n); rewrite -> ?app_length, ?map_length;
                                    try lia; intros; simpl
  | H : context[nth_error (?l ++ ?l') ?n] |- _ =>
    (rewrite -> (nth_error_app_ge l l' n) in H by lia) ||
    (rewrite -> (nth_error_app_lt l l' n) in H by lia)
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
Proof.  intros. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

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
    elim (leb_spec p n); intros; try easy.
    + destruct (nth_error_spec N (n - p)).
      ++ rewrite -> subst_rel_lt by lia.
         erewrite subst_rel_eq; try easy.
         2:rewrite -> nth_error_map, e; reflexivity.
         now rewrite commut_lift_subst_rec. lia.
      ++ unfold subst at 4.
         elim (leb_spec (p + length N + n0) n); intros; subst; try easy.
         destruct (nth_error_spec P (n - (p + length N + n0))).
         +++ erewrite subst_rel_eq. 2:eauto. 2:lia.
             assert (p + length N + n0 = length (map (subst P n0) N) + (p + n0))
               by (rewrite map_length; lia).
             rewrite H1. rewrite simpl_subst_rec; eauto; try lia.
         +++ rewrite !subst_rel_gt; rewrite ?map_length; try lia. f_equal; lia.
         +++ rewrite subst_rel_lt; try easy.
             rewrite -> subst_rel_gt; rewrite map_length. trivial. lia.
    + rewrite !subst_rel_lt; try easy.
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
  - simpl lift. f_equal. solve_all. unfold test_def in b. toProp. solve_all.
  - simpl lift. f_equal. solve_all. unfold test_def in b. toProp. solve_all.
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

Lemma lift_to_extended_list_k Γ k : forall k',
    to_extended_list_k Γ (k' + k) = map (lift0 k') (to_extended_list_k Γ k).
Proof.
  unfold to_extended_list_k.
  intros k'. rewrite !reln_alt_eq !app_nil_r.
  induction Γ in k, k' |- *; simpl; auto.
  destruct a as [na [body|] ty].
  now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k').
  simpl. now rewrite <- Nat.add_assoc, (IHΓ (k + 1) k'), map_app.
Qed.

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

Lemma map_vass_map_def g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (lift n k) g) l)) =
  (mapi (fun i d => map_decl (lift n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite -> permute_lift. f_equal; lia. lia.
Qed.

Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

Lemma shiftn_ext n f f' : (forall i, f i = f' i) -> forall t, shiftn n f t = shiftn n f' t.
Proof.
  intros.
  unfold shiftn. destruct Nat.ltb; congruence.
Qed.

Lemma rename_ext f f' : (forall i, f i = f' i) -> (forall t, rename f t = rename f' t).
Proof.
  intros. revert f f' H.
  elim t0 using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].
  - f_equal; auto. apply H0. intros.
    now apply shiftn_ext.
  - f_equal; auto. now apply H0, shiftn_ext.
  - f_equal; auto. now apply H1, shiftn_ext.
  - f_equal; auto. red in X. solve_all.
    eapply map_def_eq_spec; auto. now apply b, shiftn_ext.
  - f_equal; auto. red in X. solve_all.
    eapply map_def_eq_spec; auto. now apply b, shiftn_ext.
Qed.

Definition lift_renaming n k :=
  fun i =>
    if Nat.leb k i then (* Lifted *) n + i
    else i.

Lemma shiftn_lift_renaming n m k : forall i, shiftn m (lift_renaming n k) i = lift_renaming n (m + k) i.
Proof.
  unfold lift_renaming, shiftn. intros i.
  destruct (ltb_spec i m).
  destruct (ltb_spec (m + k) i). lia.
  destruct (leb_spec (m + k) i). lia. lia.
  destruct (leb_spec (m + k) i).
  destruct (leb_spec k (i - m)). lia. lia.
  destruct (leb_spec k (i - m)). lia. lia.
Qed.

Lemma lift_rename n k t : lift n k t = rename (lift_renaming n k) t.
Proof.
  revert n k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - unfold lift_renaming.
    elim (leb_spec k n); reflexivity.

  - f_equal; eauto.
    rewrite H0. eapply rename_ext. intros i. now rewrite shiftn_lift_renaming.
  - f_equal; eauto.
    rewrite H0. eapply rename_ext. intros i. now rewrite shiftn_lift_renaming.
  - f_equal; eauto.
    rewrite H1. eapply rename_ext. intros i. now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all. apply map_def_eq_spec; auto.
    rewrite b. apply rename_ext => i; now rewrite shiftn_lift_renaming.
  - f_equal; auto.
    red in X. solve_all. apply map_def_eq_spec; auto.
    rewrite b. apply rename_ext => i; now rewrite shiftn_lift_renaming.
Qed.

Definition up k (s : nat -> term) :=
  fun i =>
    if k <=? i then rename (add k) (s (i - k))
    else tRel i.


Require Import Morphisms.

Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 90).

Lemma shiftn_compose n f f' : shiftn n f ∘ shiftn n f' =1 shiftn n (f ∘ f').
Proof.
  unfold shiftn. intros x.
  elim (Nat.ltb_spec x n) => H.
  - now rewrite (proj2 (Nat.ltb_lt x n)).
  - destruct (Nat.ltb_spec (n + f' (x - n)) n).
    lia.
    assert (n + f' (x - n) - n = f' (x - n)) as ->. lia.
    reflexivity.
Qed.

Lemma rename_compose f f' : rename f ∘ rename f' =1 rename (f ∘ f').
Proof.
  intros x.
  induction x in f, f' |- * using term_forall_list_ind; simpl; f_equal; auto; solve_all.

  - rewrite map_map_compose. apply All_map_eq. solve_all.
  - rewrite IHx2. apply rename_ext, shiftn_compose.
  - rewrite IHx2. apply rename_ext, shiftn_compose.
  - rewrite IHx3. apply rename_ext, shiftn_compose.
  - rewrite map_map_compose; apply All_map_eq. solve_all.
    unfold compose; rewrite on_snd_on_snd.
    apply on_snd_eq_spec, H.
  - rewrite map_map_compose; apply All_map_eq. solve_all.
    unfold compose; rewrite map_def_map_def map_length.
    apply map_def_eq_spec; auto.
    rewrite b. apply rename_ext, shiftn_compose.
  - rewrite map_map_compose; apply All_map_eq. solve_all.
    unfold compose; rewrite map_def_map_def map_length.
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
    + edestruct (Nat.leb_spec k' (x - k)). lia.
      simpl. f_equal. lia.
  - elim (Nat.leb_spec (k + k') x) => H'; try f_equal; lia.
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
    let brs' := List.map (on_snd (inst s)) brs in
    tCase ind (inst s p) (inst s c) brs'
  | tProj p c => tProj p (inst s c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (inst s) (inst (up (List.length mfix) s))) mfix in
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
    try solve [f_equal; solve_all].
  - f_equal; eauto. apply H0. now apply up_ext.
  - f_equal; eauto. now apply H0, up_ext.
  - f_equal; eauto. now apply H1, up_ext.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; auto. now apply b, up_ext.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; auto. now apply b, up_ext.
Qed.

Definition ren (f : nat -> nat) : nat -> term :=
  fun i => tRel (f i).

Lemma ren_shiftn n f : up n (ren f) =1 ren (shiftn n f).
Proof.
  unfold ren, up, shiftn.
  intros i.
  elim (Nat.ltb_spec i n) => H; elim (Nat.leb_spec n i) => H'; try lia; trivial.
Qed.

Instance proper_inst : Proper (`=1` ==> Logic.eq ==> Logic.eq) inst.
Proof.
  intros f f' Hff' t t' ->. now apply inst_ext.
Qed.

Instance proper_ext_eq {A B} : Proper (`=1` ==> `=1` ==> iff) (@pointwise_relation A _ (@Logic.eq B)).
Proof.
  intros f f' Hff' g g' Hgg'. split; intros.
  - intros x. now rewrite <- Hff', <- Hgg'.
  - intros x. now rewrite Hff' Hgg'.
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
  - f_equal; eauto. solve_all. apply map_def_eq_spec; auto.
    now rewrite b ren_shiftn.
  - f_equal; eauto. solve_all. apply map_def_eq_spec; auto.
    now rewrite b ren_shiftn.
Qed.

Hint Rewrite @rename_inst : sigma.

Instance rename_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) rename.
Proof. intros f f' Hff' t t' ->. now apply rename_ext. Qed.

(** Show the σ-calculus equations.

    Additional combinators: [idsn n] for n-identity, [consn] for consing a parallel substitution.
 *)

Delimit Scope sigma_scope with sigma.
Local Open Scope sigma_scope.

Definition substitution := nat -> term.
Bind Scope sigma_scope with substitution.

Notation "t '.[' σ ]" := (inst σ t) (at level 6, format "t .[ σ ]") : sigma_scope.

Definition subst_cons (t : term) (f : nat -> term) :=
  fun i =>
    match i with
    | 0 => t
    | S n => f n
    end.

Notation " t ⋅ s " := (subst_cons t s) (at level 90) : sigma_scope.

Instance subst_cons_proper : Proper (Logic.eq ==> `=1` ==> `=1`) subst_cons.
Proof. intros x y -> f f' Hff'. intros i. destruct i; simpl; trivial. Qed.

Definition shift : nat -> term := tRel ∘ S.
Notation "↑" := shift : sigma_scope.

Definition subst_compose (σ τ : nat -> term) :=
  fun i => (σ i).[τ].

Infix "∘" := subst_compose : sigma_scope.

Instance subst_compose_proper : Proper (`=1` ==> `=1` ==> `=1`) subst_compose.
Proof.
  intros f f' Hff' g g' Hgg'. intros x. unfold subst_compose.
  now rewrite Hgg' Hff'.
Qed.

Definition Up σ : substitution := tRel 0 ⋅ (σ ∘ ↑).
Notation "⇑ s" := (Up s) (at level 20).

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
  - red in H. depelim H. reflexivity.
    depelim H.
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
  elim (Nat.ltb_spec i n) => H. reflexivity.
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

Lemma compose_ids_r σ : σ ∘ ids =1 σ.
Proof.
  unfold subst_compose. intros i; apply subst_ids.
Qed.

Lemma compose_ids_l σ : ids ∘ σ =1 σ.
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

Lemma subst_consn_subst_cons t l σ : (t :: l) ⋅n σ =1 (t ⋅ subst_consn l σ).
Proof.
  intros i. unfold subst_consn. induction i; simpl; trivial.
Qed.

Lemma subst_consn_tip t σ : [t] ⋅n σ =1 (t ⋅ σ).
Proof. now rewrite subst_consn_subst_cons subst_consn_nil. Qed.

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

Definition Upn n σ := idsn n ⋅n (σ ∘ ↑^n).
Notation "⇑^ n σ" := (Upn n σ) (at level 30, n at level 2, format "⇑^ n  σ") : sigma_scope.

Lemma Upn_eq n σ : Upn n σ = idsn n ⋅n (σ ∘ ↑^n).
Proof. reflexivity. Qed.

Lemma Upn_proper : Proper (Logic.eq ==> `=1` ==> `=1`) Upn.
Proof. intros ? ? -> f g Hfg. unfold Upn. now rewrite Hfg. Qed.

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
    intros H. destruct i; depelim H. simpl.
    unfold subst_consn.
    now rewrite (proj2 (nth_error_None l #|l|)).
    simpl. now apply IHl.
Qed.

Lemma subst_consn_lt {A} {l : list A} {i} :
  i < #|l| ->
  { x : _ & (List.nth_error l i = Some x) /\ (forall σ, (l ⋅n σ) i = x) }%type.
Proof.
  induction l in i |- *; simpl.
  - intros H; elimtype False; depelim H.
  - intros H.
    destruct i. simpl. exists a. split; auto.
    specialize (IHl i). forward IHl. now depelim H. destruct IHl as [x [Hnth Hsubst_cons]].
    exists x. simpl. split; auto.
Qed.

Lemma idsn_length n : #|idsn n| = n.
Proof.
  induction n; simpl; auto. rewrite app_length IHn; simpl; lia.
Qed.

Lemma idsn_lt {n i} : i < n -> nth_error (idsn n) i = Some (tRel i).
Proof.
  induction n in i |- *; simpl; auto.
  - intros H; depelim H.
  - intros H. depelim H.
    -- by rewrite nth_error_app_ge idsn_length ?Nat.sub_diag.
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

(** Simplify away iterated up's *)
Hint Rewrite @up_Upn : sigma.

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

Lemma inst_fix {mfix idx σ} : (tFix mfix idx).[σ] =
                              tFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec. reflexivity.
  now rewrite up_Upn.
Qed.

Lemma inst_cofix {mfix idx σ} : (tCoFix mfix idx).[σ] =
                                tCoFix (map (map_def (inst σ) (inst (⇑^#|mfix| σ))) mfix) idx.
Proof.
  simpl. f_equal. apply map_ext. intros x. apply map_def_eq_spec. reflexivity.
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

Lemma subst_cons_0 t σ : (tRel 0).[t ⋅ σ] = t. Proof. reflexivity. Qed.
Lemma subst_cons_shift t σ : ↑ ∘ (t ⋅ σ) = σ. Proof. reflexivity. Qed.
Hint Rewrite subst_cons_0 subst_cons_shift : sigma.

Lemma shiftk_shift n : ↑^(S n) =1 ↑^n ∘ ↑. Proof. reflexivity. Qed.

Lemma shiftk_shift_l n : ↑^(S n) =1 ↑ ∘ ↑^n.
Proof.
  intros i.
  unfold shiftk. unfold subst_compose, shift.
  simpl. f_equal. lia.
Qed.

Lemma Upn_1_Up σ : ⇑^1 σ =1 ⇑ σ.
Proof.
  unfold Upn.
  intros i. destruct i; auto.
  simpl. rewrite subst_consn_ge. simpl. auto with arith.
  simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.
Hint Rewrite Upn_1_Up : sigma.

Lemma subst_subst_consn s σ τ : (s ⋅ σ) ∘ τ =1 (s.[τ] ⋅ σ ∘ τ).
Proof.
  intros i.
  destruct i. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Hint Rewrite subst_subst_consn : sigma.

Lemma ren_shift : ↑ =1 ren S.
Proof. reflexivity. Qed.

Lemma compose_ren f g : ren f ∘ ren g =1 ren (Basics.compose g f).
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
  - intros H; depelim H.
  - intros H. depelim H.
    -- by rewrite nth_error_app_ge ren_ids_length ?Nat.sub_diag.
    -- rewrite nth_error_app_lt ?ren_ids_length //. apply IHn; lia.
Qed.

Infix "=2" := (Logic.eq ==> (pointwise_relation _ Logic.eq))%signature (at level 80).

Definition compose2 {A B C} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Infix "∘'" := compose2 (at level 90).

Delimit Scope program_scope with prog.

Lemma subst_consn_subst_cons' {A} (t : A) l : subst_consn (t :: l) =2 (subst_cons_gen t ∘ subst_consn l)%prog.
Proof. red.
  intros x y <-. apply subst_consn_subst_cons_gen.
Qed.

Lemma subst_consn_ids_ren n f : (idsn n ⋅n ren f) =1 ren (ren_ids n ⋅n f).
Proof.
  intros i.
  destruct (Nat.leb_spec n i).
  - rewrite subst_consn_ge idsn_length. auto.
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

Lemma ren_shiftk n : ↑^n =1 ren (add n).
Proof. reflexivity. Qed.

(** Specific lemma for the fix/cofix cases where we are subst_cons'ing a list of ids in front
    of the substitution. *)
Lemma ren_subst_consn_comm:
  forall (f : nat -> nat) (σ : nat -> term) (n : nat),
    ren (subst_consn (ren_ids n) (Init.Nat.add n ∘ f)%prog) ∘ subst_consn (idsn n) (σ ∘ ↑^n) =1
    subst_consn (idsn n) (ren f ∘ σ ∘ ↑^n).
Proof.
  intros f σ m i.
  destruct (Nat.leb_spec m i).
  -- unfold ren, compose, subst_compose. simpl.
     rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length. lia.
     rewrite [subst_consn (ren_ids _) _ i]subst_consn_ge ?ren_ids_length. lia.
     rewrite subst_consn_ge ?idsn_length. lia.
     f_equal. f_equal. lia.
  -- assert (Hr:i < #|ren_ids m |) by (rewrite ren_ids_length; lia).
     assert (Hi:i < #|idsn m |) by (rewrite idsn_length; lia).
     destruct (subst_consn_lt Hi) as [x' [Hnth He]].
     rewrite He.
     unfold ren, compose, subst_compose. simpl.
     destruct (subst_consn_lt Hr) as [x'' [Hnth' He']].
     rewrite He'. rewrite (idsn_lt H) in Hnth. injection Hnth as <-.
     rewrite (ren_ids_lt H) in Hnth'. injection Hnth' as <-.
     rewrite He. reflexivity.
Qed.

Lemma rename_inst_assoc t f σ : t.[ren f].[σ] = t.[ren f ∘ σ].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    simpl. rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    unfold Basics.compose. rewrite on_snd_on_snd.
    solve_all.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite compose_map_def map_length. apply map_def_eq_spec; solve_all.
    unfold compose.
    autorewrite with sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext. apply ren_subst_consn_comm.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite compose_map_def map_length. apply map_def_eq_spec; solve_all.
    unfold compose.
    autorewrite with sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext, ren_subst_consn_comm.
Qed.

Lemma inst_rename_assoc_n:
  forall (f : nat -> nat) (σ : nat -> term) (n : nat),
    subst_consn (idsn n) (σ ∘ ↑^n) ∘ ren (subst_consn (ren_ids n) (Init.Nat.add n ∘ f)%prog) =1
    subst_consn (idsn n) (σ ∘ ren f ∘ ↑^n).
Proof.
  intros f σ m. rewrite ren_shiftk.
  intros i.
  destruct (Nat.leb_spec m i).
  -- rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length. lia.
     unfold subst_compose.
     rewrite [subst_consn (idsn _) _ i]subst_consn_ge ?idsn_length. lia.
     rewrite !rename_inst_assoc !compose_ren.
     apply inst_ext. intros i'.
     unfold ren, compose. f_equal. rewrite subst_consn_ge ?ren_ids_length. lia.
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

Lemma inst_rename_assoc t f σ : t.[σ].[ren f] = t.[σ ∘ ren f].
Proof.
  revert f σ.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto. simpl.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H0.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto. autorewrite with sigma.
    unfold Up.
    rewrite ren_shift. rewrite compose_ren subst_cons_ren H1.
    apply inst_ext. intros i. destruct i; auto.
    unfold subst_compose. simpl. now rewrite !rename_inst_assoc !compose_ren.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    unfold Basics.compose. rewrite on_snd_on_snd.
    solve_all.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite compose_map_def map_length. apply map_def_eq_spec; solve_all.
    unfold compose.
    autorewrite with sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext. apply inst_rename_assoc_n.
  - f_equal; auto.
    red in X. rewrite map_map_compose. solve_all.
    rewrite compose_map_def map_length. apply map_def_eq_spec; solve_all.
    unfold compose.
    autorewrite with sigma.
    unfold Upn. rewrite !compose_ren.
    rewrite !subst_consn_ids_ren.
    rewrite b. simpl. apply inst_ext, inst_rename_assoc_n.
Qed.

Lemma rename_subst_compose1 r s s' : ren r ∘ (s ∘ s') =1 ren r ∘ s ∘ s'.
Proof. unfold subst_compose. simpl. intros i. reflexivity. Qed.

Lemma rename_subst_compose2 r s s' : s ∘ (ren r ∘ s') =1 s ∘ ren r ∘ s'.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite rename_inst_assoc. reflexivity.
Qed.

Lemma rename_subst_compose3 r s s' : s ∘ (s' ∘ ren r) =1 s ∘ s' ∘ ren r.
Proof.
  unfold subst_compose. simpl. intros i.
  rewrite inst_rename_assoc. reflexivity.
Qed.

Lemma Up_Up_assoc:
  forall s s' : nat -> term, (⇑ s) ∘ (⇑ s') =1 ⇑ (s ∘ s').
Proof.
  intros s s'.
  unfold Up.
  rewrite ren_shift.
  rewrite subst_subst_consn.
  simpl. apply subst_cons_proper. reflexivity.
  rewrite - rename_subst_compose2.
  rewrite - rename_subst_compose3.
  apply subst_compose_proper; auto. reflexivity.
  reflexivity.
Qed.

Hint Rewrite Up_Up_assoc : sigma.

Lemma up_up_assoc:
  forall (s s' : nat -> term) (n : nat), up n s ∘ up n s' =1 up n (s ∘ s').
Proof.
  intros s s' n i.
  unfold up, subst_compose. simpl.
  destruct (Nat.leb_spec n i).
  rewrite !(rename_inst (add n) (s (i - n))).
  rewrite rename_inst_assoc.
  rewrite !(rename_inst (add n) _).
  rewrite inst_rename_assoc.
  apply inst_ext.
  intros i'. unfold subst_compose.
  unfold ren. simpl.
  destruct (Nat.leb_spec n (n + i')).
  rewrite rename_inst.
  assert (n + i' - n = i') as -> by lia. reflexivity.
  lia.
  simpl.
  destruct (Nat.leb_spec n i). lia. reflexivity.
Qed.

Lemma inst_assoc t s s' : t.[s].[s'] = t.[s ∘ s'].
Proof.
  revert s s'.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - f_equal. rewrite map_map_compose; solve_all.
  - f_equal; auto. autorewrite with sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. autorewrite with sigma.
    now rewrite H0 Up_Up_assoc.
  - f_equal; auto. autorewrite with sigma.
    now rewrite H1 Up_Up_assoc.
  - f_equal; auto. autorewrite with sigma.
    rewrite map_map_compose; solve_all.
    unfold compose; rewrite on_snd_on_snd. solve_all.
  - f_equal; auto. autorewrite with sigma.
    rewrite map_map_compose; solve_all.
    unfold compose; rewrite map_def_map_def.
    apply map_def_eq_spec; auto.
    rewrite b.
    now rewrite map_length up_up_assoc.
  - f_equal; auto. autorewrite with sigma.
    rewrite map_map_compose; solve_all.
    unfold compose; rewrite map_def_map_def.
    apply map_def_eq_spec; auto.
    rewrite b.
    now rewrite map_length up_up_assoc.
Qed.

Hint Rewrite inst_assoc : sigma.

Lemma subst_compose_assoc s s' s'' : (s ∘ s') ∘ s'' =1 s ∘ (s' ∘ s'').
Proof.
  intros i; unfold subst_compose at 1 3 4.
  now rewrite inst_assoc.
Qed.

Hint Rewrite subst_compose_assoc : sigma.

Lemma Upn_0 σ : ⇑^0 σ =1 σ.
Proof.
  unfold Upn. simpl.
  now rewrite subst_consn_nil shiftk_0 compose_ids_r.
Qed.

Lemma Upn_Up σ n : ⇑^(S n) σ =1 ⇑^n ⇑ σ.
Proof.
  intros i. unfold Upn.
  simpl. rewrite subst_consn_app.
  rewrite subst_consn_tip. unfold Up. apply subst_consn_proper; auto.
  rewrite shiftk_shift_l.
  intros i'. unfold subst_cons, subst_compose.
  destruct i'; auto. simpl. unfold shiftk. now rewrite Nat.add_0_r.
  simpl. now rewrite inst_assoc.
Qed.

Lemma Upn_1 σ : ⇑^1 σ =1 ⇑ σ.
Proof. now rewrite Upn_Up Upn_0. Qed.

Lemma subst_cons_0_shift : tRel 0 ⋅ ↑ =1 ids.
Proof. intros i. destruct i; reflexivity. Qed.

Hint Rewrite subst_cons_0_shift : sigma.

Lemma subst_cons_0s_shifts σ : (σ 0) ⋅ (↑ ∘ σ) =1 σ.
Proof.
  intros i. destruct i; auto.
Qed.

Hint Rewrite subst_cons_0s_shifts : sigma.

(* Print Rewrite HintDb sigma. *)

Lemma subst_inst_aux s k t : subst s k t = inst (up k (subst_fn s)) t.
Proof.
  revert s k.
  elim t using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].

  - unfold subst_fn, up.
    elim (leb_spec k n). intros H.
    destruct nth_error eqn:Heq.
    apply lift_rename.
    simpl. eapply nth_error_None in Heq. f_equal. lia.
    reflexivity.

  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H0. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    rewrite H1. apply inst_ext. intros t'; now rewrite (up_up 1 k).
  - f_equal; eauto.
    solve_all; auto. apply map_def_eq_spec; auto.
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

Hint Rewrite shiftk_shift_l shiftk_shift : sigma.
(* Hint Rewrite Upn_eq : sigma. *)

Lemma term_forall_ctx_list_ind :
  forall P : context -> term -> Type,
    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ (s : String.string) (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (p : inductive * nat) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Γ) l -> P Γ (tCase p t t0 l)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat), tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat), tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros. revert Γ t0.
  fix auxt 2.
  move auxt at top.
  destruct t0; match goal with
                 H : _ |- _ => apply H
               end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert brs.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  apply auxt.

  generalize (fix_context mfix). revert mfix.
  fix auxm 1.
  destruct mfix; constructor.
  split. apply auxt. apply auxt. apply auxm.

  generalize (fix_context mfix). revert mfix.
  fix auxm 1.
  destruct mfix; constructor.
  split. apply auxt. apply auxt. apply auxm.
Defined.


Definition lift_decl n k d := (map_decl (lift n k) d).

Definition lift_context n k (Γ : context) : context :=
  fold_context (fun k' => lift n (k' + k)) Γ.


Lemma lift_decl0 k d : map_decl (lift 0 k) d = d.
Proof.
  destruct d; destruct decl_body; unfold map_decl; simpl;
  f_equal; now rewrite ?lift0_id.
Qed.

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context, fold_context.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0 at 2. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  rewrite lift_decl0; f_equal; auto.
Qed.

Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof. apply fold_context_length. Qed.
Hint Rewrite lift_context_length : lift.

Definition lift_context_snoc0 n k Γ d : lift_context n k (d :: Γ) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof. unfold lift_context. now rewrite fold_context_snoc0. Qed.
Hint Rewrite lift_context_snoc0 : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold snoc. apply lift_context_snoc0.
Qed.
Hint Rewrite lift_context_snoc : lift.

Lemma lift_context_alt n k Γ :
  lift_context n k Γ =
  mapi (fun k' d => lift_decl n (Nat.pred #|Γ| - k' + k) d) Γ.
Proof.
  unfold lift_context. apply fold_context_alt.
Qed.

Lemma lift_context_app n k Γ Δ :
  lift_context n k (Γ ,,, Δ) = lift_context n k Γ ,,, lift_context n (#|Γ| + k) Δ.
Proof.
  unfold lift_context, fold_context, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal. lia.
Qed.

Lemma nth_error_lift_context:
  forall (Γ' Γ'' : context) (v : nat),
    v < #|Γ'| -> forall nth k,
    nth_error Γ' v = Some nth ->
    nth_error (lift_context #|Γ''| k Γ') v = Some (lift_decl #|Γ''| (#|Γ'| - S v + k) nth).
Proof.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v; rewrite lift_context_snoc0.
    + simpl. repeat f_equal; try lia. simpl in *. congruence.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

Lemma nth_error_lift_context_eq:
  forall (Γ' Γ'' : context) (v : nat) k,
    nth_error (lift_context #|Γ''| k Γ') v =
    option_map (lift_decl #|Γ''| (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ'; intros.
  - simpl. unfold lift_context, fold_context; simpl. now rewrite nth_error_nil.
  - simpl. destruct v; rewrite lift_context_snoc0.
    + simpl. repeat f_equal; try lia.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.
