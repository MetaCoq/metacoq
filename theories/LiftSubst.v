(* Distributed under the terms of the MIT license.   *)

Require Import List Program.
Require Import Template.Template Template.Ast.
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
    let mfix' := List.map (map_def (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.


Notation lift0 n := (lift n 0).
Definition up := lift 1 0.

Fixpoint subst t k u :=
  match u with
  | tRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Datatypes.Gt => tRel n
    | Datatypes.Lt => tRel (pred n)
    end
  | tEvar ev args => tEvar ev (List.map (subst t k) args)
  | tLambda na T M => tLambda na (subst t k T) (subst t (S k) M)
  | tApp u v => tApp (subst t k u) (List.map (subst t k) v)
  | tProd na A B => tProd na (subst t k A) (subst t (S k) B)
  | tCast c kind ty => tCast (subst t k c) kind (subst t k ty)
  | tLetIn na b ty b' => tLetIn na (subst t k b) (subst t k ty) (subst t (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst t k)) brs in
    tCase ind (subst t k p) (subst t k c) brs'
  | tProj p c => tProj p (subst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst t k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation subst0 t := (subst t 0).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity).

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)]*)
Definition substl l t :=
  List.fold_left (fun t u => subst0 u t) l t.

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
    List.forallb (test_def (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k')) mfix
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

Ltac localeasy := easy0 || solve [eauto 7 with core arith terms].
Local Ltac easy := localeasy.
Local Tactic Notation "now" tactic(t) := t; easy.

Notation lift_rec n c k := (lift n k c) (only parsing).
Notation subst_rec N M k := (subst N k M) (only parsing).

Require Import PeanoNat.
Import Nat.

Lemma lift_rel_ge :
  forall k n p, p <= n -> lift_rec k (tRel n) p = tRel (k + n).
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma lift_rel_lt : forall k n p, p > n -> lift_rec k (tRel n) p = tRel n.
Proof.
  intros; simpl in |- *.
  now elim (leb_spec p n).
Qed.

Lemma subst_rel_lt : forall u n k, k > n -> subst_rec u (tRel n) k = tRel n.
Proof.
  simpl in |- *; intros.
  elim (compare_spec k n); intro Hcomp; easy.
Qed.

Lemma subst_rel_gt :
  forall u n k, n > k -> subst_rec u (tRel n) k = tRel (pred n).
Proof.
  simpl in |- *; intros.
  now elim (compare_spec k n). 
Qed.

Lemma subst_rel_eq : forall u n, subst_rec u (tRel n) n = lift0 n u.
Proof.
  intros; simpl in |- *.
  now elim (compare_spec n n).
Qed.

Lemma lift_rec0 : forall M k, lift_rec 0 M k = M.
Proof.
  intros M.
  elim M using term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy).

  - now elim (leb k n).
  - f_equal. rewrite <- map_id. now eapply (forall_map_spec H).
  - f_equal. auto. rewrite <- map_id. now eapply (forall_map_spec H0).
  - f_equal; auto. rewrite <- map_id. eapply (forall_map_spec H1).
    intros. destruct x; unfold on_snd. simpl. rewrite H2. reflexivity.

  - f_equal. transitivity (map (map_def id) m). eapply (tfix_map_spec H); auto.
    rewrite <- map_id. f_equal. extensionality x. destruct x; reflexivity.
  - f_equal. transitivity (map (map_def id) m). eapply (tfix_map_spec H); auto.
    rewrite <- map_id. f_equal. extensionality x. destruct x; reflexivity.
Qed.

Lemma lift0_p : forall M, lift0 0 M = M.
  intros; unfold lift in |- *.
  apply lift_rec0; easy.
Qed.


Lemma simpl_lift_rec :
  forall M n k p i,
    i <= k + n ->
    k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
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

Lemma simpl_lift : forall M n, lift0 (S n) M = lift0 1 (lift0 n M).
  now intros; rewrite simpl_lift_rec.
Qed.

Lemma permute_lift_rec :
  forall M n k p i,
    i <= k ->
    lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
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

Lemma permute_lift :
  forall M k, lift0 1 (lift_rec 1 M k) = lift_rec 1 (lift0 1 M) (S k).
  intros.
  change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
    in |- *.
  apply permute_lift_rec; easy.
Qed.

Lemma simpl_subst_rec :
  forall M N n p k,
    p <= n + k ->
    k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k.
Proof.
  intros M.
  elim M using term_forall_list_ind;
    intros; simpl; try easy;
      rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
      try solve [f_equal; easy];
      try (f_equal; try easy; apply_spec); intros;
        try rewrite ?map_length; try easy ||
      (try rewrite H, H0; f_equal; try easy; now f_equal).
  
  - elim (leb_spec k n); intros; try easy.
    + rewrite subst_rel_gt; try easy.
    + rewrite subst_rel_lt; try easy.
Qed.

Lemma simpl_subst :
  forall N M n p, p <= n -> subst_rec N (lift0 (S n) M) p = lift0 n M.
  intros; now apply simpl_subst_rec.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
    k <= p ->
    lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
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
  
  - elim (compare_spec p n); elim (leb_spec k n); intros; subst; try easy.
    + rewrite subst_rel_eq; try easy.
      now rewrite simpl_lift_rec.
    + rewrite subst_rel_gt; try easy.
      now rewrite lift_rel_ge.
    + rewrite lift_rel_ge; try easy.
      now rewrite subst_rel_lt.
    + rewrite lift_rel_lt; try easy.
      now rewrite subst_rel_lt.
Qed.

Lemma commut_lift_subst :
  forall M N k, subst_rec N (lift0 1 M) (S k) = lift0 1 (subst_rec N M k).
  now intros; rewrite commut_lift_subst_rec.
Qed.


Lemma distr_lift_subst_rec :
  forall M N n p k,
    lift_rec n (subst_rec N M p) (p + k) =
    subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
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
  
  - unfold subst at 1. unfold lift at 4.
    elim (compare_spec p n); intros; try easy;
    elim (leb_spec (S (p + k)) n); intros; subst; try easy.
    
    + rewrite subst_rel_eq. now rewrite <- permute_lift_rec. 
    + rewrite lift_rel_ge; try easy.
      now rewrite subst_rel_gt.
    + rewrite lift_rel_lt; try easy.
      now rewrite subst_rel_gt.
    + rewrite lift_rel_lt; try easy.
      now rewrite subst_rel_lt.

  - rewrite add_assoc, H0. f_equal. now f_equal.
  - rewrite add_assoc, H0. f_equal. now f_equal.
Qed.

Lemma distr_lift_subst :
  forall M N n k,
    lift_rec n (subst0 N M) k = subst0 (lift_rec n N k) (lift_rec n M (S k)).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); try easy.
  apply distr_lift_subst_rec.
Qed.


Lemma distr_subst_rec :
  forall M N (P : term) n p,
    subst_rec P (subst_rec N M p) (p + n) =
    subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p.
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
  
  - unfold subst at 2. 
    elim (compare_spec p n); intros; try easy.
    
    + subst. rewrite subst_rel_lt; try easy.
      rewrite subst_rel_eq; try easy.
      now rewrite <- commut_lift_subst_rec.
    + unfold subst at 4.
      elim (compare_spec (S (p + n0)) n); intros; subst; try easy.
      ++ rewrite subst_rel_eq.
         now rewrite simpl_subst_rec.
      ++ rewrite !subst_rel_gt; try easy.
      ++ rewrite subst_rel_lt; try easy.
         now rewrite subst_rel_gt.
    + rewrite !subst_rel_lt; try easy.

  - rewrite add_assoc, H0. f_equal. now f_equal.
  - rewrite add_assoc, H0. f_equal. now f_equal.
Qed.

Lemma distr_subst :
  forall (P : term) N M k,
    subst_rec P (subst0 N M) k = subst0 (subst_rec P N k) (subst_rec P M (S k)).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  change k with (0 + k).
  apply distr_subst_rec.
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
    transitivity (map (map_def id) m). apply_spec; eauto.
    now autorewrite with core.
  - simpl lift. f_equal.
    transitivity (map (map_def id) m). apply_spec; eauto.
    now autorewrite with core.
Qed.
