Require Import ZArith Zcompare Lia ssrbool.
Require Import MSets.MSetList MSetFacts MSetProperties.
From MetaCoq.Template Require Import MCUtils.
Require Import ssreflect.
From Equations Require Import Equations.

Local Open Scope Z_scope.

Lemma fold_max_In n m l (H : fold_left Z.max l n = m)
  : n = m \/ In m l.
Proof.
  revert n H; induction l; cbn; intros n H.
  intuition.
  apply IHl in H.
  apply or_assoc. destruct H; [left|now right]. lia.
Qed.

Lemma fold_max_le n m l (H : n <= m \/ Exists (Z.le n) l)
  : n <= fold_left Z.max l m.
Proof.
  revert m H; induction l; cbn in *; intros m [H|H].
  assumption. inversion H.
  eapply IHl. left; lia.
  eapply IHl. inversion_clear H.
  left; lia. right; assumption.
Qed.

Lemma fold_max_le' n m l (H : In n (m :: l))
  : n <= fold_left Z.max l m.
Proof.
  apply fold_max_le. destruct H.
  left; lia. right. apply Exists_exists.
  eexists. split. eassumption. reflexivity.
Qed.

Definition eq_max n m k : max n m = k -> n = k \/ m = k.
  intro; lia.
Qed.

Module Nbar.
  (* None is -∞ *)
  Definition t := option Z.
  Definition max (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (Z.max n m)
    | Some n, None => Some n
    | None, Some m => Some m
    | _, _ => None
    end.
  Definition add (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (n + m)
    | _, _ => None
    end.

  Definition sub (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (n - m)
    | _, _ => None
    end.

  Definition S : t -> t := option_map Z.succ.

  Definition le (n m : t) : Prop :=
    match n, m with
    | Some n, Some m => n <= m
    | Some _, None => False
    | None, _ => True
    end.

  Definition lt (n m : t) : Prop :=
    match n, m with
    | Some n, Some m => n < m
    | None, Some _ => True
    | _, None => False
    end.

  Arguments max _ _ : simpl nomatch.
  Arguments sub _ _ : simpl nomatch.
  Arguments add _ _ : simpl nomatch.
  Arguments le _ _ : simpl nomatch.
  Arguments lt _ _ : simpl nomatch.

  Declare Scope nbar_scope.
  Infix "+" := add : nbar_scope.
  Infix "-" := sub : nbar_scope.
  Infix "<=" := le : nbar_scope.
  Infix "<" := lt : nbar_scope.
  Delimit Scope nbar_scope with nbar.
  Bind Scope nbar_scope with t.

  Local Open Scope nbar_scope.

  #[global] Instance le_refl : Reflexive le.
  Proof.
    intro x; destruct x; cbn; reflexivity.
  Defined.

  #[global] Instance le_trans : Transitive le.
  Proof.
    intros [x|] [y|] [z|]; cbn; intuition.
  Defined.

  (* Definition is_finite (n : t) := is_Some n. *)
  (* Definition is_finite_max (n m : t) *)
  (*   : is_finite (max n m) <-> is_finite n \/ is_finite m. *)
  (* Proof. *)
  (*   split. *)
  (*   - destruct n, m; cbn; intros [k e]; try discriminate. *)
  (*     apply some_inj, eq_max in e. *)
  (*     destruct e; [left|right]; eexists; f_equal; eassumption. *)
  (*     left; eexists; reflexivity. *)
  (*     right; eexists; reflexivity. *)
  (*   - intros [H|H]. *)
  (*     destruct H as [n' e]; rewrite e; cbn. *)
  (*     destruct m; eexists; reflexivity. *)
  (*     destruct H as [m' e]; rewrite e; cbn. *)
  (*     destruct n; eexists; reflexivity. *)
  (* Defined. *)
  (* Definition is_finite_add (n m : t) *)
  (*   : is_finite (n + m) <-> is_finite n /\ is_finite m. *)
  (* Proof. *)
  (*   split. *)
  (*   - destruct n, m; cbn; intros [k e]; try discriminate. *)
  (*     split; eexists; reflexivity. *)
  (*   - intros [[n1 e1] [n2 e2]]; rewrite e1, e2. *)
  (*     eexists; reflexivity. *)
  (* Defined. *)

  (* Definition is_pos (n : t) := Some 1 <= n. *)
  (* Definition is_pos_max (n m : t) *)
  (*   : is_pos (max n m) -> is_pos n \/ is_pos m. *)
  (* Proof. *)
  (*   destruct n, m; cbn; intuition. lia. *)
  (* Defined. *)
  (* Definition is_pos_add (n m : t) *)
  (*   : is_pos (n + m) -> is_pos n \/ is_pos m. *)
  (* Proof. *)
  (*   destruct n, m; cbn; intuition. lia. *)
  (* Defined. *)

  (* Definition is_pos_is_finite n : is_pos n -> is_finite n. *)
  (* Proof. *)
  (*   destruct n; cbn; [|intuition]. *)
  (*   destruct n. lia. intros _. eexists; reflexivity. *)
  (* Qed. *)

  Definition add_assoc n m p : n + (m + p) = n + m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite Z.add_assoc.
  Defined.

  Definition add_0_r n : (n + Some 0 = n)%nbar.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite Z.add_0_r.
  Defined.

  Lemma sub_diag n : n - n = match n with None => None | Some _ => Some 0 end.
  Proof. destruct n; simpl. now rewrite Z.sub_diag. auto. Defined.

  Lemma max_None n : max n None = n.
  Proof. destruct n; simpl; auto. Qed.

  Definition max_lub n m p : n <= p -> m <= p -> max n m <= p.
  Proof.
    destruct n, m, p; cbn; intuition lia.
  Defined.

  Definition add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite Z.add_max_distr_r.
  Defined.

  Definition max_le' n m p : p <= n \/ p <= m -> p <= max n m.
  Proof.
    destruct n, m, p; cbn; intuition; lia.
  Defined.

  Definition plus_le_compat_l n m p : n <= m -> p + n <= p + m.
  Proof.
    destruct n, m, p; cbn; intuition.
  Defined.

  Definition plus_le_compat n m p q : n <= m -> p <= q -> n + p <= m + q.
  Proof.
    destruct n, m, p, q; cbn; intuition.
  Defined.

  Definition max_idempotent n : max n n = n.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite Z.max_idempotent.
  Defined.

  Lemma eq_max n m k (H : max n m = k) : n = k \/ m = k.
  Proof.
    destruct n, m; simpl in *.
    destruct (Z.max_spec z z0); intuition congruence.
    all:intuition.
  Qed.

  Lemma fold_max_In n m l (H : fold_left max l n = m)
    : n = m \/ In m l.
  Proof.
    revert n H; induction l; cbn; intros n H.
    intuition.
    apply IHl in H.
    apply or_assoc. destruct H; [left|now right].
    now apply eq_max.
  Qed.

  Lemma fold_max_le n m l (H : n <= m \/ Exists (le n) l)
    : n <= fold_left max l m.
  Proof.
    revert m H; induction l; cbn in *; intros m [H|H].
    assumption. inversion H.
    eapply IHl. left. apply max_le'; now left.
    eapply IHl. inversion_clear H.
    left. apply max_le'; now right.
    right; assumption.
  Qed.

  Lemma fold_max_le' n m l (H : In n (m :: l))
    : n <= fold_left max l m.
  Proof.
    apply fold_max_le. destruct H.
    left; subst; reflexivity.
    right. apply Exists_exists.
    eexists. split. eassumption. reflexivity.
  Qed.

  Lemma le_dec n m : {n <= m} + {~ n <= m}.
  Proof.
    destruct n as [n|], m as [m|]; cbn.
    simpl. destruct (n ?= m) eqn:comp. left.
    destruct (Z.compare_spec n m); subst; auto; try lia. discriminate.
    eapply (proj1 (Z.compare_lt_iff _ _)) in comp. left; lia.
    eapply (proj1 (Z.compare_gt_iff _ _)) in comp. right; lia.
    all: intuition.
  Defined.

  Lemma le_lt_dec n m : ({n <= m} + {m < n})%nbar.
  Proof.
    destruct n as [n|], m as [m|]; cbn.
    simpl. destruct (n ?= m) eqn:comp. left.
    destruct (Z.compare_spec n m); subst; auto; try lia. discriminate.
    eapply (proj1 (Z.compare_lt_iff _ _)) in comp. left; lia.
    eapply (proj1 (Z.compare_gt_iff _ _)) in comp. right; lia.

    all: (right; constructor) || (left; constructor).
  Defined.

  Lemma le_plus_r n m : (0 <= n)%Z -> m <= Some n + m.
  Proof.
    destruct m; cbn; lia.
  Qed.
  
  Lemma le_antisymm {n m} : n <= m -> m <= n -> n = m.
  Proof.
    destruct n, m; cbn; try easy.
  Qed.

End Nbar.

Import Nbar.

Require Import MSetDecide MSetInterface.

Module Type UsualOrderedTypeWithLeibniz.
  Include UsualOrderedType.
  Parameter eq_leibniz : forall x y, eq x y -> x = y.
End UsualOrderedTypeWithLeibniz.

Module WeightedGraph (V : UsualOrderedTypeWithLeibniz) (VSet : MSetList.SWithLeibniz with Module E := V).
  Module VSetFact := WFactsOn V VSet.
  Module VSetProp := WPropertiesOn V VSet.
  Module VSetDecide := WDecide (VSet).
  Ltac sets := VSetDecide.fsetdec.

  Module Edge.
    Definition t := (V.t * Z * V.t)%type.
    Definition eq : t -> t -> Prop := eq.
    Definition eq_equiv : RelationClasses.Equivalence eq := _.

    Definition lt : t -> t -> Prop :=
      fun '(x, n, y) '(x', n', y') => (V.lt x x') \/ (V.eq x x' /\ n < n')
                                   \/ (V.eq x x' /\ n = n' /\ V.lt y y').
    Definition lt_strorder : StrictOrder lt.
      split.
      - intros [[x n] y] H; cbn in H. intuition.
        all: eapply V.lt_strorder; eassumption.
      - intros [[x1 n1] y1] [[x2 n2] y2] [[x3 n3] y3] H1 H2; cbn in *.
        pose proof (StrictOrder_Transitive x1 x2 x3) as T1.
        pose proof (StrictOrder_Transitive y1 y2 y3) as T2.
        pose proof (@eq_trans _ n1 n2 n3) as T3.
        unfold VSet.E.lt in *. unfold V.eq in *.
        destruct H1 as [H1|[[H1 H1']|[H1 [H1' H1'']]]];
          destruct H2 as [H2|[[H2 H2']|[H2 [H2' H2'']]]]; subst; intuition.
    Qed.
    Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
      intros x x' H1 y y' H2. now subst.
    Qed.
    Definition compare : t -> t -> comparison
      := fun '(x, n, y) '(x', n', y') => match V.compare x x' with
                                      | Lt => Lt
                                      | Gt => Gt
                                      | Eq => match Z.compare n n' with
                                             | Lt => Lt
                                             | Gt => Gt
                                             | Eq => V.compare y y'
                                             end
                                      end.
    Definition compare_spec :
      forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
      intros [[x1 n1] y1] [[x2 n2] y2]; cbn.
      pose proof (V.compare_spec x1 x2) as H1.
      destruct (V.compare x1 x2); cbn in *; inversion_clear H1.
      2-3: constructor; intuition.
      subst. pose proof (Z.compare_spec n1 n2) as H2.
      destruct (n1 ?= n2); cbn in *; inversion_clear H2.
      2-3: constructor; intuition.
      subst. pose proof (V.compare_spec y1 y2) as H3.
      destruct (V.compare y1 y2); cbn in *; inversion_clear H3;
        constructor; subst; intuition.
    Defined.

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      unfold eq. decide equality. apply V.eq_dec.
      decide equality. apply Z.eq_dec. apply V.eq_dec.
    Defined.
    Definition eqb : t -> t -> bool := fun x y => match compare x y with
                                          | Eq => true
                                          | _ => false
                                          end.

    Definition eq_leibniz : forall x y, eq x y -> x = y := fun x y eq => eq.
    
  End Edge.
  Module EdgeSet:= MSets.MSetList.MakeWithLeibniz Edge.
  Module EdgeSetFact := WFactsOn Edge EdgeSet.
  Module EdgeSetProp := WPropertiesOn Edge EdgeSet.
  Module EdgeSetDecide := WDecide (EdgeSet).

  Definition t := (VSet.t * EdgeSet.t * V.t)%type.

  Local Definition V (G : t) := fst (fst G).
  Local Definition E (G : t) := snd (fst G).
  Local Definition s (G : t) := snd G.

  Definition e_source : Edge.t -> V.t := fst ∘ fst.
  Definition e_target : Edge.t -> V.t := snd.
  Definition e_weight : Edge.t -> Z := snd ∘ fst.
  Notation "x ..s" := (e_source x) (at level 3, format "x '..s'").
  Notation "x ..t" := (e_target x) (at level 3, format "x '..t'").
  Notation "x ..w" := (e_weight x) (at level 3, format "x '..w'").

  Definition opp_edge (e : Edge.t) : Edge.t :=
    (e..t, - e..w, e..s).

  Definition labelling := V.t -> nat.

  Section graph.
    Context (G : t).

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add e..s (VSet.add e..t (V G)), 
      EdgeSet.add e (E G), (s G)).

    Definition Edges x y := ∑ n, EdgeSet.In (x, n, y) (E G).

    Inductive Paths : V.t -> V.t -> Type :=
    | paths_refl x : Paths x x
    | paths_step x y z : Edges x y -> Paths y z -> Paths x z.

    Arguments paths_step {x y z} e p.

    Fixpoint weight {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => 0
      | paths_step e p => e.π1 + weight p
      end.

    Fixpoint nodes {x y} (p : Paths x y) : VSet.t :=
      match p with
      | paths_refl x => VSet.empty
      | paths_step e p => VSet.add x (nodes p)
      end.

    Fixpoint concat {x y z} (p : Paths x y) : Paths y z -> Paths x z :=
      match p with
      | paths_refl _ => fun q => q
      | paths_step e p => fun q => paths_step e (concat p q)
      end.

    Fixpoint length {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => 0
      | paths_step e p => Z.succ (length p)
      end.

    (* Global Instance Paths_refl : CRelationClasses.Reflexive Paths := paths_refl. *)
    (* Global Instance Paths_trans : CRelationClasses.Transitive Paths := @concat. *)

    Class invariants := mk_invariant
      { edges_vertices : (* E ⊆ V × V *)
         (forall e, EdgeSet.In e (E G) -> VSet.In e..s (V G) /\ VSet.In e..t (V G));
        (* s ∈ V *)
        source_vertex : VSet.In (s G) (V G);
        (* s is a source that is lower than any other node *)
        source_paths : forall x, VSet.In x (V G) -> ∥ ∑ p : Paths (s G) x, ∥ 0 <= weight p ∥ ∥ }.

    Context {HI : invariants}.


    Definition PosPaths x y := exists p : Paths x y, weight p > 0.

    Class acyclic_no_loop
      := Build_acyclic_no_loop : forall x (p : Paths x x), weight p <= 0.

    Definition acyclic_no_loop' := forall x, ~ (PosPaths x x).

    Fact acyclic_no_loop_loop' : acyclic_no_loop <-> acyclic_no_loop'.
    Proof.
      unfold acyclic_no_loop, acyclic_no_loop', PosPaths.
      split.
      - intros H x [p HH]. specialize (H x p). lia.
      - intros H x p. firstorder.
    Qed.

    Definition correct_labelling (l : labelling) :=
      l (s G) = 0%nat /\
      forall e, EdgeSet.In e (E G) -> Z.of_nat (l e..s) + e..w <= Z.of_nat (l e..t).

    Definition leq_vertices n x y := forall l, correct_labelling l -> Z.of_nat (l x) + n <= Z.of_nat (l y).

    Definition DisjointAdd x s s' := VSetProp.Add x s s' /\ ~ VSet.In x s.

    Inductive SimplePaths : VSet.t -> V.t -> V.t -> Type :=
    | spaths_refl s x : SimplePaths s x x
    | spaths_step s s' x y z : DisjointAdd x s s' -> Edges x y
                               -> SimplePaths s y z -> SimplePaths s' x z.

    Arguments spaths_step {s s' x y z} H e p.
    Derive Signature NoConfusion for SimplePaths.

    (* Global Instance SimplePaths_refl s : CRelationClasses.Reflexive (SimplePaths s) *)
    (*   := spaths_refl s. *)

    Fixpoint to_paths {s x y} (p : SimplePaths s x y) : Paths x y :=
      match p with
      | spaths_refl _ x => paths_refl x
      | spaths_step _ e p => paths_step e (to_paths p)
      end.

    Fixpoint sweight {s x y} (p : SimplePaths s x y) :=
      match p with
      | spaths_refl _ _ => 0
      | spaths_step _ e p => e.π1 + sweight p
      end.

    Lemma sweight_weight {s x y} (p : SimplePaths s x y)
      : sweight p = weight (to_paths p).
    Proof.
      induction p; cbn; lia.
    Qed.
  
    Fixpoint is_simple {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => true
      | @paths_step x y z e p => negb (VSet.mem x (nodes p)) && is_simple p
      end.

    Program Definition to_simple : forall {x y} (p : Paths x y),
        is_simple p = true -> SimplePaths (nodes p) x y
      := fix to_simple {x y} p (Hp : is_simple p = true) {struct p} :=
           match
             p in Paths t t0
             return is_simple p = true -> SimplePaths (nodes p) t t0
           with
           | paths_refl x =>
             fun _ => spaths_refl (nodes (paths_refl x)) x
           | @paths_step x y z e p0 =>
             fun Hp0 => spaths_step _ e (to_simple p0 _)
           end Hp.
    Next Obligation.
      split.
      - eapply VSetProp.Add_add.
      - apply andb_andI in Hp0 as [h1 h2].
        apply negb_true_iff in h1. apply VSetFact.not_mem_iff in h1.
        assumption.
    Defined.
    Next Obligation.
      apply andb_andI in Hp0 as [? ?]. auto.
    Defined.


    Lemma weight_concat {x y z} (p : Paths x y) (q : Paths y z)
      : weight (concat p q) = weight p + weight q.
    Proof.
      revert q; induction p; intro q; cbn.
      reflexivity. specialize (IHp q); intuition.
    Qed.

    Lemma DisjointAdd_add1 {s0 s1 s2 x y}
          (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
      : DisjointAdd x (VSet.add y s0) s2.
    Proof.
      split.
      intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
      - apply H2 in Hz. destruct Hz as [Hz|Hz]; [right|].
        now apply VSetFact.add_1.
        apply H1 in Hz. destruct Hz as [Hz|Hz]; [left; assumption|right].
        now apply VSetFact.add_2.
      - apply H2. right; apply H1. now left.
      - apply H2. apply VSet.add_spec in Hz.
        destruct Hz as [Hz|Hz]; [now left|right].
        apply H1. now right.
      - intro Hx. apply VSet.add_spec in Hx.
        destruct Hx as [Hx|Hx].
        subst. apply H2. apply H1. now left.
        now apply H1.
    Qed.

    Lemma DisjointAdd_add2 {s x} (H : ~ VSet.In x s)
      : DisjointAdd x s (VSet.add x s).
    Proof.
      split. apply VSetProp.Add_add.
      assumption.
    Qed.

    Lemma DisjointAdd_add3  {s0 s1 s2 x y}
          (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
      : DisjointAdd y s0 (VSet.add y s0).
    Proof.
      apply DisjointAdd_add2. intro H.
      unfold DisjointAdd in *.
      apply H2. apply H1. now right.
    Qed.


    Fixpoint add_end {s x y} (p : SimplePaths s x y)
      : forall {z} (e : Edges y z) {s'} (Hs : DisjointAdd y s s'), SimplePaths s' x z
      := match p with
         | spaths_refl s x => fun z e s' Hs => spaths_step Hs e (spaths_refl _ _)
         | spaths_step H e p
           => fun z e' s' Hs => spaths_step (DisjointAdd_add1 H Hs) e
                                        (add_end p e' (DisjointAdd_add3 H Hs))
         end.

    Lemma weight_add_end {s x y} (p : SimplePaths s x y) {z e s'} Hs
      : sweight (@add_end s x y p z e s' Hs) = sweight p + e.π1.
    Proof.
      revert z e s' Hs. induction p.
      - intros; cbn; lia.
      - intros; cbn. rewrite IHp; lia.
    Qed.


    Lemma DisjointAdd_remove {s s' x y} (H : DisjointAdd x s s') (H' : x <> y)
      : DisjointAdd x (VSet.remove y s) (VSet.remove y s').
    Proof.
      repeat split. 2: intros [H0|H0].
     - intro H0. apply VSet.remove_spec in H0.
       destruct H0 as [H0 H1].
       pose proof ((H.p1 y0).p1 H0) as H2.
       destruct H2; [now left|right].
       apply VSetFact.remove_2; intuition.
     - subst. apply VSet.remove_spec. split; [|assumption].
       apply H.p1. left; reflexivity.
     - apply VSet.remove_spec in H0; destruct H0 as [H0 H1].
       apply VSet.remove_spec; split; [|assumption].
       apply H.p1. right; assumption.
     - intro H0. apply VSet.remove_spec in H0; destruct H0 as [H0 _].
       apply H; assumption.
    Qed.

   (* Fixpoint split {s x y} (p : SimplePaths s x y) *)
   (*   : SimplePaths (VSet.remove y s) x y * ∑ s', SimplePaths s' y y := *)
   (*    match p with *)
   (*    | spaths_refl s x => (spaths_refl _ x, (VSet.empty; spaths_refl _ x)) *)
   (*    | spaths_step s s' x0 y0 z0 H e p0 *)
   (*      => match V.eq_dec x0 z0 with *)
   (*        | left pp => (eq_rect _ (SimplePaths _ _) (spaths_refl _ _) _ pp, *)
   (*                     (s'; eq_rect _ (fun x => SimplePaths _ x _) *)
   (*                                  (spaths_step H e p0) _ pp)) *)
   (*        | right pp => (spaths_step (DisjointAdd_remove H pp) e (split p0).1, *)
   (*                      (split p0).2) *)
   (*        end *)
   (*    end. *)

    Definition SimplePaths_sub {s s' x y}
      : VSet.Subset s s' -> SimplePaths s x y -> SimplePaths s' x y.
    Proof.
      intros Hs p; revert s' Hs; induction p.
      - constructor.
      - intros s'0 Hs. unshelve econstructor.
        exact (VSet.remove x s'0).
        3: eassumption. 2: eapply IHp.
        + split. apply VSetProp.Add_remove.
          apply Hs, d; intuition.
          now apply VSetProp.FM.remove_1.
        + intros u Hu. apply VSetFact.remove_2.
          intro X. apply d. subst; assumption.
          apply Hs, d; intuition.
    Defined.

    Definition weight_SimplePaths_sub {s s' x y} Hs p
      : sweight (@SimplePaths_sub s s' x y Hs p) = sweight p.
    Proof.
      revert s' Hs; induction p; simpl. reflexivity.
      intros s'0 Hs. now rewrite IHp.
    Qed.

    Lemma DisjointAdd_Subset {x s s'}
      : DisjointAdd x s s' -> VSet.Subset s s'.
    Proof.
      intros [H _] z Hz. apply H; intuition.
    Qed.

    Fixpoint snodes {s x y} (p : SimplePaths s x y) : VSet.t :=
      match p with
      | spaths_refl s x => VSet.empty
      | spaths_step H e p => VSet.add x (snodes p)
      end.

    Definition split {s x y} (p : SimplePaths s x y)
      : forall u, {VSet.In u (snodes p)} + {u = y} -> 
        SimplePaths (VSet.remove u s) x u * SimplePaths s u y.
    Proof.
      induction p; intros u Hu; cbn in *.
      - induction Hu. eapply False_rect, VSet.empty_spec; eassumption.
        subst. split; constructor.
      - induction (V.eq_dec x u) as [Hx|Hx].
        + split. subst; constructor.
          econstructor; try eassumption; subst; eassumption.
        + assert (Hu' : {VSet.In u (snodes p)} + {u = z}). {
            induction Hu as [Hu|Hu].
            apply (VSetFact.add_3 Hx) in Hu. now left.
            now right. }
          specialize (IHp _ Hu'). split.
          * econstructor. 2: eassumption. 2: exact IHp.1.
            now apply DisjointAdd_remove.
          * eapply SimplePaths_sub. 2: exact IHp.2.
            eapply DisjointAdd_Subset; eassumption.
    Defined.

    Lemma weight_split {s x y} (p : SimplePaths s x y) {u Hu}
      : sweight (split p u Hu).1 + sweight (split p u Hu).2 = sweight p.
    Proof.
      induction p.
      - destruct Hu as [Hu|Hu]. simpl in Hu.
        now elimtype False; eapply VSetFact.empty_iff in Hu.
        destruct Hu; reflexivity.
      - simpl. destruct (V.eq_dec x u) as [X|X]; simpl.
        + destruct X; reflexivity.
        + rewrite weight_SimplePaths_sub.
          rewrite <- Z.add_assoc.
          now rewrite IHp.
    Qed.

   (* Fixpoint split {s x y} (p : SimplePaths s x y) *)
   (*   : SimplePaths (VSet.remove y s) x y * SimplePaths s y y := *)
   (*    match p with *)
   (*    | spaths_refl s x => (spaths_refl _ x, spaths_refl _ x) *)
   (*    | spaths_step s s' x0 y0 z0 H e p0 *)
   (*      => match V.eq_dec x0 z0 with *)
   (*        | left pp => (eq_rect _ (SimplePaths _ _) (spaths_refl _ _) _ pp, *)
   (*                     eq_rect _ (fun x => SimplePaths _ x _) (spaths_step H e p0) _ pp) *)
   (*        | right pp => (spaths_step (DisjointAdd_remove H pp) e (split p0).1, *)
   (*                      SimplePaths_sub (DisjointAdd_Subset H) (split p0).2) *)
   (*        end *)
   (*    end. *)

   (*  Lemma weight_split {s x y} (p : SimplePaths s x y) *)
   (*    : sweight (split p).1 + sweight (split p).2 = sweight p. *)
   (*  Proof. *)
   (*    induction p. *)
   (*    - reflexivity. *)
   (*    - simpl. destruct (V.eq_dec x z). *)
   (*      + destruct e0; cbn. reflexivity. *)
   (*      + cbn. rewrite weight_SimplePaths_sub; lia. *)
   (*  Qed. *)

    Definition split' {s x y} (p : SimplePaths s x y)
      : SimplePaths (VSet.remove y s) x y * SimplePaths s y y
      := split p y (right eq_refl).

    Lemma weight_split' {s x y} (p : SimplePaths s x y)
      : sweight (split' p).1 + sweight (split' p).2 = sweight p.
    Proof.
      unfold split'; apply weight_split.
    Defined.    

    Lemma DisjointAdd_union {s s' s'' x} (H : DisjointAdd x s s')
      : ~ VSet.In x s'' -> DisjointAdd x (VSet.union s s'') (VSet.union s' s'').
    Proof.
      destruct H as [hadd hin].
      split.
      now eapply VSetProp.union_Add. sets.
    Qed.

    Lemma DisjointAdd_remove1 {s x} (H : VSet.In x s)
      : DisjointAdd x (VSet.remove x s) s.
    Proof.
      split.
      - intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
        + destruct (V.eq_dec x z). now left.
          right. now apply VSetFact.remove_2.
        + now subst.
        + eapply VSetFact.remove_3; eassumption.
      - now apply VSetFact.remove_1.
    Qed.
      
    Definition spaths_one {s x y k} (Hx : VSet.In x s) (Hk : EdgeSet.In (x, k, y) (E G))
      : SimplePaths s x y.
    Proof.
      econstructor. 3: constructor. now apply DisjointAdd_remove1.
      exists k. assumption.
    Defined.

    Global Instance Add_Proper : Proper (eq ==> VSet.Equal ==> VSet.Equal ==> iff) VSetProp.Add.
    Proof.
      intros x y -> s0 s1 eq s0' s1' eq'.
      unfold VSetProp.Add. now setoid_rewrite eq; setoid_rewrite eq'.
    Qed.

    Global Instance DisjointAdd_Proper : Proper (eq ==> VSet.Equal ==> VSet.Equal ==> iff) DisjointAdd.
    Proof.
      intros x y -> s0 s1 eq s0' s1' eq'.
      unfold DisjointAdd.
      now rewrite eq eq'.
    Qed.

    Lemma Add_In {s x} (H : VSet.In x s)
      : VSetProp.Add x s s.
    Proof.
      split. intuition.
      intros []; try subst; assumption.
    Qed.

    Lemma Add_Add {s s' x} (H : VSetProp.Add x s s')
      : VSetProp.Add x s' s'.
    Proof.
      apply Add_In, H. left; reflexivity.
    Qed.


    Lemma simplify_aux1 {s0 s1 s2} (H : VSet.Equal (VSet.union s0 s1) s2)
      : VSet.Subset s0 s2.
    Proof.
      intros x Hx. apply H.
      now apply VSetFact.union_2.
    Qed.

    Lemma simplify_aux2 {s0 x} (Hx : VSet.mem x s0 = true)
          {s1 s2}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union s0 s1) s2.
    Proof.
      apply VSet.mem_spec in Hx.
      etransitivity; [|eassumption].
      intro y; split; intro Hy; apply VSet.union_spec;
        apply VSet.union_spec in Hy; destruct Hy as [Hy|Hy].
      left; assumption.
      right; now apply VSetFact.add_2.
      left; assumption.
      apply VSet.add_spec in Hy; destruct Hy as [Hy|Hy].
      left; red in Hy; subst; assumption.
      right; assumption.
    Qed.

    Lemma simplify_aux3 {s0 s1 s2 x}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union (VSet.add x s0) s1) s2.
    Proof.
      etransitivity; [|eassumption].
      etransitivity. eapply VSetProp.union_add.
      symmetry. etransitivity. apply VSetProp.union_sym.
      etransitivity. eapply VSetProp.union_add.
      apply VSetFact.add_m. reflexivity.
      apply VSetProp.union_sym.
    Qed.

    Fixpoint simplify {s x y} (q : Paths y x)
      : forall (p : SimplePaths s x y) {s'},
        VSet.Equal (VSet.union s (nodes q)) s' -> ∑ x', SimplePaths s' x' x' :=
      match q with
      | paths_refl x => fun p s' Hs => (x; SimplePaths_sub (simplify_aux1 Hs) p)
      | @paths_step y y' _ e q =>
        fun p s' Hs => match VSet.mem y s as X return VSet.mem y s = X -> _ with
              | true => fun XX => let '(p1, p2) := split' p in
                       if 0 <? sweight p2
                       then (y; SimplePaths_sub (simplify_aux1 Hs) p2)
                       else (simplify q (add_end p1 e
                                          (DisjointAdd_remove1 (VSetFact.mem_2 XX)))
                                      (simplify_aux2 XX Hs))
              | false => fun XX => (simplify q (add_end p e
                            (DisjointAdd_add2 ((VSetFact.not_mem_iff _ _).p2 XX)))
                                         (simplify_aux3 Hs))
              end eq_refl
      end.

    Lemma weight_simplify {s x y} q (p : SimplePaths s x y)
      : forall {s'} Hs, (0 < weight q + sweight p)
        -> 0 < sweight (simplify q p (s':=s') Hs).π2.
    Proof.
      revert s p; induction q.
      - cbn; intros. intuition. now rewrite weight_SimplePaths_sub.
      - intros s p s' Hs H; cbn in H. simpl.
        set (F0 := proj2 (VSetFact.not_mem_iff s x)); clearbody F0.
        set (F1 := @VSetFact.mem_2 s x); clearbody F1.
        set (F2 := @simplify_aux2 s x); clearbody F2.
        destruct (VSet.mem x s).
        + case_eq (split' p); intros p1 p2 Hp.
          case_eq (0 <? sweight p2); intro eq.
          * cbn. apply Z.ltb_lt in eq.
            rewrite weight_SimplePaths_sub; lia.
          * eapply IHq. rewrite weight_add_end.
            pose proof (weight_split' p) as X; rewrite Hp in X; cbn in X.
            apply Z.ltb_ge in eq. rewrite <- X in H. lia.
        + eapply IHq. rewrite weight_add_end. lia.
    Qed.

    Definition succs (x : V.t) : list (Z * V.t)
      := let l := List.filter (fun e => V.eq_dec e..s x) (EdgeSet.elements (E G)) in
         List.map (fun e => (e..w, e..t)) l.

    (* lsp = longest simple path *)
    (* l is the list of authorized intermediate nodes *)
    (* lsp0 (a::l) x y = max (lsp0 l x y) (lsp0 l x a + lsp0 l a y) *)

    Fixpoint lsp00 fuel (s : VSet.t) (x z : V.t) : Nbar.t :=
      let base := if V.eq_dec x z then Some 0 else None in
      match fuel with
      | 0%nat => base
      | Datatypes.S fuel =>
        match VSet.mem x s with
        | true =>
          let ds := List.map
                      (fun '(n, y) => Some n + lsp00 fuel (VSet.remove x s) y z)%nbar
                      (succs x) in
          List.fold_left Nbar.max ds base
        | false => base end
      end.

    Definition lsp0 s := lsp00 (VSet.cardinal s) s.

    Lemma lsp0_eq s x z : lsp0 s x z =
      let base := if V.eq_dec x z then Some 0 else None in
      match VSet.mem x s with
      | true =>
        let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar
                           (succs x) in
        List.fold_left Nbar.max ds base
      | false => base end.
    Proof.
      unfold lsp0. set (fuel := VSet.cardinal s).
      cut (VSet.cardinal s = fuel); [|reflexivity].
      clearbody fuel. revert s x. induction fuel.
      - intros s x H.
        apply VSetProp.cardinal_inv_1 in H.
        specialize (H x). apply VSetProp.FM.not_mem_iff in H.
        rewrite H. reflexivity.
      - intros s x H. simpl.
        case_eq (VSet.mem x s); [|reflexivity].
        intro HH. f_equal. apply List.map_ext.
        intros [n y].
        assert (H': VSet.cardinal (VSet.remove x s) = fuel);
          [|rewrite H'; reflexivity].
        apply VSet.mem_spec, VSetProp.remove_cardinal_1 in HH.
        lia.
    Qed.

    (* Equations lsp0 (s : VSet.t) (x z : V.t) : Nbar.t by wf (VSet.cardinal s) *)
    (*   := *)
    (*   lsp0 s x z := *)
    (*   let base := if V.eq_dec x z then Some 0 else None in *)
    (*   match VSet.mem x s as X return VSet.mem x s = X -> _ with *)
    (*   | true => fun XX => *)
    (*     let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar *)
    (*                        (succs x) in *)
    (*     List.fold_left Nbar.max ds base *)
    (*   | false => fun _ => base end eq_refl. *)
    (* Next Obligation. *)
    (*   apply VSet.mem_spec in XX. *)
    (*   pose proof (VSetProp.remove_cardinal_1 XX). *)
    (*   lia. *)
    (* Defined. *)

    Definition lsp := lsp0 (V G).


    Lemma lsp0_VSet_Equal {s s' x y} :
      VSet.Equal s s' -> lsp0 s x y = lsp0 s' x y.
    Proof.
      intro H; unfold lsp0; rewrite (VSetProp.Equal_cardinal H).
      set (n := VSet.cardinal s'); clearbody n.
      revert x y s s' H. induction n.
      - reflexivity.
      - cbn. intros x y s s' H. erewrite map_ext.
        erewrite VSetFact.mem_m. 2: reflexivity. 2: eassumption.
        reflexivity.
        intros [m z]; cbn. erewrite IHn.
        reflexivity. now eapply VSetFact.remove_m.
    Qed.

    Lemma lsp0_spec_le {s x y} (p : SimplePaths s x y)
      : (Some (sweight p) <= lsp0 s x y)%nbar.
    Proof.
      induction p; rewrite lsp0_eq; simpl.
      - destruct (V.eq_dec x x); [|contradiction].
        destruct (VSet.mem x s0); [|cbn; reflexivity].
        match goal with
        | |- (_ <= fold_left ?F _ _)%nbar =>
          assert (XX: (forall l acc, Some 0 <= acc -> Some 0 <= fold_left F l acc)%nbar);
            [|apply XX; cbn; reflexivity]
        end.
        clear; induction l.
        + cbn; trivial.
        + intros acc H; simpl. apply IHl.
          apply max_le'; now left.
      - assert (ee: VSet.mem x s' = true). {
          apply VSet.mem_spec, d. left; reflexivity. }
        rewrite ee. etransitivity.
        eapply (plus_le_compat (Some e.π1) _ (Some (sweight p))).
        reflexivity. eassumption.
        apply Nbar.fold_max_le'.
        right.
        unfold succs. rewrite map_map_compose.
        apply in_map_iff. exists (x, e.π1, y). simpl.
        split.
        + cbn -[lsp0].
          assert (XX: VSet.Equal (VSet.remove x s') s0). {
            clear -d.
            intro a; split; intro Ha.
            * apply VSet.remove_spec in Ha. pose proof (d.p1 a).
              intuition. now symmetry in H2.
            * apply VSet.remove_spec. split.
              apply d. right; assumption.
              intro H. apply proj2 in d. apply d.
              red in H; subst; assumption. }
          rewrite (lsp0_VSet_Equal XX); reflexivity.
        + apply filter_In. split.
          apply InA_In_eq, EdgeSet.elements_spec1. exact e.π2.
          cbn. destruct (V.eq_dec x x); [reflexivity|contradiction].
    Qed.

    Lemma lsp0_spec_eq {s x y} n
      : lsp0 s x y = Some n -> exists p : SimplePaths s x y, sweight p = n.
    Proof.
      set (c := VSet.cardinal s). assert (e: VSet.cardinal s = c) by reflexivity.
      clearbody c; revert s e x y n.
      induction c using Wf_nat.lt_wf_ind.
      rename H into IH.
      intros s e x y n H.
      rewrite lsp0_eq in H; cbn -[lsp0] in H.
      case_eq (VSet.mem x s); intro Hx; rewrite Hx in H.
      - apply fold_max_In in H. destruct H.
        + destruct (V.eq_dec x y); [|discriminate].
          apply some_inj in H; subst.
          unshelve eexists; constructor.
        + apply in_map_iff in H.
          destruct H as [[x' n'] [H1 H2]].
          case_eq (lsp0 (VSet.remove x s) n' y).
          2: intros ee; rewrite ee in H1; discriminate.
          intros nn ee; rewrite ee in H1.
          eapply IH in ee. 3: reflexivity.
          * destruct ee as [p1 Hp1].
            unfold succs in H2.
            apply in_map_iff in H2.
            destruct H2 as [[[x'' n''] y''] [H2 H2']]; cbn in H2.
            inversion H2; subst; clear H2.
            apply filter_In in H2'; destruct H2' as [H2 H2']; cbn in H2'.
            destruct (V.eq_dec x'' x); [subst|discriminate]; clear H2'.
            unshelve eexists. econstructor.
            3: eassumption.
            -- split. 2: apply VSetFact.remove_1; reflexivity.
               apply VSetProp.Add_remove.
               apply VSet.mem_spec; assumption.
            -- eexists.
               apply (EdgeSet.elements_spec1 _ _).p1, InA_In_eq; eassumption.
            -- cbn. now apply some_inj in H1.
          * subst. clear -Hx. apply VSet.mem_spec in Hx.
            apply VSetProp.remove_cardinal_1 in Hx. lia.
      - destruct (V.eq_dec x y); [|discriminate].
        apply some_inj in H; subst. unshelve eexists; constructor.
    Qed.

    Lemma lsp0_spec_eq0 {s x} n
      : lsp0 s x x = Some n -> 0 <= n.
    Proof.
      intros lspeq.
      generalize (lsp0_spec_le (spaths_refl s x)).
      rewrite lspeq. simpl. auto.
    Qed.

    Lemma correct_labelling_Paths l (Hl : correct_labelling l)
      : forall x y (p : Paths x y), Z.of_nat (l x) + weight p <= Z.of_nat (l y).
    Proof.
      induction p. cbn; lia.
      apply proj2 in Hl.
      specialize (Hl (x, e.π1, y) e.π2). cbn in *; lia.
    Qed.

    Lemma correct_labelling_lsp {x y n} (e : lsp x y = Some n) :
      forall l, correct_labelling l -> Z.of_nat (l x) + n <= Z.of_nat (l y).
    Proof.
      eapply lsp0_spec_eq in e as [p Hp].
      intros l Hl; eapply correct_labelling_Paths with (p:= to_paths p) in Hl.
      now rewrite <- sweight_weight, Hp in Hl.
    Qed.

    Lemma acyclic_labelling l : correct_labelling l -> acyclic_no_loop.
    Proof.
      intros Hl x p.
      specialize (correct_labelling_Paths l Hl x x p); lia.
    Qed.

    Lemma lsp0_triangle_inequality {HG : acyclic_no_loop} s x y1 y2 n
          (He : EdgeSet.In (y1, n, y2) (E G))
          (Hy : VSet.In y1 s)
      : (lsp0 s x y1 + Some n <= lsp0 s x y2)%nbar.
    Proof.
      case_eq (lsp0 s x y1); [|cbn; trivial].
      intros m Hm.
      apply lsp0_spec_eq in Hm.
      destruct Hm as [p Hp].
      case_eq (split' p).
      intros p1 p2 Hp12.
      pose proof (weight_split' p) as H.
      rewrite Hp12 in H; cbn in H.
      etransitivity.
      2: unshelve eapply (lsp0_spec_le (add_end p1 (n; He) _)).
      subst; rewrite weight_add_end; cbn.
      pose proof (sweight_weight p2) as HH.
      red in HG. specialize (HG _ (to_paths p2)). lia.
      now apply DisjointAdd_remove1.
    Qed.

    Definition is_nonpos n := 
      match n with
      | Some z => (z <=? 0)
      | None => false        
      end.

    Lemma is_nonpos_spec n : is_nonpos n <~> ∑ z, n = Some z /\ z <= 0.
    Proof.
      unfold is_nonpos.
      split.
      - destruct n; try intuition congruence.
        intros le. eapply Z.leb_le in le. exists z; intuition eauto.
      - intros [z [-> le]]. now eapply Z.leb_le.
    Qed.

    Lemma is_nonpos_nbar n : is_nonpos n -> (n <= Some 0)%nbar.
    Proof.
      now intros [z [-> le]]%is_nonpos_spec.
    Qed.

    Definition lsp0_sub {s s' x y}
      : VSet.Subset s s' -> (lsp0 s x y <= lsp0 s' x y)%nbar.
    Proof.
      case_eq (lsp0 s x y); [|cbn; trivial].
      intros n Hn Hs.
      apply lsp0_spec_eq in Hn; destruct Hn as [p Hp]; subst.
      rewrite <- (weight_SimplePaths_sub Hs p).
      apply lsp0_spec_le.
    Qed.

    Definition snodes_Subset {s x y} (p : SimplePaths s x y)
      : VSet.Subset (snodes p) s.
    Proof.
      induction p; cbn.
      - apply VSetProp.subset_empty.
      - apply VSetProp.subset_add_3.
        apply d. left; reflexivity.
        etransitivity. eassumption.
        eapply DisjointAdd_Subset; eassumption.
    Qed.

    Definition reduce {s x y} (p : SimplePaths s x y)
      : SimplePaths (snodes p) x y.
    Proof.
      induction p; cbn.
      - constructor.
      - econstructor; try eassumption.
        apply DisjointAdd_add2.
        intro Hx; apply d. eapply snodes_Subset.
        eassumption.
    Defined.


    Definition simplify2 {x z} (p : Paths x z) :  SimplePaths (nodes p) x z.
    Proof.
      induction p; cbn.
      - constructor.
      - case_eq (VSet.mem x (snodes IHp)); intro Hx.
        + apply VSetFact.mem_2 in Hx.
          eapply SimplePaths_sub. 2: exact (split _ _ (left Hx)).2.
          apply VSetProp.subset_add_2; reflexivity.
        + eapply SimplePaths_sub. shelve.
          econstructor. 2: eassumption. 2: exact (reduce IHp).
          eapply DisjointAdd_add2. now apply VSetFact.not_mem_iff.
          Unshelve.
          apply VSetFact.add_s_m. reflexivity.
          apply snodes_Subset.
    Defined.

    Lemma weight_reduce {s x y} (p : SimplePaths s x y)
      : sweight (reduce p) = sweight p.
    Proof.
      induction p; simpl; intuition.
    Qed.

    Opaque split reduce SimplePaths_sub.

    Lemma weight_simplify2 {HG : acyclic_no_loop} {x z} (p : Paths x z)
      : weight p <= sweight (simplify2 p).
    Proof.
      induction p.
      - reflexivity.
      - simpl.
        set (F0 := @VSetFact.mem_2 (snodes (simplify2 p)) x); clearbody F0.
        set (F1 := VSetFact.not_mem_iff (snodes (simplify2 p)) x); clearbody F1.
        destruct (VSet.mem x (snodes (simplify2 p))).
        + rewrite weight_SimplePaths_sub.
          pose proof (@weight_split _ _ _ (simplify2 p))
               x (left (F0 (eq_refl))).
          set (q := split (simplify2 p) x (left (F0 (eq_refl)))) in *.
          destruct q as [q1 q2]; cbn in *.
          assert (sweight q1 + e.π1 <= 0); [|].
          specialize (HG _ (paths_step e (to_paths q1))). cbn in HG.
          rewrite <- sweight_weight in HG. lia.
          transitivity (e.π1 + sweight (simplify2 p)); [|lia]. rewrite <- H. lia.
        + rewrite weight_SimplePaths_sub. cbn.
          rewrite weight_reduce; intuition.
    Qed.

    Lemma nodes_subset {x y} (p : Paths x y)
      : VSet.Subset (nodes p) (V G).
    Proof.
      induction p; cbn.
      apply VSetProp.subset_empty.
      apply VSetProp.subset_add_3; [|assumption].
      apply (edges_vertices _ e.π2).
    Qed.

    Definition simplify2' {x z} (p : Paths x z) :  SimplePaths (V G) x z.
    Proof.
      eapply SimplePaths_sub. 2: exact (simplify2 p).
      apply nodes_subset.
    Defined.

    Lemma weight_simplify2' {HG : acyclic_no_loop} {x z} (p : Paths x z)
      : weight p <= sweight (simplify2' p).
    Proof.
      unfold simplify2'.
      unshelve erewrite weight_SimplePaths_sub.
      eapply weight_simplify2.
    Qed.

    Lemma lsp_s {HG : acyclic_no_loop} x (Hx : VSet.In x (V G))
      : exists n, lsp (s G) x = Some n /\ 0 <= n.
    Proof.
      case_eq (lsp (s G) x).
      - intros n H; eexists; split; [reflexivity|].
        destruct (source_paths _ Hx) as [[p [w]]].
        pose proof (lsp0_spec_le (simplify2' p)).
        unfold lsp in H. rewrite H in H0.
        simpl in H0.
        transitivity (weight p); auto.
        etransitivity; eauto. eapply weight_simplify2'.
      - intro e.
        destruct (source_paths x Hx) as [[p [w]]].
        pose proof (lsp0_spec_le (simplify2' p)) as X.
        unfold lsp in e; rewrite e in X. inversion X.
    Qed.
    
    Lemma SimplePaths_In {s x y} (p : SimplePaths s x y)
    : sweight p <> 0 -> VSet.In x s.
    Proof.
      destruct p. simpl. lia.
      intros _. apply d. left; reflexivity.
    Qed.

    Lemma SimplePaths_In' {s x y} (p : SimplePaths s x y) (H : VSet.In x (V G)) :
      VSet.In y (V G).
    Proof.
      induction p. simpl; auto.
      apply IHp. destruct e.
      now specialize (edges_vertices _ i).
    Qed.

    Lemma Paths_In {x y} : VSet.In y (V G) -> Paths x y -> VSet.In x (V G).
    Proof.
      intros hin p; induction p; auto.
      destruct e as [? ine].
      now eapply edges_vertices in ine.
    Qed.

    Lemma acyclic_lsp0_xx {HG : acyclic_no_loop} s x
      : lsp0 s x x = Some 0.
    Proof.
      pose proof (lsp0_spec_le (spaths_refl s x)) as H; cbn in H.
      case_eq (lsp0 s x x); [|intro e; rewrite e in H; cbn in H; lia].
      intros n Hn.
      pose proof (lsp0_spec_eq0 _ Hn).
      apply lsp0_spec_eq in Hn.
      destruct Hn as [p Hp]. rewrite sweight_weight in Hp.
      red in HG.
      specialize (HG _ (to_paths p)). subst n. f_equal. lia.
    Qed.

    (* We don't care about the default value here: lsp is defined everywhere starting from the source. *)
    Definition to_label (z : option Z) :=
      match z with
      | Some (Zpos p) => Pos.to_nat p
      | _ => 0%nat
      end.

    Lemma Z_of_to_label (z : Z) : 
      Z.of_nat (to_label (Some z)) = if 0 <=? z then z else 0.
    Proof.
      simpl. destruct z; auto. simpl.
      apply Z_of_pos_alt.
    Qed.

    Lemma Z_of_to_label_s {HG : acyclic_no_loop} x : 
      VSet.In x (V G) ->
      exists n, lsp (s G) x = Some n /\ 
        0 <= n /\ (Z.of_nat (to_label (lsp (s G) x))) = n.
    Proof.
      intros inx.
      destruct (lsp_s x inx) as [m [Hm Hpos]].
      rewrite Hm. eexists; split; auto. split; auto.
      rewrite Z_of_to_label.
      eapply Z.leb_le in Hpos. now rewrite Hpos.
    Qed.
    
    Lemma lsp_correctness {HG : acyclic_no_loop} :
        correct_labelling (fun x => to_label (lsp (s G) x)).
    Proof.
      split.
      - unfold lsp. now rewrite acyclic_lsp0_xx.
      - intros [[x n] y] He; cbn.
        simple refine (let H := lsp0_triangle_inequality
                                  (V G) (s G) x y n He _
                       in _); [|clearbody H].
        apply (edges_vertices _ He).
        fold lsp in H. revert H.
        destruct (Z_of_to_label_s x) as [xl [eq [pos ->]]]; rewrite ?eq.
        + apply (edges_vertices _ He).
        + destruct (Z_of_to_label_s y) as [yl [eq' [ylpos ->]]]; rewrite ?eq'.
          * apply (edges_vertices _ He).
          * now simpl.
    Qed.

    Lemma lsp_codistance {HG : acyclic_no_loop} x y z
      : (lsp x y + lsp y z <= lsp x z)%nbar.
    Proof.
      case_eq (lsp x y); [|cbn; trivial]. intros n Hn.
      case_eq (lsp y z); [|cbn; trivial]. intros m Hm.
      destruct (lsp0_spec_eq _ Hn) as [p1 Hp1].
      destruct (lsp0_spec_eq _ Hm) as [p2 Hp2].
      pose proof (lsp0_spec_le (simplify2' (concat (to_paths p1) (to_paths p2))))
        as XX.
      epose proof (weight_simplify2' (concat (to_paths p1) (to_paths p2))).
      unshelve erewrite weight_concat, <- !sweight_weight in H;
        try assumption.
      cbn in H; erewrite Hp1, Hp2 in H.
      simpl. etransitivity; eauto. simpl. eauto.
    Qed.
    
    (* The two largest simple paths between nodes in both directions bound each other. *)
    Lemma lsp_sym {HG : acyclic_no_loop} {x y n} : 
      lsp x y = Some n ->
      (lsp y x <= Some (-n))%nbar.
    Proof.
      intros Hn.        
      destruct (lsp0_spec_eq _ Hn) as [p Hp].
      destruct (lsp y x) eqn:lspyx.
      2:simpl; auto.
      epose proof (lsp0_spec_eq _ lspyx) as [pi Hpi].
      clear Hn lspyx. rewrite -Hp -Hpi /=.
      epose proof (weight_simplify (to_paths pi) p (reflexivity _)).
      destruct simplify as [h loop].
      simpl in H.
      move: (HG _ (to_paths loop)).
      rewrite -sweight_weight.
      rewrite -sweight_weight Hp Hpi in H.
      rewrite Hp Hpi.
      destruct (Z.ltb 0 (z + n)) eqn:ltb.
      eapply Z.ltb_lt in ltb. specialize (H ltb). lia.
      eapply Z.ltb_nlt in ltb.
      intros wl.
      lia.
    Qed.

    Lemma le_Some_lsp {n x y} : (Some n <= lsp x y)%nbar -> 
      ∑ k, lsp x y = Some k /\ n <= k.
    Proof.
      destruct lsp eqn:xy.
      simpl. intros. eexists; split; eauto.
      simpl; now intros [].
    Qed.

    (* There can be no universe lower than the source: all paths to the source have null or 
      negative weight. *)
    Lemma source_bottom {HG : acyclic_no_loop} {x} (p : Paths x (s G)) : weight p <= 0.
    Proof.
      unshelve epose proof (Paths_In _ p).
      eapply source_vertex.
      destruct (lsp_s _ H) as [lx [lsx w]].
      etransitivity; [apply (weight_simplify2' p)|].
      set (sp := simplify2' p).
      epose proof (lsp0_spec_le sp).
      eapply le_Some_lsp in H0 as [xs [lxs wxs]].
      generalize (lsp_codistance x (s G) x).
      rewrite lxs lsx /lsp acyclic_lsp0_xx /=. lia.
    Qed.

    Lemma lsp_to_s {HG : acyclic_no_loop} {x} (Hx : VSet.In x (V G)) {n}
      : lsp x (s G) = Some n -> n <= 0.
    Proof.
      case_eq (lsp x (s G)).
      - intros z H [= <-].
        destruct (lsp0_spec_eq _ H).
        pose proof (source_bottom (to_paths x0)).
        rewrite <- sweight_weight in H1. congruence.
      - intro e. discriminate.
    Qed.

    Lemma lsp_xx_acyclic
      : VSet.For_all (fun x => lsp x x = Some 0) (V G) -> acyclic_no_loop'.
    Proof.
      intros H. intros x [p Hp]. assert (hw: 0 < weight p + sweight ((spaths_refl (V G) x))) by (simpl; lia).
      simple refine (let Hq := weight_simplify p (spaths_refl (V G) _)
                                               _ hw
                     in _).
      + exact (V G).
      + etransitivity. apply VSetProp.union_sym.
        etransitivity. apply VSetProp.union_subset_equal.
        apply nodes_subset. reflexivity.
      + match goal with
        | _ : 0 < sweight ?qq.π2 |- _ => set (q := qq) in *; clearbody Hq
        end.
        destruct q as [x' q]; cbn in Hq.
        assert (Some (sweight q) <= Some 0)%nbar. {
          erewrite <- H. eapply lsp0_spec_le.
          eapply (SimplePaths_In q). lia. }
        cbn in H0; lia.
    Defined.

    Lemma VSet_Forall_reflect P f (Hf : forall x, reflect (P x) (f x)) s
      : reflect (VSet.For_all P s) (VSet.for_all f s).
    Proof.
      apply iff_reflect. etransitivity.
      2: apply VSetFact.for_all_iff.
      2: intros x y []; reflexivity.
      apply iff_forall; intro x.
      apply iff_forall; intro Hx.
      now apply reflect_iff.
    Qed.

    Lemma reflect_logically_equiv {A B} (H : A <-> B) f
      : reflect B f -> reflect A f.
    Proof.
      destruct 1; constructor; intuition.
    Qed.

    Definition is_acyclic := VSet.for_all (fun x => match lsp x x with
                                                 | Some 0 => true
                                                 | _ => false
                                                 end) (V G).


    (** ** Main results about acyclicity *)

    Lemma acyclic_caract1
      : acyclic_no_loop <-> exists l, correct_labelling l.
    Proof.
      split.
      intro HG; eexists. eapply (lsp_correctness).
      intros [l Hl]; eapply acyclic_labelling; eassumption.
    Defined.

    Lemma acyclic_caract2 :
      acyclic_no_loop <-> (VSet.For_all (fun x => lsp x x = Some 0) (V G)).
    Proof.
      split.
      - intros HG x Hx. unshelve eapply acyclic_lsp0_xx.
      - intros H. apply acyclic_no_loop_loop'.
        now eapply lsp_xx_acyclic.
    Defined.

    (* Lemma acyclic_caract3 *)
    (*   : acyclic_no_loop <-> acyclic_well_founded. *)
    (* Proof. *)
    (*   split. *)
    (*   intro. eapply acyclic_labelling. *)
    (*   now eapply lsp_correctness. *)
    (*   apply acyclic_wf_no_loop. *)
    (* Defined. *)

    Lemma is_acyclic_spec : is_acyclic <-> acyclic_no_loop.
    Proof.
      symmetry. etransitivity. eapply acyclic_caract2.
      etransitivity. 2: eapply VSetFact.for_all_iff.
      2: now intros x y [].
      apply iff_forall; intro x.
      apply iff_forall; intro Hx.
      split. now intros ->.
      destruct lsp as [[]|]; try congruence.
    Qed.

    Lemma Zle_opp {n m} : - n <= m <-> - m <= n.
    Proof. lia. Qed.

    Lemma Zle_opp' {n m} : n <= m <-> - m <= - n.
    Proof. lia. Qed.

    Lemma lsp_xx {HG : acyclic_no_loop} {x} : lsp x x = Some 0.
    Proof.
      rewrite /lsp.
      now rewrite acyclic_lsp0_xx.
    Qed.

    Definition edge_paths {e} : EdgeSet.In e (E G) -> Paths e..s e..t.
    Proof.
      intros hin.
      eapply (paths_step (y := e..t)). exists e..w. destruct e as [[s w] t].
      simpl in *. apply hin. constructor.
    Defined.

    Lemma Z_of_to_label_pos x : 0 <= x -> Z.of_nat (to_label (Some x)) = x.
    Proof.
      intros le.
      rewrite Z_of_to_label.
      destruct (Z.leb_spec 0 x); auto. lia.
    Qed.

    Lemma to_label_max x y : (Some 0 <= x)%nbar -> to_label (max x y) = Nat.max (to_label x) (to_label y).
    Proof.
      destruct x; intros H; simpl in H; auto. 2:elim H.
      eapply Nat2Z.inj.
      rewrite Nat2Z.inj_max.
      destruct y; cbn -[to_label].
      rewrite Z_of_to_label_pos; try lia.
      rewrite Z_of_to_label_pos. lia.
      rewrite Z_of_to_label.
      destruct (Z.leb_spec 0 z0); lia.
      rewrite Z_of_to_label_pos; try lia.
      simpl. lia.
    Qed.

    Lemma lsp_from_source {HG : acyclic_no_loop} {x} {n} : lsp (s G) x = Some n -> 0 <= n.
    Proof.
      intros H.
      assert (VSet.In x (V G)).
      destruct (lsp0_spec_eq _ H).
      apply (SimplePaths_In' x0). eapply HI.
      destruct (lsp_s _ H0) as [n' [lspeq w]].
      rewrite H in lspeq. congruence.
    Qed.

    Lemma lsp_to_source {HG : acyclic_no_loop} {x z} : lsp x (s G) = Some z -> z <= 0.
    Proof.
      intros h.
      destruct (lsp0_spec_eq z h).
      pose proof (source_bottom (to_paths x0)).
      rewrite -sweight_weight in H0. lia.
    Qed.

    Lemma lsp_source_max {HG : acyclic_no_loop} {x y} : VSet.In x (V G) -> VSet.In y (V G) ->
       (lsp y x <= lsp (s G) x)%nbar.
    Proof.
      intros inx iny.
      destruct (Z_of_to_label_s x) as [zl [eq [pos zof]]]; eauto.
      rewrite eq. simpl.
      destruct (lsp y x) eqn:yx.
      simpl.
      pose proof (lsp_codistance (s G) y x).
      rewrite eq yx in H. simpl in *.
      destruct (lsp_s y iny) as [ly [lspy neg]].
      rewrite lspy in H. simpl in H. lia.
      now simpl.
    Qed.

    (* Lemma is_acyclic_correct : reflect acyclic_no_loop is_acyclic. *)
    (* Proof. *)
    (*   eapply reflect_logically_equiv. eapply acyclic_caract2. *)
    (*   apply VSet_Forall_reflect; intro x. *)
    (*   destruct (lsp x x). destruct n. constructor; reflexivity. *)
    (*   all: constructor; discriminate. *)
    (* Qed. *)
  End graph.

  Definition add_edges G e :=
    add_edge (add_edge G e) (opp_edge e).
  Arguments sweight {G s x y}.
  Arguments weight {G x y}.

  Module Subgraph1.    
    Section graph2.
    Context (G : t) {HI : invariants G} {HG : acyclic_no_loop G}.
    Context (y_0 x_0 : V.t) (Vx : VSet.In x_0 (V G))
              (Vy : VSet.In y_0 (V G))
              (K : Z) 
              (Hxs : lsp G x_0 y_0 = Some K).

    Local Definition G' : t
      := (V G, EdgeSet.add (y_0, - K, x_0) (E G), s G).

    Definition to_G' {u v} (q : Paths G u v) : Paths G' u v.
    Proof.
      clear -q.
      induction q; [constructor|].
      econstructor. 2: eassumption.
      exists e.π1. cbn. apply EdgeSet.add_spec; right. exact e.π2.
    Defined.

    Lemma to_G'_weight {u v} (p : Paths G u v)
      : weight (to_G' p) = weight p.
    Proof.
      clear.
      induction p. reflexivity.
      simpl. now rewrite IHp.
    Qed.

    Opaque Edge.eq_dec.


    Definition from_G'_path {u v} (q : Paths G' u v)
      : Paths G u v + (Paths G u y_0 * Paths G x_0 v).
    Proof.
      clear -q. induction q.
      - left; constructor.
      - induction (Edge.eq_dec (y_0, -K, x_0) (x, e.π1, y)) as [XX|XX].
        + right. split.
          * rewrite (fst_eq (fst_eq XX)); constructor.
          * destruct IHq as [IHq|IHq].
            -- now rewrite (snd_eq XX).
            -- exact IHq.2.
        + induction IHq as [IHq|IHq].
          * left. econstructor; try eassumption.
            exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
          * right. split.
            -- econstructor; try eassumption.
                2: exact IHq.1.
                exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            -- exact IHq.2.
    Defined.

    Lemma from_G'_path_weight {u v} (q : Paths G' u v)
      : match from_G'_path q with
        | inl q' => weight q = weight q'
        | inr (q1, q2) => 
          weight q <= weight q1 - K + weight q2
        end.
    Proof.
      clear -HI HG Hxs.
      induction q.
      - reflexivity.
      - simpl.
        destruct (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
        + destruct (fst_eq (fst_eq XX)). simpl.
          inversion XX. 
          destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
          * destruct (snd_eq XX); cbn.
            destruct e as [e He]; cbn in *. lia.
          * subst y.
            transitivity (-K + weight q1 - K + weight q2). lia.
            epose proof (lsp0_spec_le G (simplify2' G q1)).
            unfold lsp in Hxs; rewrite Hxs /= in H.
            pose proof (weight_simplify2' G q1). lia.
        + destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
          * lia.
          * lia.
    Qed.

    Definition from_G' {S u v} (q : SimplePaths G' S u v)
      : SimplePaths G S u v + (SimplePaths G S u y_0 * SimplePaths G S x_0 v).
    Proof.
      clear -q. induction q.
      - left; constructor.
      - induction (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX].
        + right. split.
          * rewrite (fst_eq (fst_eq XX)); constructor.
          * eapply SimplePaths_sub.
            eapply DisjointAdd_Subset; eassumption.
            induction IHq as [IHq|IHq].
            -- now rewrite (snd_eq XX).
            -- exact IHq.2.
        + induction IHq as [IHq|IHq].
          * left. econstructor; try eassumption.
            exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
          * right. split.
            -- econstructor; try eassumption.
                2: exact IHq.1.
                exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            -- eapply SimplePaths_sub; [|exact IHq.2].
                eapply DisjointAdd_Subset; eassumption.
    Defined.

    Lemma from_G'_weight {S u v} (q : SimplePaths G' S u v)
      : match from_G' q with
        | inl q' => sweight q = sweight q'
        | inr (q1, q2) => sweight q <= sweight q1 - K + sweight q2
        end.
    Proof.
      clear -HI HG Hxs.
      induction q.
      - reflexivity.
      - simpl.
        destruct (Edge.eq_dec (y_0, - K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
        + destruct (fst_eq (fst_eq XX)). simpl.
          inversion XX. rewrite weight_SimplePaths_sub.
          destruct (from_G' q) as [q'|[q1 q2]]; simpl.
          * destruct (snd_eq XX); cbn.
            destruct e as [e He]; cbn in *; lia.
          * subst y.
            assert (Hle := lsp0_spec_le G (simplify2' G (to_paths G q1))).
            unfold lsp in *. rewrite Hxs /= in Hle.
            pose proof (weight_simplify2' G (to_paths G q1)).
            rewrite -sweight_weight in H. lia.
        + destruct (from_G' q) as [q'|[q1 q2]]; simpl.
          * lia.
          * rewrite weight_SimplePaths_sub; lia.
    Qed.

    Lemma lsp_paths {x y} (p : Paths G x y) : ∑ n, lsp G x y = Some n /\ weight p <= n.
    Proof.
      pose proof (lsp0_spec_le G (simplify2' G p)) as ineq.
      unfold lsp in *.
      destruct (lsp0 G (V G) x y). eexists; eauto. split; eauto.
      simpl in ineq. epose proof (weight_simplify2' G p). lia.
      now simpl in ineq.
    Qed.

    Global Instance HI' : invariants G'.
    Proof.
      split.
      - cbn. intros e He. apply EdgeSet.add_spec in He; destruct He as [He|He].
        subst; cbn. split; assumption.
        now apply HI.
      - apply HI.
      - intros z Hz. epose proof (source_paths G z Hz).
        destruct H as [[p [w]]]. sq. exists (to_G' p).
        sq. now rewrite to_G'_weight.
    Qed.

    Global Instance HG' : acyclic_no_loop G'.
    Proof.
      apply acyclic_caract2. exact _. intros x Hx.
      pose proof (lsp0_spec_le G' (spaths_refl G' (V G') x)) as H; cbn in H.
      case_eq (lsp0 G' (V G) x x); [|intro e; rewrite e in H; cbn in H; lia].
      intros m Hm. unfold lsp; cbn; rewrite Hm. rewrite Hm in H.
      simpl in H.
      apply lsp0_spec_eq in Hm.
      destruct Hm as [p Hp]. subst.
      pose proof (from_G'_weight p) as XX.
      destruct (from_G' p).
      - f_equal. rewrite (sweight_weight G s0) in XX.
        specialize (HG _ (to_paths G s0)). lia.
      - assert (Hle := lsp0_spec_le G (simplify2' G (concat G (to_paths G p0.2) (to_paths G p0.1)))).
        destruct p0 as [q1 q2]; simpl in *.
        unfold lsp in *; rewrite -> Hxs in Hle. simpl in Hle.
        epose proof (weight_simplify2' G (concat G (to_paths G q2) (to_paths G q1))).
        rewrite weight_concat - !sweight_weight in H0. f_equal.
        enough (sweight q1 - K + sweight q2 <= 0). lia.
        lia.
    Qed.

    Lemma lsp_G'_yx : (Some (- K) <= lsp G' y_0 x_0)%nbar.
    Proof.
      unshelve refine (transport (fun K => (Some K <= _)%nbar) _ (lsp0_spec_le _ _)).
      - eapply spaths_one; tas.
        apply EdgeSet.add_spec. now left.
      - cbn. lia.
    Qed.

    Lemma correct_labelling_lsp_G'
      : correct_labelling G (to_label ∘ (lsp G' (s G'))).
    Proof.
      pose proof (lsp_correctness G') as XX.
      split. exact XX.p1.
      intros e He; apply XX; cbn.
      apply EdgeSet.add_spec; now right.
    Qed.

    Definition sto_G' {S u v} (p : SimplePaths G S u v)
      : SimplePaths G' S u v.
    Proof.
      clear -p. induction p.
      - constructor.
      - econstructor; tea. exists e.π1.
        apply EdgeSet.add_spec. right. exact e.π2.
    Defined.


    Lemma sto_G'_weight {S u v} (p : SimplePaths G S u v)
      : sweight (sto_G' p) = sweight p.
    Proof.
      clear.
      induction p. reflexivity.
      simpl. now rewrite IHp.
    Qed.

    Lemma lsp_G'_incr x y : (lsp G x y <= lsp G' x y)%nbar.
    Proof.
      case_eq (lsp G x y); cbn; [|trivial].
      intros kxy Hkxy. apply lsp0_spec_eq in Hkxy.
      destruct Hkxy as [pxy Hkxy].
      etransitivity. 2: eapply (lsp0_spec_le _ (sto_G' pxy)).
      rewrite sto_G'_weight. now rewrite Hkxy.
    Qed.

    Lemma lsp_G'_sx : (lsp G' (s G) y_0 + Some (- K) <= lsp G' (s G) x_0)%nbar.
    Proof.
      etransitivity. 2: eapply lsp_codistance; try exact _.
      apply plus_le_compat_l. apply lsp_G'_yx.
    Qed.

    Lemma lsp_G'_spec_left x :
      lsp G' y_0 x = max (lsp G y_0 x) (Some (- K) + lsp G x_0 x)%nbar.
    Proof.
      apply Nbar.le_antisymm.
      - case_eq (lsp G' y_0 x); [|cbn; trivial].
        intros k Hk.
        apply lsp0_spec_eq in Hk; destruct Hk as [p' Hk].
        subst k.
        generalize (from_G'_weight p').
        destruct (from_G' p') as [p|[p1 p2]].
        + intros ->. apply max_le'. left. apply lsp0_spec_le.
        + intros He. apply max_le'. right.
          pose proof (lsp_paths (to_paths G p2)) as [x0x [lspx0x wp2]].
          rewrite -sweight_weight in wp2. rewrite lspx0x. simpl.
          pose proof (lsp_paths (to_paths G p1)) as [y0y0 [lspy0 wp1]].
          rewrite -sweight_weight in wp1. rewrite lsp_xx in lspy0.
          injection lspy0; intros <-. lia.
      - apply max_lub. apply lsp_G'_incr.
        case_eq (lsp G x_0 x); cbn; [intros k Hk|trivial].
        etransitivity.
        2:apply (lsp_codistance G' y_0 x_0 x).
        pose proof (lsp_G'_yx).
        eapply le_Some_lsp in H as [y0x0 [-> w]].
        generalize (lsp_G'_incr x_0 x). rewrite Hk.
        move/le_Some_lsp => [x0x [-> w']]. simpl. lia.
    Qed.
    End graph2.
  End Subgraph1.

  Section subgraph.
    Context (G : t) {HI : invariants G} {HG : acyclic_no_loop G}.

    Section subgraph2.
      Context (y_0 x_0 : V.t) (Vx : VSet.In x_0 (V G))
              (Vy : VSet.In y_0 (V G))
              (Hxs : lsp G x_0 y_0 = None)              
              (K : Z).

      Local Definition G' : t
        := (V G, EdgeSet.add (y_0, K, x_0) (E G), s G).

      Definition to_G' {u v} (q : Paths G u v) : Paths G' u v.
      Proof.
        clear -q.
        induction q; [constructor|].
        econstructor. 2: eassumption.
        exists e.π1. cbn. apply EdgeSet.add_spec; right. exact e.π2.
      Defined.

      Lemma to_G'_weight {u v} (p : Paths G u v)
        : weight (to_G' p) = weight p.
      Proof.
        clear.
        induction p. reflexivity.
        simpl. now rewrite IHp.
      Qed.

      Opaque Edge.eq_dec.


      Definition from_G'_path {u v} (q : Paths G' u v)
        : Paths G u v + (Paths G u y_0 * Paths G x_0 v).
      Proof.
        clear -q. induction q.
        - left; constructor.
        - induction (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX].
          + right. split.
            * rewrite (fst_eq (fst_eq XX)); constructor.
            * destruct IHq as [IHq|IHq].
              -- now rewrite (snd_eq XX).
              -- exact IHq.2.
          + induction IHq as [IHq|IHq].
            * left. econstructor; try eassumption.
              exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            * right. split.
              -- econstructor; try eassumption.
                  2: exact IHq.1.
                  exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
              -- exact IHq.2.
      Defined.


      Lemma from_G'_path_weight {u v} (q : Paths G' u v)
        : weight q = match from_G'_path q with
                    | inl q' => weight q'
                    | inr (q1, q2) => weight q1 + K + weight q2
                      end.
      Proof.
        clear -HI HG Hxs.
        induction q.
        - reflexivity.
        - simpl.
          destruct (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
          + destruct (fst_eq (fst_eq XX)). simpl.
            inversion XX. 
            destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
            * destruct (snd_eq XX); cbn.
              destruct e as [e He]; cbn in *. lia.
            * subst y. rewrite IHq.
              simple refine (let XX := lsp0_spec_le
                                          G (simplify2' G q1) in _).
              unfold lsp in *. rewrite -> Hxs in XX; inversion XX.
          + destruct (from_G'_path q) as [q'|[q1 q2]]; simpl.
            * lia.
            * lia.
      Qed.

      Definition from_G' {S u v} (q : SimplePaths G' S u v)
        : SimplePaths G S u v + (SimplePaths G S u y_0 * SimplePaths G S x_0 v).
      Proof.
        clear -q. induction q.
        - left; constructor.
        - induction (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX].
          + right. split.
            * rewrite (fst_eq (fst_eq XX)); constructor.
            * eapply SimplePaths_sub.
              eapply DisjointAdd_Subset; eassumption.
              induction IHq as [IHq|IHq].
              -- now rewrite (snd_eq XX).
              -- exact IHq.2.
          + induction IHq as [IHq|IHq].
            * left. econstructor; try eassumption.
              exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
            * right. split.
              -- econstructor; try eassumption.
                  2: exact IHq.1.
                  exists e.π1. exact (EdgeSetFact.add_3 XX e.π2).
              -- eapply SimplePaths_sub; [|exact IHq.2].
                  eapply DisjointAdd_Subset; eassumption.
      Defined.

      Lemma from_G'_weight {S u v} (q : SimplePaths G' S u v)
        : sweight q = match from_G' q with
                      | inl q' => sweight q'
                      | inr (q1, q2) => sweight q1 + K + sweight q2
                      end.
      Proof.
        clear -HI HG Hxs.
        induction q.
        - reflexivity.
        - simpl.
          destruct (Edge.eq_dec (y_0, K, x_0) (x, e.π1, y)) as [XX|XX]; simpl.
          + destruct (fst_eq (fst_eq XX)). simpl.
            inversion XX. rewrite weight_SimplePaths_sub.
            destruct (from_G' q) as [q'|[q1 q2]]; simpl.
            * destruct (snd_eq XX); cbn.
              destruct e as [e He]; cbn in *; lia.
            * subst y.
              simple refine (let XX := lsp0_spec_le
                                          G (simplify2' G (to_paths G q1)) in _).
              unfold lsp in *. rewrite -> Hxs in XX; inversion XX.
          + destruct (from_G' q) as [q'|[q1 q2]]; simpl.
            * lia.
            * rewrite weight_SimplePaths_sub; lia.
      Qed.

      Lemma lsp_paths {x y} (p : Paths G x y) : ∑ n, lsp G x y = Some n.
      Proof.
        pose proof (lsp0_spec_le G (simplify2' G p)) as ineq.
        unfold lsp in *.
        destruct (lsp0 G (V G) x y). eexists; eauto.
        now simpl in ineq.
      Qed.

      Global Instance HI' : invariants G'.
      Proof.
        split.
        - cbn. intros e He. apply EdgeSet.add_spec in He; destruct He as [He|He].
          subst; cbn. split; assumption.
          now apply HI.
        - apply HI.
        - intros z Hz. epose proof (source_paths G z Hz).
          destruct H as [[p [w]]]. sq. exists (to_G' p).
          sq. now rewrite to_G'_weight.
      Qed.

      Global Instance HG' : acyclic_no_loop G'.
      Proof.
        apply acyclic_caract2. exact _. intros x Hx.
        pose proof (lsp0_spec_le G' (spaths_refl G' (V G') x)) as H; cbn in H.
        case_eq (lsp0 G' (V G) x x); [|intro e; rewrite e in H; cbn in H; lia].
        intros m Hm. unfold lsp; cbn; rewrite Hm. rewrite Hm in H.
        simpl in H.
        apply lsp0_spec_eq in Hm.
        destruct Hm as [p Hp]. subst.
        pose proof (from_G'_weight p) as XX.
        destruct (from_G' p).
        - f_equal. rewrite (sweight_weight G s0) in XX.
          specialize (HG _ (to_paths G s0)). lia.
        - simple refine (let XX := lsp0_spec_le
            G (simplify2' G (concat G (to_paths G p0.2) (to_paths G p0.1))) in _).
          unfold lsp in *; rewrite -> Hxs in XX; inversion XX.
      Qed.

      Lemma lsp_G'_yx : (Some K <= lsp G' y_0 x_0)%nbar.
      Proof.
        unshelve refine (transport (fun K => (Some K <= _)%nbar) _ (lsp0_spec_le _ _)).
        - eapply spaths_one; tas.
          apply EdgeSet.add_spec. now left.
        - cbn. lia.
      Qed.

      Lemma lsp_G'_sx : (lsp G' (s G) y_0 + Some K <= lsp G' (s G) x_0)%nbar.
      Proof.
        etransitivity. 2: eapply lsp_codistance; try exact _.
        apply plus_le_compat_l. apply lsp_G'_yx.
      Qed.

      Lemma correct_labelling_lsp_G'
        : correct_labelling G (to_label ∘ (lsp G' (s G'))).
      Proof.
        pose proof (lsp_correctness G') as XX.
        split. exact XX.p1.
        intros e He; apply XX; cbn.
        apply EdgeSet.add_spec; now right.
      Qed.

      Definition sto_G' {S u v} (p : SimplePaths G S u v)
        : SimplePaths G' S u v.
      Proof.
        clear -p. induction p.
        - constructor.
        - econstructor; tea. exists e.π1.
          apply EdgeSet.add_spec. right. exact e.π2.
      Defined.


      Lemma sto_G'_weight {S u v} (p : SimplePaths G S u v)
        : sweight (sto_G' p) = sweight p.
      Proof.
        clear.
        induction p. reflexivity.
        simpl. now rewrite IHp.
      Qed.

      Lemma lsp_G'_incr x y : (lsp G x y <= lsp G' x y)%nbar.
      Proof.
        case_eq (lsp G x y); cbn; [|trivial].
        intros kxy Hkxy. apply lsp0_spec_eq in Hkxy.
        destruct Hkxy as [pxy Hkxy].
        etransitivity. 2: eapply (lsp0_spec_le _ (sto_G' pxy)).
        rewrite sto_G'_weight. now rewrite Hkxy.
      Qed.

      Lemma lsp_G'_spec_left x :
        lsp G' y_0 x = max (lsp G y_0 x) (Some K + lsp G x_0 x)%nbar.
      Proof.
        apply Nbar.le_antisymm.
        - case_eq (lsp G' y_0 x); [|cbn; trivial].
          intros k Hk.
          apply lsp0_spec_eq in Hk; destruct Hk as [p' Hk].
          subst k.
          rewrite (from_G'_weight p').
          destruct (from_G' p') as [p|[p1 p2]].
          + apply max_le'. left. apply lsp0_spec_le.
          + apply max_le'. right.
            apply (plus_le_compat (Some (sweight p1 + K)) _ (Some (sweight p2))).
            * cbn. rewrite sweight_weight.
              specialize (HG _ (to_paths G p1)). simpl in *.
              assert (forall x n, n <= 0 -> n + x <= x). lia. apply H. auto.
            * apply lsp0_spec_le.
        - apply max_lub. apply lsp_G'_incr.
          case_eq (lsp G x_0 x); cbn; [intros k Hk|trivial].
          apply lsp0_spec_eq in Hk. destruct Hk as [p Hk].
          unshelve refine (transport (fun K => (Some K <= _)%nbar)
                                      _ (lsp0_spec_le _ _)).
          eapply SimplePaths_sub. shelve.
          pose (p' := sto_G' p).
          unshelve econstructor.
          + exact (snodes G' p').
          + shelve.
          + apply DisjointAdd_add2.
            intro HH. eapply left, split in HH.
            destruct HH as [p1 _].
            apply from_G' in p1. destruct p1 as [p1|[p1 p2]].
            all: epose proof (lsp0_spec_le _ (SimplePaths_sub _ _ p1)) as HH;
              unfold lsp in Hxs; now erewrite Hxs in HH.
          + exists K. apply EdgeSet.add_spec. now left.
          + exact (reduce _ p').
          + rewrite weight_SimplePaths_sub. cbn.
            now rewrite weight_reduce sto_G'_weight Hk.
          Unshelve.
          2-3: now apply VSetProp.subset_remove_3.
          apply VSetProp.subset_add_3. assumption.
          apply snodes_Subset.
      Qed.
    End subgraph2.

    Lemma VSet_add_remove x y p : 
      x <> y ->
      VSet.Equal (VSet.add x (VSet.remove y p)) (VSet.remove y (VSet.add x p)).
    Proof. now sets. Qed.
    
    Lemma VSet_remove_add x p : 
      ~ VSet.In x p ->
      VSet.Equal (VSet.remove x (VSet.add x p)) p.
    Proof. now sets. Qed.


    Lemma VSet_add_add x y p : 
      VSet.Equal (VSet.add x (VSet.add y p)) (VSet.add y (VSet.add x p)).
    Proof. now sets. Qed.

    Lemma VSet_add_add_same x p : 
      VSet.Equal (VSet.add x (VSet.add x p)) (VSet.add x p).
    Proof. now sets. Qed.

    Lemma SimplePaths_sets {s x y} (p : SimplePaths G s x y)
      : x = y \/ VSet.In x s.
    Proof.
      induction p. left; auto.
      destruct IHp; subst. right.
      destruct d.
      apply H. left; auto.
      right. apply d. left; auto.
    Qed.

    Arguments paths_refl {G x}.
    Arguments paths_step {G x y z}.
    
    Fixpoint Paths_add_end {x y z} (p : Paths G x y) : Edges G y z -> Paths G x z :=
      match p with
      | paths_refl => fun e => paths_step e paths_refl
      | paths_step e' p' => fun e => paths_step e' (Paths_add_end p' e)
      end.

    Lemma Paths_add_end_weight {x y z} (p : Paths G x y) (e : Edges G y z) : weight (Paths_add_end p e) = weight p + e.π1.
    Proof.
      induction p; simpl; auto. lia.
      rewrite IHp. lia.
    Qed.

    Lemma negbe {b} : ~~ b <-> (~ b).
    Proof.
      intuition try congruence.
      now rewrite H0 in H.
      destruct b; simpl; auto.
    Qed.

    Lemma In_nodes_app_end {x y z} (p : Paths G x y) (e : Edges G y z) i : 
      VSet.In i (nodes G (Paths_add_end p e)) -> 
      VSet.In i (nodes G p) \/ i = y.
    Proof.
      induction p; simpl; try sets.
      rewrite VSet.add_spec.
      intros []; subst.
      - sets.
      - specialize (IHp _ H). sets.
    Qed.

    Lemma paths_add_end_simpl {x y z} (p : Paths G x y) (e : Edges G y z) : 
      is_simple _ p -> ~~ VSet.mem y (nodes G p) -> is_simple _ (Paths_add_end p e).
    Proof.
      induction p; simpl; auto.
      now rewrite andb_true_r.
      move/andP => [nmen iss].
      specialize (IHp e iss). intros Hm%negbe.
      rewrite andb_and. split; auto.
      apply negbe. intro. 
      apply VSet.mem_spec in H.
      apply Hm. eapply In_nodes_app_end in H as [inn | ->].
      eapply negbe in nmen. now elim nmen; apply VSet.mem_spec.
      apply VSet.mem_spec. sets.
      eapply IHp. apply negbe => nmem. eapply VSet.mem_spec in nmem.
      eapply Hm. eapply VSet.mem_spec, VSet.add_spec. sets.
    Qed.

    Definition Disjoint s s' := 
      VSet.Empty (VSet.inter s s').
 
    Lemma Disjoint_DisjointAdd x s s' s'' : 
      DisjointAdd x s s' -> 
      Disjoint s' s'' ->
      Disjoint s s''.
    Proof.
      intros da; unfold Disjoint.
      intros disj i. specialize (disj i).
      intros ininter; apply disj.
      eapply DisjointAdd_Subset in da.
      sets.
    Qed.

    Obligation Tactic := Program.Tactics.program_simpl.
    Program Fixpoint sconcat {s s' x y z} (p : SimplePaths G s x y) : Disjoint s s' -> 
      SimplePaths G s' y z -> SimplePaths G (VSet.union s s') x z :=
      match p in SimplePaths _ s x y return Disjoint s s' -> SimplePaths G s' y z -> SimplePaths G (VSet.union s s') x z  with
      | spaths_refl _ _ _ => fun hin q => SimplePaths_sub _ _ q
      | @spaths_step _ s s0 x y z' da e p => fun hin q =>
        @spaths_step _ (VSet.union s s') _ x y z _ e (@sconcat _ _ _ _ _ p _ q)
      end.
      Next Obligation. sets. Qed.
      Next Obligation. 
      Proof.
        eapply DisjointAdd_union; eauto.
        destruct da. unfold Disjoint in hin.
        intros inxs'. apply (hin x).
        destruct (H x). specialize (H2 (or_introl eq_refl)).
        now eapply VSet.inter_spec.
      Qed.
      Next Obligation.
        eapply Disjoint_DisjointAdd in hin; eauto.
      Qed.

    Lemma DisjointAdd_remove_add {x s} :
      DisjointAdd x (VSet.remove x s) (VSet.add x s).
    Proof. split; [intro|]; sets. Qed.

    Lemma DisjointAdd_Equal x s s' s'' : DisjointAdd x s s' -> VSet.Equal s' s'' -> DisjointAdd x s s''.
    Proof. now intros d <-. Qed.

    Lemma DisjointAdd_Equal_l x s s' s'' : DisjointAdd x s s' -> VSet.Equal s s'' -> DisjointAdd x s'' s'.
    Proof. now intros d <-. Qed.

    Lemma DisjointAdd_remove_inv {x s s' z} : DisjointAdd x s (VSet.remove z s') -> 
      VSet.Equal s (VSet.remove z s).
    Proof.
      intros [].
      intros i. rewrite VSet.remove_spec.
      intuition auto. red in H2; subst.
      specialize (proj2 (H z) (or_intror H1)).
      rewrite VSet.remove_spec.
      intuition.
    Qed.

    Lemma leq_vertices_caract0 {n x y} (Vy : VSet.In y (V G)) :
      leq_vertices G n x y <-> (Some n <= lsp G x y)%nbar.
    Proof.
      split; intro Hle.
      - assert (Vx : VSet.In x (V G)). {
          case_eq (VSet.mem x (V G)); intro Vx; [now apply VSet.mem_spec in Vx|].
          apply False_rect. apply VSetFact.not_mem_iff in Vx.
          pose (K := (if (n <=? 0)%Z then (Z.to_nat (Z.of_nat (to_label (lsp G (s G) y)) - n)) + 1 else to_label (lsp G (s G) y))%nat).
          pose (l := fun z => if V.eq_dec z x then K
                           else to_label (lsp G (s G) z)).
          unshelve refine (let XX := Hle l _ in _); subst l K.
          * split.
            -- destruct (V.eq_dec (s G) x).
               apply False_rect. apply Vx. subst; apply HI.
               now apply lsp_correctness.
            -- intros e H.
               destruct (V.eq_dec e..s x).
               apply False_rect, Vx; subst; now apply HI.
               destruct (V.eq_dec e..t x).
               apply False_rect, Vx; subst; now apply HI.
               now apply lsp_correctness.
          * clearbody XX; cbn in XX.
            destruct (V.eq_dec x x) as [Hx|Hx]; [|now apply Hx].
            destruct (V.eq_dec y x) as [Hy|Hy].
            now subst.
            pose proof (lsp_correctness G).
            specialize (Hle _ H). simpl in Hle.
            destruct (Z_of_to_label_s G y) as [zl [eq [pos zof]]]; eauto.
            rewrite zof in XX, Hle.
            destruct (Z.leb_spec n 0).
            rewrite Nat2Z.inj_add in XX.
            rewrite Z2Nat.id in XX; try lia.
            rewrite zof in XX. lia. }
        destruct (Z_of_to_label_s G y Vy) as [ly [Hly [Hpos Hlab]]].
        destruct (Z_of_to_label_s G _ Vx) as [lx [Hlx [poskx Hlab']]].
        destruct (lsp G x (s G)) eqn:xs.
        + destruct (lsp G x y) as [K|] eqn:xy. simpl.
          2:{ simpl.
            generalize (lsp_codistance G x (s G) y).
            now rewrite xs Hly xy /=. }
          unshelve epose proof (Subgraph1.correct_labelling_lsp_G' _ _ _ _ _ _ xy) as XX;
            tas; try apply HI.
          set (G' := Subgraph1.G' G y x K) in XX.
          assert (HI' : invariants G'). { eapply Subgraph1.HI'; tas. }
          specialize (Hle _ XX); clear XX; cbn in Hle.
          assert (HG' : acyclic_no_loop G'). { apply Subgraph1.HG'; eauto. }
          assert (XX: (Some (- K) <= lsp G' y x)%nbar). {
            apply Subgraph1.lsp_G'_yx. apply Vy. }
          apply le_Some_lsp in XX as [yx [lspyx lekyx]].
          destruct (Z_of_to_label_s G' _ Vx) as [kx' [Hkx' [kx'pos zofx']]].
          cbn in *; rewrite zofx' in Hle.
          destruct (Z_of_to_label_s G' _ Vy) as [ky' [Hky' [ky'pos zofy']]].
          cbn in Hky'; rewrite zofy' in Hle; cbn in *.
          epose proof (Subgraph1.lsp_G'_spec_left G _ _ Vx Vy _ xy x).
          rewrite lspyx in H. rewrite lsp_xx in H. simpl in H.
          pose proof (lsp_sym _ xy).
          assert (yx = - K).
          { destruct (lsp G y x); simpl in *; injection H. simpl. lia. lia. }
          subst yx.
          pose proof (lsp_codistance G' (s G) y x).
          rewrite Hky' lspyx Hkx' in H1. simpl in H1. lia.
             
        + pose (K := if n <=? 0 then Z.max lx (Z.succ ly - n) else Z.max lx (Z.succ ly)).
          unshelve epose proof (correct_labelling_lsp_G' _ _ _ _ xs K) as XX;
            tas; try apply HI.
          set (G' := G' (s G) x K) in XX.
          assert (HI' : invariants G'). {
            eapply HI'; tas. apply HI. }
          specialize (Hle _ XX); clear XX; cbn in Hle.
          assert (XX: (Some K <= lsp G' (s G) x)%nbar). {
            apply lsp_G'_yx. apply HI. }
          assert (HG' : acyclic_no_loop G'). { apply HG'; eauto. apply HI. }
          destruct (Z_of_to_label_s G' _ Vx) as [kx' [Hkx' [kx'pos zofx']]].
          cbn in Hkx'; rewrite Hkx' in XX; cbn in *.
          rewrite zofx' in Hle.
          destruct (Z_of_to_label_s G' _ Vy) as [ky' [Hky' [ky'pos zofy']]].
          cbn in Hky'; rewrite zofy' in Hle; cbn in *.
          assert (Hle'' : K + n <= ky') by lia; clear Hle.
          enough ((Some ky' <= Some K + lsp G x y)%nbar) as HH. {
            revert HH. destruct (lsp G x y); cbn; auto. lia. }
          unshelve erewrite (lsp_G'_spec_left (s G) x _ xs K) in Hky'. apply HI.
          apply eq_max in Hky'. destruct Hky' as [Hk|Hk].
          -- rewrite Hly in Hk. apply some_inj in Hk.
            elimtype False.
            clear -XX ky'pos Hk Hle''. subst. subst K.
            destruct (Z.leb_spec n 0); lia.
          -- rewrite Hk. reflexivity.
      - case_eq (lsp G x y).
        * intros m Hm l Hl. rewrite Hm in Hle.
          apply (lsp0_spec_eq G) in Hm. destruct Hm as [p Hp].
          pose proof (correct_labelling_Paths G l Hl _ _ (to_paths G p)) as XX.
          rewrite <- sweight_weight, Hp in XX. cbn in Hle; lia.
        * intro X; rewrite X in Hle; inversion Hle.
    Defined.

    Lemma lsp_vset_in {s x y n} : 
      lsp0 G s x y = Some n -> 
      (n = 0 /\ x = y) \/ (VSet.In y (V G)).
    Proof.
      intros H.
      eapply lsp0_spec_eq in H.
      destruct H. subst n. induction x0.
      simpl. left; auto. destruct IHx0 as [[sw ->]|IH].
      destruct e. simpl. specialize (edges_vertices _ _ i) as [Hs Ht]. right; apply Ht.
      right; auto.
    Qed.

    Lemma leq_vertices_caract {n x y} :
      leq_vertices G n x y <-> (if VSet.mem y (V G) then Some n <= lsp G x y
                             else (n <= 0)%Z /\ (x = y \/ Some n <= lsp G x (s G)))%nbar.
    Proof.
      case_eq (VSet.mem y (V G)); intro Vy;
        [apply VSet.mem_spec in Vy; now apply leq_vertices_caract0|].
      split.
      - intro Hle. apply VSetFact.not_mem_iff in Vy. 
        assert (nneg : n <= 0).
        { pose (K := to_label (lsp G (s G) x)).
          pose (l := fun z => if V.eq_dec z y then K
                           else to_label (lsp G (s G) z)).
            unshelve refine (let XX := Hle l _ in _); subst l K.
            -- split.
              ++ destruct (V.eq_dec (s G) y).
                 apply False_rect. apply Vy. subst; apply HI.
                 now apply lsp_correctness.
              ++ intros e H.
                 destruct (V.eq_dec e..s y).
                 apply False_rect, Vy; subst; now apply HI.
                 destruct (V.eq_dec e..t y).
                 apply False_rect, Vy; subst; now apply HI.
                 now apply lsp_correctness.
            -- clearbody XX; cbn in XX.
               destruct (V.eq_dec y y) as [?|?]; simpl in *; [|contradiction].
               destruct (V.eq_dec x y) as [Hy|Hy]; simpl in *; [intuition|lia]. }
        split; auto.
        + destruct (V.eq_dec x y); [now left|right].
          case_eq (lsp G x (s G)); [intros; cbn; try lia|].
          ++ destruct (VSet.mem x (V G)) eqn:mem.
             2:{ enough (z = 0); try lia.
                 epose proof (lsp0_spec_eq G _ H) as [p wp]. 
                 assert (~ VSet.In x (V G)). 
                 { intros inx. eapply VSet.mem_spec in inx. congruence. }
                 clear - HI HG H0 p wp. 
                 depind p. simpl in wp. lia.
                 epose proof (edges_vertices G). destruct e. 
                 specialize (H _ i) as [H _]. cbn in H. contradiction. }
             apply VSet.mem_spec in mem. red in Hle.
             unshelve epose proof (Subgraph1.correct_labelling_lsp_G' G (s G) x mem _ _ H) as X.
             now apply source_vertex.
            set (G' := Subgraph1.G' G (s G) x z) in X.
            assert (HI' : invariants G'). {
              eapply Subgraph1.HI'; tas. apply HI. }
            assert (HG' : acyclic_no_loop G'). {
              eapply Subgraph1.HG'; tas. apply HI. }
            pose (l := fun v => if V.eq_dec v y then 0%nat
                            else to_label (lsp G' (s G) v)).
            assert (XX : correct_labelling G l). {
              subst l; split.
              -- destruct (V.eq_dec (s G) y).
                apply False_rect. apply Vy. subst; apply HI.
                unfold lsp; rewrite acyclic_lsp0_xx; try assumption. reflexivity.
              -- intros e H'.
                destruct (V.eq_dec e..s y).
                apply False_rect, Vy; subst; now apply HI.
                destruct (V.eq_dec e..t y).
                apply False_rect, Vy; subst; now apply HI.
                simpl.
                now apply X. }
            specialize (Hle _ XX); subst l; cbn in *.
            destruct (V.eq_dec y y); [|contradiction].
            simpl in Hle.
            destruct (V.eq_dec x y); [contradiction|].
            simpl in Hle.
            destruct (lsp_s G' x) as [lx [lspx wx]]; auto.
            rewrite lspx in Hle.
            rewrite Z_of_to_label_pos in Hle. lia.
            assert (lx = - z).
            { enough (lsp G' (s G') x = Some (- z)). congruence.
              rewrite (Subgraph1.lsp_G'_spec_left G _ _ _ _ _ H x). auto. 
              apply source_vertex; eauto.
              rewrite lsp_xx /=.
              pose proof (lsp_s G x mem) as [lx' [lspx' w]].
              enough (lsp G (s G) x <= Some (-z))%nbar. rewrite lspx' /= in H0.
              rewrite lspx'. simpl. f_equal. lia.
              apply (lsp_sym _ H). }
            subst lx. lia.

          ++ intros Hxs. simpl.
          case_eq (VSet.mem x (V G)); intro Vx.
          * apply VSet.mem_spec in Vx.
            assert (x <> s G). 
            { destruct (V.eq_dec x (s G)) => //. rewrite e in Hxs.
              epose proof (lsp0_spec_le G (spaths_refl G (V G) (s G))).
              rewrite /lsp in Hxs. now rewrite Hxs in H. }
            pose (K := Z.succ (- n - n) ).
            unshelve epose proof (correct_labelling_lsp_G' _ _ _ _ Hxs K) as X;
              tas; try apply HI.
            set (G' := G' (s G) x K) in X.
            assert (HI' : invariants G'). {
              eapply HI'; tas. apply HI. }
            assert (HG' : acyclic_no_loop G'). {
              eapply HG'; tas. apply HI. }
            pose (l := fun z => if V.eq_dec z y then Z.to_nat (-n)
                             else to_label (lsp G' (s G) z)).
            assert (XX : correct_labelling G l). {
              subst l; split.
              -- destruct (V.eq_dec (s G) y).
                 apply False_rect. apply Vy. subst; apply HI.
                 unfold lsp; rewrite acyclic_lsp0_xx; try assumption. reflexivity.
              -- intros e H'.
                 destruct (V.eq_dec e..s y).
                 apply False_rect, Vy; subst; now apply HI.
                 destruct (V.eq_dec e..t y).
                 apply False_rect, Vy; subst; now apply HI.
                 now apply X. }
            specialize (Hle _ XX); subst l; cbn in *.
            destruct (V.eq_dec y y) as [?|?]; [|contradiction].
            destruct (V.eq_dec x y) as [Hy|Hy]. simpl in *. contradiction.
            simple refine (let YY := lsp0_spec_le G'
                                (spaths_step G' _ (V G) (s G) x x ?[XX] (K; _)
                                             (spaths_refl _ _ _)) in _).
            [XX]: apply DisjointAdd_remove1. apply HI.
            apply EdgeSet.add_spec. left; reflexivity.
            clearbody YY; simpl in YY.
            case_eq (lsp0 G' (V G) (s G) x);
              [|intro HH; rewrite HH in YY; inversion YY].
            intros kx Hkx.
            unfold lsp in Hle; cbn in *; rewrite Hkx in YY, Hle.
            rewrite Z_of_to_label in Hle. simpl in YY.
            destruct (Z.leb_spec 0 kx).
            rewrite Z2Nat.id in Hle; lia.
            subst K. lia.
          * apply VSetFact.not_mem_iff in Vx.
            pose (K := to_label (lsp G (s G) x)).
            pose (l := fun z => if V.eq_dec z y then 0%nat
                             else if V.eq_dec z x then (Z.to_nat (- n) + 1)%nat
                             else to_label (lsp G (s G) z)).
            unshelve refine (let XX := Hle l _ in _); subst l K.
            -- split.
               +++ destruct (V.eq_dec (s G) y).
                  apply False_rect. apply Vy. subst; apply HI.
                  destruct (V.eq_dec (s G) x).
                  apply False_rect. apply Vx. subst; apply HI.
                  now apply lsp_correctness.
               +++ intros e H.
                  destruct (V.eq_dec e..s y).
                  apply False_rect, Vy; subst; now apply HI.
                  destruct (V.eq_dec e..t y).
                  apply False_rect, Vy; subst; now apply HI.
                  destruct (V.eq_dec e..s x).
                  apply False_rect, Vx; subst; now apply HI.
                  destruct (V.eq_dec e..t x).
                  apply False_rect, Vx; subst; now apply HI.
                  now apply lsp_correctness.
            -- clearbody XX; cbn in XX.
               destruct (V.eq_dec y y) as [?|?]; [|contradiction].
               destruct (V.eq_dec x y) as [Hy|Hy]. simpl in *; contradiction.
               destruct (V.eq_dec x x) as [?|?]; simpl in *; [lia|contradiction].
      - intros [e [Hxy|Hxs]] l Hl; subst; [lia|].
        case_eq (lsp G x (s G)); [|intro H; rewrite H in Hxs; inversion Hxs].
        intros k Hk.
        rewrite Hk in Hxs. simpl in Hxs.
        destruct (lsp0_spec_eq _ _ Hk) as [p Hp].
        epose proof (correct_labelling_Paths G l Hl _ _ (to_paths G p)).
        rewrite (proj1 Hl) in H.
        simpl in Hxs. rewrite <- sweight_weight, Hp in H.
        lia.
    Defined.
    
    Definition leqb_vertices z x y : bool :=
      if VSet.mem y (V G) then if is_left (Nbar.le_dec (Some z) (lsp G x y)) then true else false
      else (Z.leb z 0 && (V.eq_dec x y || Nbar.le_dec (Some z) (lsp G x (s G))))%bool.

    Lemma leqb_vertices_correct n x y
      : leq_vertices G n x y <-> leqb_vertices n x y.
    Proof.
      etransitivity. apply leq_vertices_caract. unfold leqb_vertices.
      destruct (VSet.mem y (V G)).
      - destruct (le_dec (Some n) (lsp G x y)); cbn; intuition.
        discriminate.
      - symmetry; etransitivity. apply andb_and.
        apply Morphisms_Prop.and_iff_morphism.
        apply Z.leb_le.
        etransitivity. apply orb_true_iff.
        apply Morphisms_Prop.or_iff_morphism.
        destruct (V.eq_dec x y); cbn; intuition; try discriminate.
        destruct (le_dec (Some n) (lsp G x (s G))); cbn; intuition.
        discriminate.
    Qed.

  End subgraph.

End WeightedGraph.