From Coq Require Import MSetList MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils BasicAst config.

Local Open Scope nat_scope.
Local Open Scope string_scope2.


Ltac absurd :=
  match goal with
  | [H : False |- _] => elim H
  end.
Hint Extern 10 => absurd : core.

(** * Valuations *)

(** A valuation is a universe level (nat) given for each
    universe variable (Level.t).
    It is >= for polymorphic universes and > 0 for monomorphic universes. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Class Evaluable (A : Type) := val : valuation -> A -> nat.

(** Levels are Set or Level or Var *)
Module Level.
  Inductive t_ : Set :=
  | lSet
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices in the local universe polymorphic context *).

  Definition t := t_.

  Definition is_small (x : t) :=
    match x with
    | lSet => true
    | _ => false
    end.

  Definition is_set (x : t) :=
    match x with
    | lSet => true
    | _ => false
    end.

  Definition is_var (l : t) :=
    match l with
    | Var _ => true
    | _ => false
    end.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | lSet =>  (0%nat)
               | Level s => (Pos.to_nat (v.(valuation_mono) s))
               | Var x => (v.(valuation_poly) x)
               end.


  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lSet, lSet => Eq
    | lSet, _ => Lt
    | _, lSet => Gt
    | Level s1, Level s2 => string_compare s1 s2
    | Level _, _ => Lt
    | _, Level _ => Gt
    | Var n, Var m => Nat.compare n m
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lSet (Level s)
  | ltSetVar n : lt_ lSet (Var n)
  | ltLevelLevel s s' : string_lt s s' -> lt_ (Level s) (Level s')
  | ltLevelVar s n : lt_ (Level s) (Var n)
  | ltVarVar n n' : Nat.lt n n' -> lt_ (Var n) (Var n').

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [| |] X; inversion X.
      eapply string_lt_irreflexive; tea.
      eapply Nat.lt_irrefl; tea.
    - intros [| |] [| |] [| |] X1 X2;
        inversion X1; inversion X2; constructor.
      eapply transitive_string_lt; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] []; repeat constructor.
    - eapply CompareSpec_Proper.
      5: eapply CompareSpec_string. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
  Qed.

  (* Bonus *)
  Definition eqb (l1 l2 : Level.t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.

  Global Instance eqb_refl : Reflexive eqb.
  Proof.
    intros []; unfold eqb; cbnr.
    - rewrite (ssreflect.iffRL (string_compare_eq s s)). all: auto.
    - rewrite Nat.compare_refl. reflexivity.
  Qed.

  Lemma eqb_spec l l' : reflect (eq l l') (eqb l l').
  Proof.
    destruct l, l'; cbn; try constructor; try reflexivity; try discriminate.
    - apply iff_reflect. unfold eqb; cbn.
      destruct (CompareSpec_string s s0); split; intro HH;
        try reflexivity; try discriminate; try congruence.
      all: inversion HH; subst; now apply string_lt_irreflexive in H.
    - apply iff_reflect. unfold eqb; cbn.
      destruct (Nat.compare_spec n n0); split; intro HH;
        try reflexivity; try discriminate; try congruence.
      all: inversion HH; subst; now apply Nat.lt_irrefl in H.
  Qed.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End Level.

Module LevelSet := MSetList.MakeWithLeibniz Level.
Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := WDecide (LevelSet).
Ltac lsets := LevelSetDecide.fsetdec.

Definition LevelSet_pair x y
  := LevelSet.add y (LevelSet.singleton x).

Lemma LevelSet_pair_In x y z :
  LevelSet.In x (LevelSet_pair y z) -> x = y \/ x = z.
Proof.
  intro H. apply LevelSetFact.add_iff in H.
  destruct H; [intuition|].
  apply LevelSetFact.singleton_1 in H; intuition.
Qed.

Definition LevelSet_mem_union (s s' : LevelSet.t) x :
  LevelSet.mem x (LevelSet.union s s') <-> LevelSet.mem x s \/ LevelSet.mem x s'.
Proof.
  rewrite LevelSetFact.union_b.
  apply orb_true_iff.
Qed.


Module UnivExpr.
  (* npe = no prop expression *)
  (* (u,k) represents u + k *)
  Definition t := (Level.t * nat)%type.

  Global Instance Evaluable : Evaluable t
    := fun v l => (snd l + val v (fst l)).

  Definition succ (l : t) := (fst l, S (snd l)).

  Definition get_level (e : t) : Level.t := fst e.

  Definition get_noprop_deprecated (e : UnivExpr.t) := Some (fst e).
  #[deprecated(note="Is that used ?")]
  Notation get_noprop := get_noprop_deprecated.

  Definition is_small (e : t) : bool :=
    match e with
    | (Level.lSet, 0%nat) => true
    | _  => false
    end.

  Definition is_level (e : t) : bool :=
    match e with
    | (_, 0%nat) => true
    | _  => false
    end.

  Definition make (l : Level.t) : t := (l, 0%nat).

  Definition set : t := (Level.lSet, 0%nat).
  Definition type1 : t := (Level.lSet, 1%nat).

  (* Used for (un)quoting. *)
  Definition from_kernel_repr (e : Level.t * bool) : t
    := (e.1, if e.2 then 1%nat else 0%nat).

  Definition to_kernel_repr (e : t) : Level.t * bool
    := match e with
       | (l, b) => (l, match b with 0%nat => false | _ => true end)
       end.

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltUnivExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltUnivExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X. subst. lia. subst.
      eapply Level.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1, H2.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match Level.compare l1 l2 with
      | Eq => Nat.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (Level.compare_spec t0 t1); repeat constructor; tas.
    subst.
    destruct (Nat.compare_spec n n0); repeat constructor; tas. congruence.
  Qed.

  Definition eq_dec (l1 l2 : t) : {l1 = l2} + {l1 <> l2}.
  Proof.
    repeat decide equality.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Lemma val_make v l
    : val v (UnivExpr.make l) = val v l.
  Proof.
    destruct l eqn:H; cbnr.
  Qed.

  Lemma val_make_npl v (l : Level.t)
    : val v (UnivExpr.make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

End UnivExpr.

Module UnivExprSet := MSetList.MakeWithLeibniz UnivExpr.
Module UnivExprSetFact := WFactsOn UnivExpr UnivExprSet.
Module UnivExprSetProp := WPropertiesOn UnivExpr UnivExprSet.

Module UniverseLevel.
  (** A universe level is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty
   It represents the max of its constituents. *)
  Record t_ := { t_set : UnivExprSet.t ;
                 t_ne  : UnivExprSet.is_empty t_set = false }.


  Definition t := t_.

  Coercion t_set : t_ >-> UnivExprSet.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.


  Definition lt (x y : t) := UnivExprSet.lt x y.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [] ?; now eapply irreflexivity.
    - intros [] [] [] ? ?; unfold lt in *. now etransitivity.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. red; intros; subst; reflexivity. Qed.


  Definition compare (e1 e2 : t) : comparison :=
    UnivExprSet.compare e1 e2.

  Definition eq_dec (e1 e2 : t) : {e1 = e2} +  {e1 <> e2}.
  Proof.
    destruct (UnivExprSet.eq_dec e1 e2) as [eq%UnivExprSet.eq_leibniz|neq].
    2: right; intros ?; now apply neq.
    left; destruct e1 as [e1 ne1]; destruct e2 as [e2 ne2]; cbn in *.
    revert ne1 ne2; rewrite eq; intros; f_equal; apply uip_bool.
  Qed.

  Lemma compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [] [].
    eapply CompareSpec_Proper.
    5: eapply UnivExprSet.compare_spec.
    4: reflexivity. 2,3: reflexivity.
    split. 1:now intros [= ->].
    cbn; intros ->%UnivExprSet.eq_leibniz; f_equal; apply uip_bool.
  Qed.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition eqb (e1 e2 : t) : bool :=
    UnivExprSet.equal e1.(t_set) e2.(t_set).

  Definition make' (e : UnivExpr.t) : t
    := {| t_set := UnivExprSet.singleton e;
          t_ne := eq_refl |}.

  (** Create a universe representing the given level. *)
  Definition make (l : Level.t) : t :=
    make' (UnivExpr.make l).

  Definition of_expr e := make' e.

  Lemma not_Empty_is_empty s :
    ~ UnivExprSet.Empty s -> UnivExprSet.is_empty s = false.
  Proof.
    intro H. apply not_true_is_false. intro H'.
    apply H. now apply UnivExprSetFact.is_empty_2 in H'.
  Qed.

  Program Definition add (e : UnivExpr.t) (u : t) : t
    := {| t_set := UnivExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply UnivExprSet.add_spec.
    left; reflexivity.
  Qed.

  #[deprecated(note="use add instead")]
  Notation add_to_exprs := add.

  Lemma add_spec e u e' :
    UnivExprSet.In e' (add e u) <-> e' = e \/ UnivExprSet.In e' u.
  Proof.
    apply UnivExprSet.add_spec.
  Qed.

  Definition add_list : list UnivExpr.t -> t -> t
    := List.fold_left (fun u e => add e u).

  Lemma add_list_spec l u e :
    UnivExprSet.In e (add_list l u) <-> In e l \/ UnivExprSet.In e u.
  Proof.
    unfold add_list. rewrite <- fold_left_rev_right.
    etransitivity. 2:{ eapply or_iff_compat_r. etransitivity.
                       2: apply @InA_In_eq with (A:=UnivExpr.t).
                       eapply InA_rev. }
    induction (List.rev l); cbn.
    - split. intuition. intros [H|H]; tas. invs H.
    - split.
      + intro H. apply add_spec in H. destruct H as [H|H].
        * left. now constructor.
        * apply IHl0 in H. destruct H as [H|H]; [left|now right].
          now constructor 2.
      + intros [H|H]. inv H.
        * apply add_spec; now left.
        * apply add_spec; right. apply IHl0. now left.
        * apply add_spec; right. apply IHl0. now right.
  Qed.

  #[deprecated(note="Use add_list instead")]
  Notation add_list_to_exprs := add_list.

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
      UnivExprSet.for_all UnivExpr.is_level u.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (UnivExprSet.cardinal u =? 1)%nat && is_levels u.

  Definition is_small (u : t) : bool :=
    UnivExprSet.for_all UnivExpr.is_small u .

  #[deprecated(note="Should only be used for predicative sorts")]
  Notation is_sprop := (fun (u : t) => false).

  #[deprecated(note="Should only be used for predicative sorts")]
  Notation is_prop := (fun (u : t) => false).

  Definition type0 : t := make Level.lSet.
  Definition type1 : t := make' UnivExpr.type1.

  (* Used for quoting. *)
  Definition from_kernel_repr (e : Level.t * bool) (es : list (Level.t * bool)) : t
    := add_list (map UnivExpr.from_kernel_repr es)
                (make' (UnivExpr.from_kernel_repr e)).


  (** The non empty / sorted / without dup list of univ expressions, the
      components of the pair are the head and the tail of the (non empty) list *)
  Program Definition exprs (u : t) : UnivExpr.t * list UnivExpr.t
    := match UnivExprSet.elements u with
       | [] => False_rect _ _
       | e :: l => (e, l)
       end.
  Next Obligation.
    destruct u as [u1 u2]; cbn in *. revert u2.
    apply eq_true_false_abs.
    unfold UnivExprSet.is_empty, UnivExprSet.Raw.is_empty,
    UnivExprSet.elements, UnivExprSet.Raw.elements in *.
    rewrite <- Heq_anonymous; reflexivity.
  Qed.

  Lemma exprs_make' e : exprs (make' e) = (e, []).
  Proof. reflexivity. Defined.

  (* Lemma exprs_make l : Universe.exprs (Universe.make l) = (UnivExpr.make l, []). *)
  (* Proof. reflexivity. Defined. *)


  Lemma exprs_spec u :
    let '(e, u') := exprs u in
    e :: u' = UnivExprSet.elements u.
  Proof.
    destruct u as [u1 u2].
    pose (l := UnivExprSet.elements u1).
    change (let '(e, u') :=
                match l return l = UnivExprSet.elements u1 -> _ with
                | [] => fun Heq_anonymous : [] = _ u1 =>
                    False_rect (UnivExpr.t × list UnivExpr.t)
                               (exprs_obligation_1
                                  {| t_set := u1; t_ne := u2 |}
                                  Heq_anonymous)
                | e :: l0 => fun _ : e :: l0 = _ u1 => (e, l0)
                end eq_refl in e :: u' = UnivExprSet.elements  u1).
    set (e := eq_refl). clearbody e. change (l = UnivExprSet.elements u1) in e.
    destruct l.
    - exfalso. revert u2. apply eq_true_false_abs.
      unfold UnivExprSet.is_empty, UnivExprSet.Raw.is_empty,
      UnivExprSet.elements, UnivExprSet.Raw.elements in *.
      rewrite <- e; reflexivity.
    - assumption.
  Qed.

  Lemma exprs_spec' u :
    (exprs u).1 :: (exprs u).2 = UnivExprSet.elements u.
  Proof.
    pose proof (exprs_spec u).
    now destruct (exprs u).
  Qed.

  Lemma In_exprs (u : t) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (exprs u).1 \/ In e (exprs u).2.
  Proof.
    etransitivity. symmetry. apply UnivExprSet.elements_spec1.
    pose proof (exprs_spec' u) as H.
    destruct (exprs u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_exprs_rev (u : t) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (exprs u).1 \/ In e (List.rev (exprs u).2).
  Proof.
    etransitivity. eapply In_exprs.
    apply or_iff_compat_l. apply in_rev.
  Qed.

  Definition map (f : UnivExpr.t -> UnivExpr.t) (u : t) : t :=
    let '(e, l) := exprs u in
    add_list (List.map f l) (make' (f e)).

  Lemma map_spec f u e :
    UnivExprSet.In e (map f u) <-> exists e0, UnivExprSet.In e0 u /\ e = (f e0).
  Proof.
    unfold map. symmetry. etransitivity.
    { eapply iff_ex; intro. eapply and_iff_compat_r. eapply In_exprs. }
    destruct (exprs u) as [e' l]; cbn in *.
    symmetry. etransitivity. eapply add_list_spec.
    etransitivity. eapply or_iff_compat_l. apply UnivExprSet.singleton_spec.
    etransitivity. eapply or_iff_compat_r.
    apply in_map_iff. clear u. split.
    - intros [[e0 []]|H].
      + exists e0. split. right; tas. congruence.
      + exists e'. split; tas. left; reflexivity.
    - intros [xx [[H|H] ?]].
      + right. congruence.
      + left. exists xx. split; tas; congruence.
  Qed.

  (** The universe strictly above FOR TYPING (not cumulativity) *)

  Definition super (l : t) : t :=
    map UnivExpr.succ l.

  (** The l.u.b. of 2 non-prop universe sets *)
  Program Definition sup (u v : t) : t :=
    {| t_set := UnivExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: UnivExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply UnivExprSet.union_spec. now left. }
    apply UnivExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.


  Definition get_univ_exprs (u : t) (H1 : is_prop u = false) (H2 : is_sprop u = false) : t.
  Proof. easy. Defined.

  (** Type of a product *)
  Definition level_of_product (domsort rangsort : t) :=
    sup domsort rangsort.

  Lemma eqb_refl u : eqb u u.
  Proof.
    destruct u;auto.
    now apply UnivExprSet.equal_spec.
  Qed.

  Lemma elements_not_empty (u : t) : UnivExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold UnivExprSet.is_empty, UnivExprSet.elements,
    UnivExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
  Qed.

  Definition get_is_level (u : t) : option Level.t :=
    match UnivExprSet.elements u with
      [(l, 0%nat)] => Some l
    | _ => None
    end.

  Global Instance Evaluable' : Evaluable t
    := fun v u => let '(e, u) := exprs u in
               List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  Lemma val_make' v e
    : val v (make' e) = val v e.
  Proof.
    reflexivity.
  Qed.

  Lemma make_inj x y :
    make x = make y -> x = y.
  Proof.
    destruct x, y; try now inversion 1.
  Qed.

End UniverseLevel.

#[deprecated(note="No more propositional levels")]
Notation is_propositional u := (fun u => false).

(** This coercion allows to see the universes as a [UnivExprSet.t] *)
Coercion UniverseLevel.t_set : UniverseLevel.t_ >-> UnivExprSet.t.

Declare Scope univ_scope.
Delimit Scope univ_scope with u.


(** ** Properties of valuation on universe levels *)

Ltac u :=
 change LevelSet.elt with Level.t in *;
 change UnivExprSet.elt with UnivExpr.t in *.

Lemma val_fold_right (u : UniverseLevel.t) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (UniverseLevel.exprs u).1)
                       (List.rev (UniverseLevel.exprs u).2).
Proof.
  unfold val at 1, UniverseLevel.Evaluable'.
  destruct (UniverseLevel.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : UniverseLevel.t) v e :
  UnivExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply UniverseLevel.In_exprs_rev in H. destruct (UniverseLevel.exprs u); cbn in *.
  clear -H. destruct H as [H|H].
  - subst. induction (List.rev l); cbnr; lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : UniverseLevel.t) v :
  exists e, UnivExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply UniverseLevel.In_exprs_rev. }
  rewrite val_fold_right. destruct (UniverseLevel.exprs u) as [e l]; cbn in *.
  clear. induction (List.rev l); cbn.
  - exists e. split; cbnr. left; reflexivity.
  - destruct IHl0 as [e' [H1 H2]].
    destruct (Nat.max_dec (val v a) (fold_right (fun e0 x0 => Nat.max (val v e0) x0)
                                               (val v e) l0)) as [H|H];
      rewrite H; clear H.
    + exists a. split; cbnr. right. now constructor.
    + rewrite <- H2. exists e'. split; cbnr.
      destruct H1 as [H1|H1]; [now left|right]. now constructor 2.
Qed.

Lemma val_ge_caract (u : UniverseLevel.t) v k :
  (forall e, UnivExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply UniverseLevel.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (UniverseLevel.exprs u) as [e l]; cbn; clear.
    induction (List.rev l); cbn.
    + intros H. apply H. left; reflexivity.
    + intros H.
      destruct (Nat.max_dec (val v a) (fold_right (fun e0 x => Nat.max (val v e0) x)
                                                 (val v e) l0)) as [H'|H'];
        rewrite H'; clear H'.
      * apply H. right. now constructor.
      * apply IHl0. intros x [H0|H0]; apply H. now left.
        right; now constructor 2.
  - intros H e He. eapply val_In_le in He. etransitivity; eassumption.
Qed.

Lemma val_le_caract (u : UniverseLevel.t) v k :
  (exists e, UnivExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply UniverseLevel.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (UniverseLevel.exprs u) as [e l]; cbn; clear.
    induction (List.rev l); cbn.
    + intros H. destruct H as [e' [[H1|H1] H2]].
      * now subst.
      * invs H1.
    + intros [e' [[H1|H1] H2]].
      * forward IHl0; [|lia]. exists e'. split; tas. left; assumption.
      * invs H1.
        -- u; lia.
        -- forward IHl0; [|lia]. exists e'. split; tas. right; assumption.
  - intros H. destruct (val_In_max u v) as [e [H1 H2]].
    exists e. rewrite H2; split; assumption.
Qed.



Lemma val_caract (u : UniverseLevel.t) v k :
  val v u = k
  <-> (forall e, UnivExprSet.In e u -> val v e <= k)
    /\ exists e, UnivExprSet.In e u /\ val v e = k.
Proof.
  split.
  - intros <-; split.
    + apply val_In_le.
    + apply val_In_max.
  - intros [H1 H2].
    apply val_ge_caract in H1.
    assert (k <= val v u); [clear H1|lia].
    apply val_le_caract. destruct H2 as [e [H2 H2']].
    exists e. split; tas. lia.
Qed.

Lemma val_add v e s
  : val v (UniverseLevel.add e s) = Nat.max (val v e) (val v s).
Proof.
  apply val_caract. split.
  - intros e' H. apply UnivExprSet.add_spec in H. destruct H as [H|H].
    + subst. u; lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v e) (val v s)) as [H|H]; rewrite H; clear H.
    + exists e. split; cbnr. apply UnivExprSetFact.add_1. reflexivity.
    + destruct (val_In_max s v) as [e' [H1 H2]].
      exists e'. split; tas. now apply UnivExprSetFact.add_2.
Qed.

Lemma val_sup v s1 s2 :
  val v (UniverseLevel.sup s1 s2) = Nat.max (val v s1) (val v s2).
Proof.
  eapply val_caract. cbn. split.
  - intros e' H. eapply UnivExprSet.union_spec in H. destruct H as [H|H].
    + eapply val_In_le with (v:=v) in H. lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v s1) (val v s2)) as [H|H]; rewrite H; clear H.
    + destruct (val_In_max s1 v) as [e' [H1 H2]].
      exists e'. split; tas. apply UnivExprSet.union_spec. now left.
    + destruct (val_In_max s2 v) as [e' [H1 H2]].
      exists e'. split; tas. apply UnivExprSet.union_spec. now right.
Qed.

(* 
Lemma val_zero_exprs v (l : Universe.t0) : 0 <= val v l.
Proof.
  rewrite val_fold_right.
  destruct (Universe.exprs l) as [e u']; clear l; cbn.
  induction (List.rev u'); simpl.
  - destruct e as [npl_expr].
    destruct npl_expr as [t b].
    cbn.
    assert (0 <= val v t) by apply Level.val_zero.
    destruct b;lia.
  - pose proof (UnivExpr.val_zero a v); lia.
Qed. *)

(** ** Extensionality lemmas on universe levels *)

Lemma eq_univ (u v : UniverseLevel.t) :
  u = v :> UnivExprSet.t -> u = v.
Proof.
  destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
  now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma eq_univ' (u v : UniverseLevel.t) :
  UnivExprSet.Equal u v -> u = v.
Proof.
  intro H. now apply eq_univ, UnivExprSet.eq_leibniz.
Qed.

Lemma eq_univ'' (u v : UniverseLevel.t) :
  UnivExprSet.elements u = UnivExprSet.elements v -> u = v.
Proof.
  intro H. apply eq_univ.
  destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
  destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
  destruct H. now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma eq_universe_iff (u v : UniverseLevel.t) :
  u = v <-> u = v :> UnivExprSet.t.
Proof.
  destruct u, v; cbn; split. now inversion 1.
  intros ->. f_equal. apply uip_bool.
Qed.

Lemma eq_universe_iff' (u v : UniverseLevel.t) :
  u = v <-> UnivExprSet.elements u = UnivExprSet.elements v.
Proof.
  etransitivity. apply eq_universe_iff.
  destruct u as [[u1 u2] ?], v as [[v1 v2] ?]; cbn; clear; split.
  now inversion 1. intros ->. f_equal. apply uip_bool.
Qed.


Lemma get_is_level_correct u l :
  UniverseLevel.get_is_level u = Some l -> u = UniverseLevel.make l.
Proof.
  intro H.
  destruct u.
  cbn in *.
  unfold UniverseLevel.make, UniverseLevel.make'.
  unfold UniverseLevel.get_is_level in H.
  destruct (UnivExprSet.elements _) as [|l0 L] eqn:Hu1; [discriminate|].
  destruct l0, L; try discriminate.
  * destruct n;inversion H;subst.
    apply eq_univ'';unfold UnivExpr.make.
    cbn. simpl in Hu1. rewrite Hu1. reflexivity.
  * destruct e,n;inversion H;subst.
Qed.

Lemma univ_expr_eqb_true_iff (u v : UniverseLevel.t) :
  UnivExprSet.equal u v <-> u = v.
Proof.
  split.
  - intros.
    apply eq_univ'. now apply UnivExprSet.equal_spec.
  - intros ->. now apply UnivExprSet.equal_spec.
Qed.

Lemma eqb_true_iff u v :
  UniverseLevel.eqb u v <-> u = v.
Proof.
  split. 2: intros ->; apply UniverseLevel.eqb_refl.
  intro H.
  destruct u,v;auto;try discriminate.
  now apply univ_expr_eqb_true_iff.
Qed.


(** ** Lemmas on for_all *)

Ltac proper := let H := fresh in try (intros ? ? H; destruct H; reflexivity).

Lemma for_all_elements (P : UnivExpr.t -> bool) u :
  UnivExprSet.for_all P u = forallb P (UnivExprSet.elements u).
Proof.
  apply UnivExprSetFact.for_all_b; proper.
Qed.

Lemma UnivExprSet_for_all_false f u :
  UnivExprSet.for_all f u = false -> UnivExprSet.exists_ (negb ∘ f) u.
Proof.
  intro H. rewrite UnivExprSetFact.exists_b.
  rewrite UnivExprSetFact.for_all_b in H.
  all: try now intros x y [].
  induction (UnivExprSet.elements u); cbn in *; [discriminate|].
  apply andb_false_iff in H; apply orb_true_iff; destruct H as [H|H].
  left; now rewrite H.
  right; now rewrite IHl.
Qed.

Lemma UnivExprSet_For_all_exprs (P : UnivExpr.t -> Prop) (u : UniverseLevel.t)
  : UnivExprSet.For_all P u
    <-> P (UniverseLevel.exprs u).1 /\ Forall P (UniverseLevel.exprs u).2.
Proof.
  etransitivity.
  - eapply iff_forall; intro e. eapply imp_iff_compat_r.
    apply UniverseLevel.In_exprs.
  - cbn; split.
    + intro H. split. apply H. now left.
      apply Forall_forall. intros x H0.  apply H; now right.
    + intros [H1 H2] e [He|He]. subst e; tas.
      eapply Forall_forall in H2; tea.
Qed.



(** ** Lemmas on sup of two universe levels *)

Lemma sup_comm x1 x2 :
  UniverseLevel.sup x1 x2 = UniverseLevel.sup x2 x1.
Proof.
  apply eq_univ'; simpl. unfold UnivExprSet.Equal.
  intros H. rewrite !UnivExprSet.union_spec. intuition.
Qed.


(** ** Constraints on universe levels *)

Module UnivConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.
  Definition t := t_.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition Le0 := Le 0.
  Definition Lt := Le 1.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X. lia.
    - intros ? ? ? X Y; invs X; invs Y; constructor. lia.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | Le n, Le m => Z.compare n m
    | Le _, Eq => Datatypes.Lt
    | Eq, Eq => Datatypes.Eq
    | Eq, _  => Datatypes.Gt
    end.

  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y; repeat constructor. simpl.
    destruct (Z.compare_spec z z0); simpl; constructor.
    subst; constructor. now constructor. now constructor.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality.
    apply Z.eq_dec.
  Qed.
End UnivConstraintType.

Module UnivConstraint.
  Definition t : Set := Level.t * UnivConstraintType.t * Level.t.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : UnivConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X; subst;
        try (eapply Level.lt_strorder; eassumption).
      eapply UnivConstraintType.lt_strorder; eassumption.
    - intros ? ? ? X Y; invs X; invs Y; constructor; tea.
      etransitivity; eassumption.
      2: etransitivity; eassumption.
      eapply UnivConstraintType.lt_strorder; eassumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      Pos.switch_Eq (Pos.switch_Eq (Level.compare l2 l2')
                                   (UnivConstraintType.compare t t'))
                    (Level.compare l1 l1').

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x as [[l1 t] l2], y as [[l1' t'] l2']; cbn.
    destruct (Level.compare_spec l1 l1'); cbn; repeat constructor; tas.
    invs H.
    destruct (UnivConstraintType.compare_spec t t'); cbn; repeat constructor; tas.
    invs H.
    destruct (Level.compare_spec l2 l2'); cbn; repeat constructor; tas.
    invs H. reflexivity.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. repeat decide equality.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End UnivConstraint.

Module UnivConstraintSet := MSetList.MakeWithLeibniz UnivConstraint.
Module UnivConstraintSetFact := WFactsOn UnivConstraint UnivConstraintSet.
Module UnivConstraintSetProp := WPropertiesOn UnivConstraint UnivConstraintSet.



