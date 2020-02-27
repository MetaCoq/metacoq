From Coq Require Import Ascii String ZArith List Bool Lia.
From Coq Require Import MSetList MSetFacts MSetProperties RelationClasses.
From MetaCoq.Template Require Import utils BasicAst config.
Import ListNotations.

Local Open Scope Z_scope.

(** * Valuations *)

(** A valuation is a universe level (nat) given for each
    universe variable (Level.t).
    It is >= for polymorphic universes and > 0 for monomorphic universes. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Class Evaluable (A : Type) := val : valuation -> A -> Z.

Module Level.
  Inductive t_ : Set :=
  | lProp
  | lSet
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices *).

  Definition t := t_.

  Definition is_small (x : t) :=
    match x with
    | lProp | lSet => true
    | _ => false
    end.

  Definition is_prop (x : t) :=
    match x with
    | lProp => true
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
               | lProp => -1
               | lSet => 0
               | Level s => Z.pos (v.(valuation_mono) s)
               | Var x => Z.of_nat (v.(valuation_poly) x)
               end.


  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lProp, lProp => Eq
    | lProp, _ => Lt
    | _, lProp => Gt
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
  | ltPropSet : lt_ lProp lSet
  | ltPropLevel s : lt_ lProp (Level s)
  | ltPropVar n : lt_ lProp (Var n)
  | ltSetLevel s : lt_ lSet (Level s)
  | ltSetVar n : lt_ lSet (Var n)
  | ltLevelLevel s s' : string_lt s s' -> lt_ (Level s) (Level s')
  | ltLevelVar s n : lt_ (Level s) (Var n)
  | ltVarVar n n' : Nat.lt n n' -> lt_ (Var n) (Var n').

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [| | |] X; inversion X.
      eapply string_lt_irreflexive; tea.
      eapply Nat.lt_irrefl; tea.
    - intros [| | |] [| | |] [| | |] X1 X2;
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


(** no prop levels are levels which are Set or Level or Var *)
Module NoPropLevel.
  Inductive t_ := lSet |  Level (_ : string) | Var (_ : nat).

  Definition t : Set := t_.

  Global Instance Level_Evaluable : Evaluable t
    := fun v l => match l with
               | lSet => 0
               | Level s => Z.pos (v.(valuation_mono) s)
               | Var x => Z.of_nat (v.(valuation_poly) x)
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

  Definition eq : t -> t -> Prop := Logic.eq.

  Definition eq_equiv : RelationClasses.Equivalence eq := _.

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

  Global Instance lt_strorder : StrictOrder lt.
    split.
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

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition of_level (l : Level.t) : option t :=
    match l with
    | Level.lProp => None
    | Level.lSet => Some lSet
    | Level.Level s => Some (Level s)
    | Level.Var n => Some (Var n)
    end.

  Definition to_level (l : t) : Level.t :=
    match l with
    | lSet => Level.lSet
    | Level s => Level.Level s
    | Var n => Level.Var n
    end.

  Lemma of_to_level l
    : of_level (to_level l) = Some l.
  Proof.
    destruct l; reflexivity.
  Qed.

  Definition is_small (e : t) : bool :=
    match e with
    | lSet => true
    | _ => false
    end.

  Lemma val_to_level v l :
    val v (to_level l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_zero l v : 0 <= val v l.
  Proof.
    destruct l; cbn; lia.
  Qed.
End NoPropLevel.

Coercion NoPropLevel.to_level : NoPropLevel.t >-> Level.t.


Module UnivExpr.
  (* npe = no prop expression, +1 if true *)
  Inductive t_ := lProp | npe (e : NoPropLevel.t * bool).

  Definition t := t_.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | lProp => -1
               | npe (l, b) => (if b then 1 else 0) + val v l
               end.


  Definition is_small (e : t) : bool :=
    match e with
    | lProp
    | npe (NoPropLevel.lSet, false) => true
    | _  => false
    end.

  Definition is_level (e : t) : bool :=
    match e with
    | lProp
    | npe (_, false) => true
    | _  => false
    end.

  Definition is_prop (e : t) : bool :=
    match e with
    | lProp => true
    | _  => false
    end.

  Definition get_level (e : t) : Level.t :=
    match e with
    | lProp => Level.lProp
    | npe (l, _) => l
    end.

  Definition get_noprop (e : UnivExpr.t) :=
    match e with
    | lProp => None
    | npe (l, _) => Some l
    end.

  Definition make (l : Level.t) : t :=
    match NoPropLevel.of_level l with
    | None => lProp
    | Some l => npe (l, false)
    end.

  Definition prop : t := lProp.
  Definition set : t := npe (NoPropLevel.lSet, false).
  Definition type1 : t := npe (NoPropLevel.lSet, true).

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltUnivExpr0 e : lt_ lProp (npe e)
  | ltUnivExpr1 l : lt_ (npe (l, false)) (npe (l, true))
  | ltUnivExpr2 l l' b b' : NoPropLevel.lt l l' -> lt_ (npe (l, b)) (npe (l', b')).

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X.
      eapply NoPropLevel.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2; now rewrite H1, H2.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | lProp, lProp => Eq
    | lProp, _ => Lt
    | _, lProp => Gt
    | npe (l1, b1), npe (l2, b2) =>
      match NoPropLevel.compare l1 l2 with
      | Eq => bool_compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [|[]] [|[]]; cbn; repeat constructor.
    destruct (NoPropLevel.compare_spec t0 t1); repeat constructor; tas.
    subst. destruct b, b0; repeat constructor.
  Qed.

  Definition eq_dec (l1 l2 : t) : {l1 = l2} + {l1 <> l2}.
  Proof.
    repeat decide equality.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.


  Lemma val_make v l
    : val v (UnivExpr.make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_make_npl v (l : NoPropLevel.t)
    : val v (UnivExpr.make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_minus_one e v : -1 <= val v e.
  Proof.
    destruct e as [|[[] b]]; cbn; try destruct b; lia.
  Qed.

  Lemma is_prop_val e : is_prop e -> forall v, val v e = -1.
  Proof.
    destruct e as [|[[] []]]; cbn; try reflexivity; try discriminate.
  Qed.

  Lemma val_is_prop e v : val v e <= -1 -> is_prop e.
  Proof.
    destruct e as [|[[] b]]; cbnr; try destruct b; lia.
  Qed.

  Lemma is_prop_val_false e :
    is_prop e = false -> forall v, 0 <= val v e.
  Proof.
    intros He v.
    pose proof (val_is_prop e v).
    pose proof (val_minus_one e v).
    destruct (Z_le_gt_dec (val v e) (-1)); [|lia].
    forward H; tas. rewrite He in H; discriminate.
  Qed.

  Lemma val_is_prop_false e v :
    0 <= val v e -> is_prop e = false.
  Proof.
    pose proof (is_prop_val e) as H. destruct (is_prop e); cbnr.
    rewrite (H eq_refl v). lia.
  Qed.
End UnivExpr.

Module UnivExprSet := MSetList.MakeWithLeibniz UnivExpr.
Module UnivExprSetFact := WFactsOn UnivExpr UnivExprSet.
Module UnivExprSetProp := WPropertiesOn UnivExpr UnivExprSet.


Module Universe.
  (** A universe is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty *)
  Record t := { t_set : UnivExprSet.t ;
                t_ne  : UnivExprSet.is_empty t_set = false }.

  Coercion t_set : t >-> UnivExprSet.t.

  Definition eqb (u1 u2 : t) : bool :=
    UnivExprSet.equal u1.(t_set) u2.(t_set).

  Definition make' (e : UnivExpr.t) : t
    := {| t_set := UnivExprSet.singleton e;
          t_ne := eq_refl |}.

  (** Create a universe representing the given level. *)
  Definition make (l : Level.t) : t := make' (UnivExpr.make l).

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

  Definition make'' (e : UnivExpr.t) (l : list UnivExpr.t) : t
    := add_list l (make' e).

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels : t -> bool
    := UnivExprSet.for_all UnivExpr.is_level.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (UnivExprSet.cardinal u =? 1)%nat &&  is_levels u.

  Definition is_small  : t -> bool :=
    UnivExprSet.for_all UnivExpr.is_small.

  Definition is_prop  : t -> bool :=
    UnivExprSet.for_all UnivExpr.is_prop.

  Definition type0m : t := make Level.lProp.
  Definition type0 : t := make Level.lSet.
  Definition type1 : t := make' UnivExpr.type1.

  (** The universe strictly above FOR TYPING (not cumulativity) *)
  Definition super (l : Level.t) : t :=
    match NoPropLevel.of_level l with
    | None => type1
    | Some NoPropLevel.lSet => type1
    | Some l => make' (UnivExpr.npe (l, true))
    end.

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

  Lemma exprs_make' e : Universe.exprs (Universe.make' e) = (e, []).
  Proof. reflexivity. Defined.

  Lemma exprs_make l : Universe.exprs (Universe.make l) = (UnivExpr.make l, []).
  Proof. reflexivity. Defined.


  Lemma exprs_spec u :
    let '(e, u') := Universe.exprs u in
    e :: u' = UnivExprSet.elements u.
  Proof.
    destruct u as [u1 u2].
    pose (l := UnivExprSet.elements u1).
    change (let '(e, u') :=
                match l return l = UnivExprSet.elements u1 -> _ with
                | [] => fun Heq_anonymous : [] = _ u1 =>
                    False_rect (UnivExpr.t × list UnivExpr.t)
                               (exprs_obligation_1
                                  {| Universe.t_set := u1; Universe.t_ne := u2 |}
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
    (Universe.exprs u).1 :: (Universe.exprs u).2 = UnivExprSet.elements u.
  Proof.
    pose proof (exprs_spec u).
    now destruct (Universe.exprs u).
  Qed.

  (* Lemma exprs_spec'' u : *)
  (*   (Universe.exprs u).1 :: (Universe.exprs u).2 = UnivExprSet.this u.(t_set). *)
  (* Proof. *)
  (*   apply exprs_spec'. *)
  (* Qed. *)

  Lemma In_exprs (u : t) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (Universe.exprs u).1 \/ In e (Universe.exprs u).2.
  Proof.
    etransitivity. symmetry. apply UnivExprSet.elements_spec1.
    pose proof (Universe.exprs_spec' u) as H.
    destruct (Universe.exprs u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_exprs_rev (u : t) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (Universe.exprs u).1 \/ In e (List.rev (Universe.exprs u).2).
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

  Definition try_suc
    := map (fun l => match l with
                  | UnivExpr.lProp => UnivExpr.type1
                  | UnivExpr.npe (l, _) => UnivExpr.npe (l, true)
                  end).

  (** The l.u.b. of 2 universes *)
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

  (** Type of a product *)
  Definition sort_of_product (domsort rangsort : t) :=
    (* Prop impredicativity *)
    if Universe.is_prop rangsort then rangsort
    else Universe.sup domsort rangsort.

  Lemma eqb_refl u : eqb u u.
  Proof.
    apply UnivExprSet.equal_spec. reflexivity.
  Qed.

  Lemma elements_not_empty (u : Universe.t) : UnivExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold UnivExprSet.is_empty, UnivExprSet.elements,
    UnivExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
  Qed.

  Global Instance Evaluable : Evaluable t
    := fun v u => let '(e, u) := Universe.exprs u in
               List.fold_left (fun n e => Z.max (val v e) n) u (val v e).

  Lemma val_make' v e
    : val v (make' e) = val v e.
  Proof.
    reflexivity.
  Qed.

  Lemma val_make v l
    : val v (make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_make_npl v (l : NoPropLevel.t)
    : val v (make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.
End Universe.

(** This coercion allows to see the universes as a [UnivExprSet.t] *)
Coercion Universe.t_set : Universe.t >-> UnivExprSet.t.


Ltac u :=
 change LevelSet.elt with Level.t in *;
 change UnivExprSet.elt with UnivExpr.t in *.
 (* change ConstraintSet.elt with UnivConstraint.t in *. *)


Lemma val_fold_right (u : Universe.t) v :
  val v u = fold_right (fun e x => Z.max (val v e) x) (val v (Universe.exprs u).1)
                       (List.rev (Universe.exprs u).2).
Proof.
  unfold val at 1, Universe.Evaluable.
  destruct (Universe.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : Universe.t) v e :
  UnivExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply Universe.In_exprs_rev in H. destruct (Universe.exprs u); cbn in *.
  clear -H. destruct H as [H|H].
  - subst. induction (List.rev l); cbnr; lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : Universe.t) v :
  exists e, UnivExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply Universe.In_exprs_rev. }
  rewrite val_fold_right. destruct (Universe.exprs u) as [e l]; cbn in *.
  clear. induction (List.rev l); cbn.
  - exists e. split; cbnr. left; reflexivity.
  - destruct IHl0 as [e' [H1 H2]].
    destruct (Z.max_dec (val v a) (fold_right (fun e0 x0 => Z.max (val v e0) x0)
                                               (val v e) l0)) as [H|H];
      rewrite H; clear H.
    + exists a. split; cbnr. right. now constructor.
    + rewrite <- H2. exists e'. split; cbnr.
      destruct H1 as [H1|H1]; [now left|right]. now constructor 2.
Qed.

Lemma val_ge_caract (u : Universe.t) v k :
  (forall e, UnivExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply Universe.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (Universe.exprs u) as [e l]; cbn; clear.
    induction (List.rev l); cbn.
    + intros H. apply H. left; reflexivity.
    + intros H.
      destruct (Z.max_dec (val v a) (fold_right (fun e0 x => Z.max (val v e0) x)
                                                 (val v e) l0)) as [H'|H'];
        rewrite H'; clear H'.
      * apply H. right. now constructor.
      * apply IHl0. intros x [H0|H0]; apply H. now left.
        right; now constructor 2.
  - intros H e He. eapply val_In_le in He. etransitivity; eassumption.
Qed.

Lemma val_le_caract (u : Universe.t) v k :
  (exists e, UnivExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply Universe.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (Universe.exprs u) as [e l]; cbn; clear.
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


Lemma val_caract (u : Universe.t) v k :
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
  : val v (Universe.add e s) = Z.max (val v e) (val v s).
Proof.
  apply val_caract. split.
  - intros e' H. apply UnivExprSet.add_spec in H. destruct H as [H|H].
    + subst. u; lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Z.max_dec (val v e) (val v s)) as [H|H]; rewrite H; clear H.
    + exists e. split; cbnr. apply UnivExprSetFact.add_1. reflexivity.
    + destruct (val_In_max s v) as [e' [H1 H2]].
      exists e'. split; tas. now apply UnivExprSetFact.add_2.
Qed.

Lemma val_sup v s1 s2 :
  val v (Universe.sup s1 s2) = Z.max (val v s1) (val v s2).
Proof.
  eapply val_caract. cbn. split.
  - intros e' H. eapply UnivExprSet.union_spec in H. destruct H as [H|H].
    + eapply val_In_le with (v:=v) in H. rewrite H; lia.
    + eapply val_In_le with (v:=v) in H. rewrite H; lia.
  - destruct (Z.max_dec (val v s1) (val v s2)) as [H|H]; rewrite H; clear H.
    + destruct (val_In_max s1 v) as [e' [H1 H2]].
      exists e'. split; tas. apply UnivExprSet.union_spec. now left.
    + destruct (val_In_max s2 v) as [e' [H1 H2]].
      exists e'. split; tas. apply UnivExprSet.union_spec. now right.
Qed.

Ltac proper := let H := fresh in try (intros ? ? H; destruct H; reflexivity).

Lemma for_all_elements (P : UnivExpr.t -> bool) u :
  UnivExprSet.for_all P u = forallb P (UnivExprSet.elements u).
Proof.
  apply UnivExprSetFact.for_all_b; proper.
Qed.

Lemma val_minus_one u v :
  (-1 <= val v u)%Z.
Proof.
  rewrite val_fold_right.
  destruct (Universe.exprs u) as [e u']; clear u; cbn.
  induction (List.rev u'); simpl.
  - apply UnivExpr.val_minus_one.
  - pose proof (UnivExpr.val_minus_one a v). lia.
Qed.

Lemma is_prop_val u :
  Universe.is_prop u -> forall v, val v u = -1.
Proof.
  unfold Universe.is_prop. rewrite for_all_elements.
  intros H v. rewrite val_fold_right.
  rewrite <- (Universe.exprs_spec' u) in H.
  destruct (Universe.exprs u) as [e l]; simpl in *.
  apply andb_true_iff in H; destruct H as [He H]; revert H.
  rewrite <- forallb_rev. induction (List.rev l); simpl.
  - intros _. apply UnivExpr.is_prop_val; assumption.
  - intro H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply UnivExpr.is_prop_val with (v:=v) in H1. now rewrite IHl0, H1.
Qed.

Lemma val_is_prop u v :
  val v u <= -1 -> Universe.is_prop u.
Proof.
  unfold Universe.is_prop. rewrite for_all_elements.
  rewrite val_fold_right.
  rewrite <- (Universe.exprs_spec' u).
  destruct (Universe.exprs u) as [e l]; simpl.
  rewrite <- forallb_rev.
  induction (List.rev l); cbn.
  - rewrite andb_true_r. apply UnivExpr.val_is_prop.
  - intro H. forward IHl0; [lia|].
    specialize (UnivExpr.val_is_prop a v) as H'. forward H'; [lia|].
    apply andb_true_iff. apply andb_true_iff in IHl0.
    intuition.
Qed.

Lemma is_prop_val_false u :
  Universe.is_prop u = false -> forall v, 0 <= val v u.
Proof.
  intros Hu v.
  pose proof (val_is_prop u v).
  pose proof (val_minus_one u v).
  destruct (Z_le_gt_dec (val v u) (-1)); [|lia].
  forward H; tas. rewrite Hu in H; discriminate.
Qed.

Lemma val_is_prop_false u v :
  0 <= val v u -> Universe.is_prop u = false.
Proof.
  pose proof (is_prop_val u) as H. destruct (Universe.is_prop u); cbnr.
  rewrite (H eq_refl v). lia.
Qed.


Lemma eq_univ (u v : Universe.t) :
  u = v :> UnivExprSet.t -> u = v.
Proof.
  destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
  now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma eq_univ' (u v : Universe.t) :
  UnivExprSet.Equal u v -> u = v.
Proof.
  intro H. now apply eq_univ, UnivExprSet.eq_leibniz.
Qed.

Lemma eq_univ'' (u v : Universe.t) :
  UnivExprSet.elements u = UnivExprSet.elements v -> u = v.
Proof.
  intro H. apply eq_univ.
  destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
  destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
  destruct H. now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma eqb_true_iff u v :
  Universe.eqb u v <-> u = v.
Proof.
  split. 2: intros ->; apply Universe.eqb_refl.
  intro H. apply eq_univ'. now apply UnivExprSet.equal_spec.
Qed.



(** Sort families *)

Inductive sort_family : Set := InProp | InSet | InType.

Definition leb_sort_family x y :=
  match x, y with
  | InProp, _ => true
  | InSet, InProp => false
  | InType, (InProp | InSet) => false
  | _, _ => true
  end.

(** Family of a universe [u]. *)
Definition universe_family (u : Universe.t) :=
  if Universe.is_prop u then InProp
  else if Universe.is_small u then InSet
  else InType.


Module ConstraintType.
  Inductive t_ : Set := Lt | Le | Eq.
  Definition t := t_.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | LtLe : lt_ Lt Le
  | LtEq : lt_ Lt Eq
  | LeEq : lt_ Le Eq.
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X.
    - intros ? ? ? X Y; invs X; invs Y; constructor.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | Lt, Lt => Datatypes.Eq
    | Lt, _  => Datatypes.Lt
    | Le, Lt => Datatypes.Gt
    | Le, Le => Datatypes.Eq
    | Le, Eq => Datatypes.Lt
    | Eq, Eq => Datatypes.Eq
    | Eq, _  => Datatypes.Gt
    end.

  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y; repeat constructor.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. decide equality.
  Qed.
End ConstraintType.

Module UnivConstraint.
  Definition t : Set := Level.t * ConstraintType.t * Level.t.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.

  Definition make l1 ct l2 : t := (l1, ct, l2).

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X; subst;
        try (eapply Level.lt_strorder; eassumption).
      eapply ConstraintType.lt_strorder; eassumption.
    - intros ? ? ? X Y; invs X; invs Y; constructor; tea.
      etransitivity; eassumption.
      2: etransitivity; eassumption.
      eapply ConstraintType.lt_strorder; eassumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros ? ? X ? ? Y; invs X; invs Y. reflexivity.
  Qed.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      Pos.switch_Eq (Pos.switch_Eq (Level.compare l2 l2')
                                   (ConstraintType.compare t t'))
                    (Level.compare l1 l1').

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x as [[l1 t] l2], y as [[l1' t'] l2']; cbn.
    destruct (Level.compare_spec l1 l1'); cbn; repeat constructor; tas.
    invs H.
    destruct (ConstraintType.compare_spec t t'); cbn; repeat constructor; tas.
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

Module ConstraintSet := MSetList.MakeWithLeibniz UnivConstraint.
Module ConstraintSetFact := WFactsOn UnivConstraint ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraint ConstraintSet.


(** {6 Universe instances} *)

Module Instance.

  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)
  Definition t : Set := list Level.t.

  Definition empty : t := [].
  Definition is_empty (i : t) : bool :=
    match i with
    | [] => true
    | _ => false
    end.

  Definition eqb (i j : t) :=
    forallb2 Level.eqb i j.

  Definition equal_upto (f : Level.t -> Level.t -> bool) (i j : t) :=
    forallb2 f i j.
End Instance.



Module UContext.
  Definition t := Instance.t × ConstraintSet.t.

  Definition make : Instance.t -> ConstraintSet.t -> t := pair.

  Definition empty : t := (Instance.empty, ConstraintSet.empty).

  Definition instance : t -> Instance.t := fst.
  Definition constraints : t -> ConstraintSet.t := snd.

  Definition dest : t -> Instance.t * ConstraintSet.t := fun x => x.
End UContext.

Module AUContext.
  Definition t := list ident × ConstraintSet.t.

  Definition make (ids : list ident) (ctrs : ConstraintSet.t) : t
    := (ids, ctrs).
  Definition repr '((u, cst) : t) : UContext.t :=
    (mapi (fun i _ => Level.Var i) u, cst).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (repr uctx)).
End AUContext.

Module ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.

  Definition empty : t := (LevelSet.empty, ConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && ConstraintSet.is_empty (snd uctx).
End ContextSet.


(* Variance info is needed to do full universe polymorphism *)
Module Variance.
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.

(** Universe info for cumulative inductive types: A context of
   universe levels with universe constraints, representing local
   universe variables and constraints, together with an array of
   Variance.t.

    This data structure maintains the invariant that the variance
   array has the same length as the universe instance. *)
Module ACumulativityInfo.
  Definition t := AUContext.t × list Variance.t.

  Definition make ctx var : t := (ctx, var).
  (* Definition empty : t := (AUContext.empty, nil). *)
  (* val is_empty : t -> bool *)

  Definition univ_context : t -> AUContext.t := fst.
  Definition variance : t -> list Variance.t := snd.

  (** This function takes a universe context representing constraints
     of an inductive and produces a CumulativityInfo.t with the
     trivial subtyping relation. *)
  (* val from_universe_context : UContext.t -> t *)

  (* val leq_constraints : t -> Instance.t constraint_function *)
  (* val eq_constraints : t -> Instance.t constraint_function *)
End ACumulativityInfo.


Inductive universes_decl : Type :=
| Monomorphic_ctx (ctx : ContextSet.t)
| Polymorphic_ctx (cst : AUContext.t)
| Cumulative_ctx (ctx : ACumulativityInfo.t).

Definition monomorphic_udecl u :=
  match u with
  | Monomorphic_ctx ctx => ctx
  | _ => ContextSet.empty
  end.

Definition monomorphic_levels φ := (monomorphic_udecl φ).1.
Definition monomorphic_constraints φ := (monomorphic_udecl φ).2.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => fst ctx
  | Polymorphic_ctx ctx
  | Cumulative_ctx (ctx, _) => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => snd ctx
  | Polymorphic_ctx ctx
  | Cumulative_ctx (ctx, _) => snd (AUContext.repr ctx)
  end.




Definition llt {cf:checker_flags} (x y : Z) : Prop :=
  if prop_sub_type then x < y else 0 <= x /\ x < y.

Notation "x < y" := (llt x y) : univ_scope.

Delimit Scope univ_scope with u.

Definition lle {cf:checker_flags} (x y : Z) : Prop :=
  (x < y)%u \/ x = y.

Notation "x <= y" := (lle x y) : univ_scope.

Ltac lle := unfold lle, llt in *.
Ltac lled := lle; match goal with
                  | H : prop_sub_type = true |- _ => rewrite H in *
                  | H : prop_sub_type = false |- _ => rewrite H in *
                  | H : is_true prop_sub_type |- _ => rewrite H in *
                  | _ => destruct prop_sub_type eqn:?Hb
                  end.


Section Univ.

Context {cf:checker_flags}.

  Global Instance lle_refl : Reflexive lle.
  Proof.
    intro x. now right.
  Qed.

  Global Instance llt_trans : Transitive llt.
  Proof.
    intros x y z; unfold llt; destruct prop_sub_type; lia.
  Qed.

  Global Instance lle_trans : Transitive lle.
  Proof.
    intros x y z [] []; subst; try (right; reflexivity); left; tas.
    etransitivity; eassumption.
  Qed.

  Lemma llt_lt n m : (n < m)%u -> (n < m)%Z.
  Proof. lled; lia. Qed.

  Lemma lle_le n m : (n <= m)%u -> (n <= m)%Z.
  Proof. lled; lia. Qed.

  Lemma lt_llt n m : prop_sub_type -> (n < m)%Z -> (n < m)%u.
  Proof. unfold llt. now intros ->. Qed.

  Lemma le_lle n m : prop_sub_type -> (n <= m)%Z -> (n <= m)%u.
  Proof. lled; [lia|discriminate]. Qed.

  Lemma lt_llt' n m : (0 <= n)%Z -> (n < m)%Z -> (n < m)%u.
  Proof. lled; lia. Qed.

  Lemma le_lle' n m : (0 <= n)%Z -> (n <= m)%Z -> (n <= m)%u.
  Proof. lled; lia. Qed.


  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) : (val v l < val v l')%u
                         -> satisfies0 v (l, ConstraintType.Lt, l')
  | satisfies0_Le (l l' : Level.t) : (val v l <= val v l')%u
                         -> satisfies0 v (l, ConstraintType.Le, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition eq_universe0 (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> val v u = val v u'.

  Definition leq_universe_n n (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Z.of_nat n + val v u <= val v u')%u.

  Definition leq_universe0 := leq_universe_n 0.
  Definition lt_universe := leq_universe_n 1.

  Definition eq_universe φ u u'
    := if check_univs then eq_universe0 φ u u' else True.

  Definition leq_universe φ u u'
    := if check_univs then leq_universe0 φ u u' else True.

  (* ctrs are "enforced" by φ *)

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Lemma valid_subset φ φ' ctrs
    : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof.
    unfold valid_constraints.
    destruct check_univs; [|trivial].
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.


  (** **** Lemmas about eq and leq **** *)

  (** We show that equality and inequality of universes form an equivalence and
      a partial order (one w.r.t. the other).
      We use classes from [CRelationClasses] for consistency with the rest of the
      development which uses relations in [Type] rather than [Prop].
      These definitions hence use [Prop <= Type]. *)

  Global Instance eq_universe0_refl φ : Reflexive (eq_universe0 φ).
  Proof.
    intros vH s; reflexivity.
  Qed.

  Global Instance eq_universe_refl φ : Reflexive (eq_universe φ).
  Proof.
    intro s.
    unfold eq_universe; destruct check_univs;
      [apply eq_universe0_refl|constructor].
  Qed.

  Global Instance leq_universe0_refl φ : Reflexive (leq_universe0 φ).
  Proof.
    intros s vH; reflexivity.
  Qed.

  Global Instance leq_universe_refl φ : Reflexive (leq_universe φ).
  Proof.
    intro s.
    unfold leq_universe; destruct check_univs;
      [apply leq_universe0_refl|constructor].
  Qed.

  Global Instance eq_universe0_sym φ : Symmetric (eq_universe0 φ).
  Proof.
    intros s s' e vH. symmetry ; eauto.
  Qed.

  Global Instance eq_universe_sym φ : Symmetric (eq_universe φ).
  Proof.
    unfold eq_universe. destruct check_univs ; eauto.
    eapply eq_universe0_sym.
  Qed.

  Global Instance eq_universe0_trans φ : Transitive (eq_universe0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h.
    etransitivity ; try eapply h1 ; eauto.
  Qed.

  Global Instance eq_universe_trans φ : Transitive (eq_universe φ).
  Proof.
    intros s1 s2 s3.
    unfold eq_universe. destruct check_univs ; auto.
    intros h1 h2.
    eapply eq_universe0_trans ; eauto.
  Qed.

  Global Instance leq_universe0_trans φ : Transitive (leq_universe0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h. etransitivity.
    - eapply h1. assumption.
    - eapply h2. assumption.
  Qed.

  Global Instance leq_universe_trans φ : Transitive (leq_universe φ).
  Proof.
    intros s1 s2 s3.
    unfold leq_universe. destruct check_univs ; auto.
    intros h1 h2.
    eapply leq_universe0_trans ; eauto.
  Qed.

  Lemma eq_leq_universe φ u u' :
    eq_universe0 φ u u' <-> leq_universe0 φ u u' /\ leq_universe0 φ u' u.
  Proof.
    split.
    intro H; split; intros v Hv; specialize (H v Hv); lled; lia.
    intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv); lled; lia.
  Qed.


  Lemma leq_universe0_sup_l φ s1 s2 :
    Universe.is_prop s1 = false -> leq_universe0 φ s1 (Universe.sup s1 s2).
  Proof.
    intros H v Hv. apply is_prop_val_false with (v:=v) in H.
    rewrite val_sup. unfold lle, llt. destruct prop_sub_type; lia.
  Qed.

  Lemma leq_universe0_sup_r φ s1 s2 :
    Universe.is_prop s2 = false -> leq_universe0 φ s2 (Universe.sup s1 s2).
  Proof.
    intros H v Hv. apply is_prop_val_false with (v:=v) in H.
    rewrite val_sup. unfold lle, llt. destruct prop_sub_type; lia.
  Qed.

  Lemma leq_universe0_sup_l' φ s1 s2 :
    prop_sub_type -> leq_universe0 φ s1 (Universe.sup s1 s2).
  Proof.
    intros H v Hv. rewrite val_sup. unfold lle, llt; rewrite H. lia.
  Qed.

  Lemma leq_universe0_sup_r' φ s1 s2 :
    prop_sub_type -> leq_universe0 φ s2 (Universe.sup s1 s2).
  Proof.
    intros H v Hv. rewrite val_sup. unfold lle, llt; rewrite H. lia.
  Qed.

  Lemma leq_universe_product φ s1 s2
    : leq_universe φ s2 (Universe.sort_of_product s1 s2).
  Proof.
    unfold leq_universe; destruct check_univs; [cbn|constructor].
    unfold Universe.sort_of_product; case_eq (Universe.is_prop s2); intro eq.
    apply leq_universe0_refl.
    now apply leq_universe0_sup_r.
  Qed.

  (* Rk: [leq_universe φ s1 (sort_of_product s1 s2)] does not hold due to
     impredicativity. *)

  Global Instance eq_universe_leq_universe φ : subrelation (eq_universe φ) (leq_universe φ).
  Proof.
    unfold eq_universe, leq_universe; destruct check_univs; [|intuition].
    intros u u' HH v Hv. rewrite (HH v Hv). reflexivity.
  Qed.

  Global Instance eq_universe0_equivalence φ : Equivalence (eq_universe0 φ) :=
     {| Equivalence_Reflexive := _ ;
        Equivalence_Symmetric := _;
        Equivalence_Transitive := _ |}.

  Global Instance eq_universe_equivalence φ : Equivalence (eq_universe φ) :=
     {| Equivalence_Reflexive := eq_universe_refl _ ;
        Equivalence_Symmetric := eq_universe_sym _;
        Equivalence_Transitive := eq_universe_trans _ |}.

  Global Instance leq_universe_preorder φ : PreOrder (leq_universe φ) :=
     {| PreOrder_Reflexive := leq_universe_refl _ ;
        PreOrder_Transitive := leq_universe_trans _ |}.

  Global Instance llt_str_order : StrictOrder llt.
  Proof.
    split.
    - intros x H. unfold llt in *; destruct prop_sub_type; lia.
    - exact _.
  Qed.

  Global Instance lle_antisym : Antisymmetric _ eq lle.
  Proof.
    intros t u [] []; subst; try reflexivity.
    exfalso; eapply llt_str_order; etransitivity; eassumption.
  Qed.

  Global Instance leq_universe0_antisym φ
    : Antisymmetric _ (eq_universe0 φ) (leq_universe0 φ).
  Proof.
    intros t u tu ut. unfold leq_universe0, eq_universe0 in *.
    red in tu, ut.
    intros v sat.
    specialize (tu _ sat).
    specialize (ut _ sat).
    simpl in tu, ut.
    apply lle_antisym; tea.
  Qed.

  Global Instance leq_universe_antisym φ
    : Antisymmetric _ (eq_universe φ) (leq_universe φ).
  Proof.
    intros t u tu ut. unfold leq_universe, eq_universe in *.
    destruct check_univs; [|trivial]. eapply leq_universe0_antisym; auto.
  Qed.

  Global Instance leq_universe_partial_order φ
    : PartialOrder (eq_universe φ) (leq_universe φ).
  Proof.
    intros x y; split. intros eqxy; split. now eapply eq_universe_leq_universe. red.
    now eapply eq_universe_leq_universe, symmetry.
    intros [l r]. now eapply leq_universe_antisym.
  Defined.


  Definition eq_universe_leq_universe' {cf} φ u u'
    := @eq_universe_leq_universe cf φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_universe_leq_universe' leq_universe_refl'.

End Univ.


(* This universe is a hack used in plugings to generate fresh universes *)
Definition fresh_universe : Universe.t. exact Universe.type0. Qed.
(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t. exact Level.lSet. Qed.
