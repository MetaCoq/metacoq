From Coq Require Import MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From Equations Require Import Equations.
From MetaCoq.Template Require Import utils BasicAst config.
Require Import ssreflect.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Implicit Types (cf : checker_flags).

Ltac absurd :=
  match goal with
  | [H: ~ True |- _] => elim (H I)
  | [H : False |- _] => elim H
  | H: is_true false |- _ => discriminate H
  | |- False -> _ => let H := fresh in intro H; elim H
  | |- _ -> False -> _ => let H := fresh in intros ? H; elim H
  | |- is_true false -> _ => let H := fresh in intro H; discriminate H
  | |- _ -> is_true false -> _ => let H := fresh in intros ? H; discriminate H
  end.
#[global]
Hint Extern 10 => absurd : core.

(** * Valuations *)

(** A valuation is a universe level (nat) given for each
    universe variable (Level.t).
    It is >= for polymorphic concreteUniverses and > 0 for monomorphic concreteUniverses. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Class Evaluable (A : Type) := val : valuation -> A -> nat.


(** Levels are Set or Level or Var *)
Module Level.
  Inductive t_ : Set :=
  | lzero
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices *).
  Derive NoConfusion for t_.

  Definition t := t_.

  Definition is_set (x : t) :=
    match x with
    | lzero => true
    | _ => false
    end.

  Definition is_var (l : t) :=
    match l with
    | Var _ => true
    | _ => false
    end.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | lzero =>  (0%nat)
               | Level s => (Pos.to_nat (v.(valuation_mono) s))
               | Var x => (v.(valuation_poly) x)
               end.


  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lzero, lzero => Eq
    | lzero, _ => Lt
    | _, lzero => Gt
    | Level s1, Level s2 => string_compare s1 s2
    | Level _, _ => Lt
    | _, Level _ => Gt
    | Var n, Var m => Nat.compare n m
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (Level s)
  | ltSetVar n : lt_ lzero (Var n)
  | ltLevelLevel s s' : StringOT.lt s s' -> lt_ (Level s) (Level s')
  | ltLevelVar s n : lt_ (Level s) (Var n)
  | ltVarVar n n' : Nat.lt n n' -> lt_ (Var n) (Var n').
  Derive Signature for lt_.

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros [| |] X; inversion X.
      now eapply irreflexivity in H1.
      eapply Nat.lt_irrefl; tea.
    - intros [| |] [| |] [| |] X1 X2;
        inversion X1; inversion X2; constructor.
      now transitivity s0.
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

  Definition eq_level l1 l2 :=
    match l1, l2 with
    | Level.lzero, Level.lzero => true
    | Level.Level s1, Level.Level s2 => ReflectEq.eqb s1 s2
    | Level.Var n1, Level.Var n2 => ReflectEq.eqb n1 n2
    | _, _ => false
    end.
    
  #[global, program] Instance reflect_level : ReflectEq Level.t := {
    eqb := eq_level
  }.
  Next Obligation.
    destruct x, y.
    all: unfold eq_level.
    all: try solve [ constructor ; reflexivity ].
    all: try solve [ constructor ; discriminate ].
    - destruct (ReflectEq.eqb_spec t0 t1) ; nodec.
      constructor. f_equal. assumption.
    - destruct (ReflectEq.eqb_spec n n0) ; nodec.
      constructor. subst. reflexivity.
  Defined.
  
  Global Instance eqb_refl : @Reflexive Level.t eqb.
  Proof.
    intros x. apply ReflectEq.eqb_refl.
  Qed.

  Definition eqb := eq_level.

  Lemma eqb_spec l l' : reflect (eq l l') (eqb l l').
  Proof.
    apply reflectProp_reflect.
    now generalize (eqb_spec l l').
  Qed.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2}+{l1 <> l2} := Classes.eq_dec.

End Level.

Module LevelSet := MSetAVL.Make Level.
Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := WDecide (LevelSet).
Module LS := LevelSet.

Ltac lsets := LevelSetDecide.fsetdec.
Notation "(=_lset)" := LevelSet.Equal (at level 0).
Infix "=_lset" := LevelSet.Equal (at level 30).

Section LevelSetMoreFacts.

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

  Lemma LevelSet_In_fold_right_add x l :
    In x l <-> LevelSet.In x (fold_right LevelSet.add LevelSet.empty l).
  Proof.
    split.
    - induction l; simpl => //.
      intros [<-|H].
      * eapply LevelSet.add_spec; left; auto.
      * eapply LevelSet.add_spec; right; auto.
    - induction l; simpl => //.
      * now rewrite LevelSetFact.empty_iff.
      * rewrite LevelSet.add_spec. intuition auto.
  Qed.

  Lemma LevelSet_union_empty s : LevelSet.Equal (LevelSet.union LevelSet.empty s) s.
  Proof.
    intros x; rewrite LevelSet.union_spec. lsets.
  Qed.
End LevelSetMoreFacts.

(* prop level is Prop or SProp *)
Module PropLevel.

  Inductive t := lSProp | lProp.
  Derive NoConfusion EqDec for t.
  (* Global Instance PropLevel_Evaluable : Evaluable t :=
    fun v l => match l with
              lSProp => -1
            | lProp => -1
            end. *)

  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lSProp, lSProp  => Eq
    | lProp, lProp  => Eq
    | lProp, lSProp => Gt
    | lSProp, lProp => Lt
    end.

  Inductive lt_ : t -> t -> Prop :=
    ltSPropProp : lt_ lSProp lProp.

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  split.
  - intros n X. destruct n;inversion X.
  - intros n1 n2 n3 X1 X2. destruct n1,n2,n3;auto; try inversion X1;try inversion X2.
  Defined.

End PropLevel.

Module LevelExpr.
  (* npe = no prop expression *)
  Definition t := (Level.t * nat)%type.

  Global Instance Evaluable : Evaluable t
    := fun v l => (snd l + val v (fst l)).

  Definition succ (l : t) := (fst l, S (snd l)).

  Definition get_level (e : t) : Level.t := fst e.

  Definition get_noprop (e : LevelExpr.t) := Some (fst e).

  Definition is_level (e : t) : bool :=
    match e with
    | (_, 0%nat) => true
    | _  => false
    end.

  Definition make (l : Level.t) : t := (l, 0%nat).

  Definition set : t := (Level.lzero, 0%nat).
  Definition type1 : t := (Level.lzero, 1%nat).

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
  | ltLevelExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

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
    intros x x' H1 y y' H2; now rewrite H1 H2.
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

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Lemma val_make v l
    : val v (LevelExpr.make l) = val v l.
  Proof.
    destruct l eqn:H; cbnr.
  Qed.

  Lemma val_make_npl v (l : Level.t)
    : val v (LevelExpr.make l) = val v l.
  Proof.
    destruct l; cbnr.
  Qed.

End LevelExpr.

Module LevelExprSet := MSetList.MakeWithLeibniz LevelExpr.
Module LevelExprSetFact := WFactsOn LevelExpr LevelExprSet.
Module LevelExprSetProp := WPropertiesOn LevelExpr LevelExprSet.

(* We have decidable equality w.r.t leibniz equality for sets of levels.
  This means concreteUniverses also have a decidable equality. *)
#[global, program] Instance levelexprset_reflect : ReflectEq LevelExprSet.t :=
  { eqb := LevelExprSet.equal }.
Next Obligation.
  destruct (LevelExprSet.equal x y) eqn:e; constructor.
  eapply LevelExprSet.equal_spec in e.
  now eapply LevelExprSet.eq_leibniz.
  intros e'.
  subst y.
  pose proof (@LevelExprSetFact.equal_1 x x).
  forward H. reflexivity. congruence.
Qed.

#[global] Instance levelexprset_eq_dec : Classes.EqDec LevelExprSet.t := Classes.eq_dec.



Record nonEmptyLevelExprSet
  := { t_set : LevelExprSet.t ;
       t_ne  : LevelExprSet.is_empty t_set = false }.

Derive NoConfusion for nonEmptyLevelExprSet.

(** This coercion allows to see the non-empty set as a regular [LevelExprSet.t] *)
Coercion t_set : nonEmptyLevelExprSet >-> LevelExprSet.t.

Module NonEmptySetFacts.
  Definition singleton (e : LevelExpr.t) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.singleton e;
          t_ne := eq_refl |}.

  Lemma not_Empty_is_empty s :
    ~ LevelExprSet.Empty s -> LevelExprSet.is_empty s = false.
  Proof.
    intro H. apply not_true_is_false. intro H'.
    apply H. now apply LevelExprSetFact.is_empty_2 in H'.
  Qed.

  Program Definition add (e : LevelExpr.t) (u : nonEmptyLevelExprSet) : nonEmptyLevelExprSet
    := {| t_set := LevelExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply LevelExprSet.add_spec.
    left; reflexivity.
  Qed.

  Lemma add_spec e u e' :
    LevelExprSet.In e' (add e u) <-> e' = e \/ LevelExprSet.In e' u.
  Proof.
    apply LevelExprSet.add_spec.
  Qed.

  Definition add_list : list LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet
    := List.fold_left (fun u e => add e u).

  Lemma add_list_spec l u e :
    LevelExprSet.In e (add_list l u) <-> In e l \/ LevelExprSet.In e u.
  Proof.
    unfold add_list. rewrite <- fold_left_rev_right.
    etransitivity. 2:{ eapply or_iff_compat_r. etransitivity.
                       2: apply @InA_In_eq with (A:=LevelExpr.t).
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

  Program Definition to_nonempty_list (u : nonEmptyLevelExprSet) : LevelExpr.t * list LevelExpr.t
    := match LevelExprSet.elements u with
       | [] => False_rect _ _
       | e :: l => (e, l)
       end.
  Next Obligation.
    destruct u as [u1 u2]; cbn in *. revert u2.
    apply eq_true_false_abs.
    unfold LevelExprSet.is_empty, LevelExprSet.Raw.is_empty,
    LevelExprSet.elements, LevelExprSet.Raw.elements in *.
    rewrite <- Heq_anonymous; reflexivity.
  Qed.

  Lemma singleton_to_nonempty_list e : to_nonempty_list (singleton e) = (e, []).
  Proof. reflexivity. Defined.

  Lemma to_nonempty_list_spec u :
    let '(e, u') := to_nonempty_list u in
    e :: u' = LevelExprSet.elements u.
  Proof.
    destruct u as [u1 u2].
    unfold to_nonempty_list; cbn.
    set (l := LevelExprSet.elements u1). unfold l at 2 3 4.
    set (e := (eq_refl: l = LevelExprSet.elements u1)); clearbody e.
    destruct l.
    - exfalso. revert u2. apply eq_true_false_abs.
      unfold LevelExprSet.is_empty, LevelExprSet.Raw.is_empty,
      LevelExprSet.elements, LevelExprSet.Raw.elements in *.
      rewrite <- e; reflexivity.
    - reflexivity.
  Qed.

  Lemma to_nonempty_list_spec' u :
    (to_nonempty_list u).1 :: (to_nonempty_list u).2 = LevelExprSet.elements u.
  Proof.
    pose proof (to_nonempty_list_spec u).
    now destruct (to_nonempty_list u).
  Qed.

  Lemma In_to_nonempty_list (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (to_nonempty_list u).2.
  Proof.
    etransitivity. symmetry. apply LevelExprSet.elements_spec1.
    pose proof (to_nonempty_list_spec' u) as H.
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_to_nonempty_list_rev (u : nonEmptyLevelExprSet) (e : LevelExpr.t) :
    LevelExprSet.In e u
    <-> e = (to_nonempty_list u).1 \/ In e (List.rev (to_nonempty_list u).2).
  Proof.
    etransitivity. eapply In_to_nonempty_list.
    apply or_iff_compat_l. apply in_rev.
  Qed.

  Definition map (f : LevelExpr.t -> LevelExpr.t) (u : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    let '(e, l) := to_nonempty_list u in
    add_list (List.map f l) (singleton (f e)).

  Lemma map_spec f u e :
    LevelExprSet.In e (map f u) <-> exists e0, LevelExprSet.In e0 u /\ e = (f e0).
  Proof.
    unfold map. symmetry. etransitivity.
    { eapply iff_ex; intro. eapply and_iff_compat_r. eapply In_to_nonempty_list. }
    destruct (to_nonempty_list u) as [e' l]; cbn in *.
    symmetry. etransitivity. eapply add_list_spec.
    etransitivity. eapply or_iff_compat_l. apply LevelExprSet.singleton_spec.
    etransitivity. eapply or_iff_compat_r.
    apply in_map_iff. clear u. split.
    - intros [[e0 []]|H].
      + exists e0. split. right; tas. congruence.
      + exists e'. split; tas. left; reflexivity.
    - intros [xx [[H|H] ?]].
      + right. congruence.
      + left. exists xx. split; tas; congruence.
  Qed.

  Program Definition non_empty_union (u v : nonEmptyLevelExprSet) : nonEmptyLevelExprSet :=
    {| t_set := LevelExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: LevelExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply LevelExprSet.union_spec. now left. }
    apply LevelExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.

  Lemma elements_not_empty (u : nonEmptyLevelExprSet) : LevelExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold LevelExprSet.is_empty, LevelExprSet.elements,
    LevelExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
  Qed.


  Lemma eq_univ (u v : nonEmptyLevelExprSet) :
    u = v :> LevelExprSet.t -> u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
    now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma eq_univ' (u v : nonEmptyLevelExprSet) :
    LevelExprSet.Equal u v -> u = v.
  Proof.
    intro H. now apply eq_univ, LevelExprSet.eq_leibniz.
  Qed.

  Lemma eq_univ'' (u v : nonEmptyLevelExprSet) :
    LevelExprSet.elements u = LevelExprSet.elements v -> u = v.
  Proof.
    intro H. apply eq_univ.
    destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
    destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
    destruct H. now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma univ_expr_eqb_true_iff (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> u = v.
  Proof.
    split.
    - intros.
      apply eq_univ'. now apply LevelExprSet.equal_spec.
    - intros ->. now apply LevelExprSet.equal_spec.
  Qed.

  Lemma univ_expr_eqb_comm (u v : nonEmptyLevelExprSet) :
    LevelExprSet.equal u v <-> LevelExprSet.equal v u.
  Proof.
    transitivity (u = v). 2: transitivity (v = u).
    - apply univ_expr_eqb_true_iff.
    - split; apply eq_sym.
    - split; apply univ_expr_eqb_true_iff.
  Qed.


  Lemma LevelExprSet_for_all_false f u :
    LevelExprSet.for_all f u = false -> LevelExprSet.exists_ (negb ∘ f) u.
  Proof.
    intro H. rewrite LevelExprSetFact.exists_b.
    rewrite LevelExprSetFact.for_all_b in H.
    all: try now intros x y [].
    induction (LevelExprSet.elements u); cbn in *; [discriminate|].
    apply andb_false_iff in H; apply orb_true_iff; destruct H as [H|H].
    left; now rewrite H.
    right; now rewrite IHl.
  Qed.

  Lemma LevelExprSet_For_all_exprs (P : LevelExpr.t -> Prop) (u : nonEmptyLevelExprSet)
    : LevelExprSet.For_all P u
      <-> P (to_nonempty_list u).1 /\ Forall P (to_nonempty_list u).2.
  Proof.
    etransitivity.
    - eapply iff_forall; intro e. eapply imp_iff_compat_r.
      apply In_to_nonempty_list.
    - cbn; split.
      + intro H. split. apply H. now left.
        apply Forall_forall. intros x H0.  apply H; now right.
      + intros [H1 H2] e [He|He]. subst e; tas.
        eapply Forall_forall in H2; tea.
  Qed.


End NonEmptySetFacts.
Import NonEmptySetFacts.


Module LevelAlgExpr.
  (** A universe / an algebraic expression is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty *)

  Definition t := nonEmptyLevelExprSet.

  (* We use uip on the is_empty condition *)
  #[global, program] Instance levelexprset_reflect : ReflectEq t :=
    { eqb x y := eqb x.(t_set) y.(t_set) }.
  Next Obligation.
    destruct (eqb_spec (t_set x) (t_set y)); constructor.
    destruct x, y; cbn in *. subst.
    now rewrite (uip t_ne0 t_ne1).
    intros e; subst x; apply H.
    reflexivity.
  Qed.

  #[global] Instance eq_dec_univ0 : EqDec t := eq_dec.

  Definition make (e: LevelExpr.t) : t := singleton e.
  Definition make' (l: Level.t) := singleton (LevelExpr.make l).

  (** The non empty / sorted / without dup list of univ expressions, the
    components of the pair are the head and the tail of the (non empty) list *)
  Definition exprs : t -> LevelExpr.t * list LevelExpr.t := to_nonempty_list.

  Global Instance Evaluable : Evaluable LevelAlgExpr.t
    := fun v u =>
      let '(e, u) := LevelAlgExpr.exprs u in
      List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    LevelExprSet.for_all LevelExpr.is_level u.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (LevelExprSet.cardinal u =? 1)%nat && is_levels u.


  Definition succ : t -> t := map LevelExpr.succ.

  (** The l.u.b. of 2 non-prop universe sets *)
  Definition sup : t -> t -> t := non_empty_union.

  Definition get_is_level (u : t) : option Level.t :=
    match LevelExprSet.elements u with
    | [(l, 0%nat)] => Some l
    | _ => None
    end.

  Lemma val_make v e : val v (make e) = val v e.
  Proof. reflexivity. Qed.

  Lemma val_make' v l
    : val v (make' l) = val v l.
  Proof. reflexivity. Qed.

End LevelAlgExpr.

Ltac u :=
  change LevelSet.elt with Level.t in *;
  change LevelExprSet.elt with LevelExpr.t in *.
  (* change ConstraintSet.elt with UnivConstraint.t in *. *)


Lemma val_fold_right (u : LevelAlgExpr.t) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (LevelAlgExpr.exprs u).1)
                       (List.rev (LevelAlgExpr.exprs u).2).
Proof.
  unfold val at 1, LevelAlgExpr.Evaluable.
  destruct (LevelAlgExpr.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : LevelAlgExpr.t) v e :
  LevelExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply In_to_nonempty_list_rev in H.
  fold LevelAlgExpr.exprs in H; destruct (LevelAlgExpr.exprs u); cbn in *.
  destruct H as [H|H].
  - subst. induction (List.rev l); cbnr. lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : LevelAlgExpr.t) v :
  exists e, LevelExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
  rewrite val_fold_right. fold LevelAlgExpr.exprs; destruct (LevelAlgExpr.exprs u) as [e l]; cbn in *.
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

Lemma val_ge_caract (u : LevelAlgExpr.t) v k :
  (forall e, LevelExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold LevelAlgExpr.exprs; destruct (LevelAlgExpr.exprs u) as [e l]; cbn; clear.
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

Lemma val_le_caract (u : LevelAlgExpr.t) v k :
  (exists e, LevelExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply In_to_nonempty_list_rev. }
    rewrite val_fold_right.
    fold LevelAlgExpr.exprs; destruct (LevelAlgExpr.exprs u) as [e l]; cbn; clear.
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



Lemma val_caract (u : LevelAlgExpr.t) v k :
  val v u = k
  <-> (forall e, LevelExprSet.In e u -> val v e <= k)
    /\ exists e, LevelExprSet.In e u /\ val v e = k.
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

Lemma val_add v e (s: LevelAlgExpr.t)
  : val v (add e s) = Nat.max (val v e) (val v s).
Proof.
  apply val_caract. split.
  - intros e' H. apply LevelExprSet.add_spec in H. destruct H as [H|H].
    + subst. u; lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v e) (val v s)) as [H|H]; rewrite H; clear H.
    + exists e. split; cbnr. apply LevelExprSetFact.add_1. reflexivity.
    + destruct (val_In_max s v) as [e' [H1 H2]].
      exists e'. split; tas. now apply LevelExprSetFact.add_2.
Qed.

Lemma val_sup v s1 s2 :
  val v (LevelAlgExpr.sup s1 s2) = Nat.max (val v s1) (val v s2).
Proof.
  eapply val_caract. cbn. split.
  - intros e' H. eapply LevelExprSet.union_spec in H. destruct H as [H|H].
    + eapply val_In_le with (v:=v) in H. lia.
    + eapply val_In_le with (v:=v) in H. lia.
  - destruct (Nat.max_dec (val v s1) (val v s2)) as [H|H]; rewrite H; clear H.
    + destruct (val_In_max s1 v) as [e' [H1 H2]].
      exists e'. split; tas. apply LevelExprSet.union_spec. now left.
    + destruct (val_In_max s2 v) as [e' [H1 H2]].
      exists e'. split; tas. apply LevelExprSet.union_spec. now right.
Qed.

Ltac proper := let H := fresh in try (intros ? ? H; destruct H; reflexivity).

Lemma for_all_elements (P : LevelExpr.t -> bool) u :
  LevelExprSet.for_all P u = forallb P (LevelExprSet.elements u).
Proof.
  apply LevelExprSetFact.for_all_b; proper.
Qed.


Lemma levelalg_get_is_level_correct u l :
  LevelAlgExpr.get_is_level u = Some l -> u = LevelAlgExpr.make' l.
Proof.
  intro H.
  unfold LevelAlgExpr.get_is_level in *.
  destruct (LevelExprSet.elements u) as [|l0 L] eqn:Hu1; [discriminate |].
  destruct l0, L; try discriminate.
  * destruct n; inversion H; subst.
    apply eq_univ''; apply Hu1.
  * destruct n; discriminate.
Qed.


Lemma sup0_comm x1 x2 :
  LevelAlgExpr.sup x1 x2 = LevelAlgExpr.sup x2 x1.
Proof.
  apply eq_univ'; simpl. unfold LevelExprSet.Equal.
  intros H. rewrite !LevelExprSet.union_spec. intuition.
Qed.


Declare Scope univ_scope.
Delimit Scope univ_scope with u.

(** Universes with linear hierarchy *)
Section ConcreteUniverses.
  Context {cf}.

  Inductive concreteUniverses :=
    | UProp
    | USProp
    | UType (i : nat).
  Derive NoConfusion EqDec for concreteUniverses.

  (** u + n <= u' *)
  Definition leq_cuniverse_n n u u' :=
    match u, u' with
    | UProp, UProp
    | USProp, USProp => (n = 0)%Z
    | UType u, UType u' => (Z.of_nat u <= Z.of_nat u' - n)%Z
    | UProp, UType u =>
      if prop_sub_type then True else False
    | _, _ => False
    end.

  Definition leq_cuniverse := leq_cuniverse_n 0.
  Definition lt_cuniverse := leq_cuniverse_n 1.

  Notation "x <_ n  y" := (leq_cuniverse_n n x y) (at level 10, n name) : univ_scope.
  Notation "x < y" := (lt_cuniverse x y) : univ_scope.
  Notation "x <= y" := (leq_cuniverse x y) : univ_scope.

  Definition cuniv_sup u1 u2 :=
    match u1, u2 with
    | UProp, UProp => UProp
    | USProp, USProp => USProp
    | UType v, UType v' => UType (Nat.max v v')
    | _, UType _ => u2
    | UType _, _ => u1
    | UProp, USProp => UProp
    | USProp, UProp => UProp
    end.

  Definition is_uprop u := match u with UProp => True | _ => False end.
  Definition is_usprop u := match u with USProp => True | _ => False end.
  Definition is_uproplevel u := match u with USProp | UProp => True | _ => False end.
  Definition is_uproplevel_or_set u := match u with USProp | UProp | UType 0 => True | _ => False end.
  Definition is_utype u := match u with UType _ => True | _ => False end.

  (** Type of a product *)
  Definition cuniv_of_product domsort rangsort :=
    match rangsort with
    (* Prop and SProp impredicativity *)
    | UProp | USProp => rangsort
    | _ => cuniv_sup domsort rangsort
    end.

  Lemma cuniv_sup_comm u u' : cuniv_sup u u' = cuniv_sup u' u.
  Proof using Type. destruct u, u'; cbn; try congruence. f_equal; lia. Qed.

  Lemma cuniv_sup_not_uproplevel u u' :
    ~ is_uproplevel u -> ∑ n, cuniv_sup u u' = UType n.
  Proof using Type.
    destruct u, u'; cbn; intros Hp; try absurd;
    now eexists.
  Qed.

  Lemma cuniv_le_uprop_inv u : (u <= UProp)%u -> u = UProp.
  Proof using Type. destruct u; simpl; intros Hle; try absurd; now reflexivity. Qed.

  Lemma cuniv_le_usprop_inv u : (u <= USProp)%u -> u = USProp.
  Proof using Type. destruct u; simpl; intros Hle; try absurd; now reflexivity. Qed.

  Lemma cuniv_uprop_le_inv u : (UProp <= u)%u ->
    (u = UProp \/ (prop_sub_type /\ exists n, u = UType n)).
  Proof using Type.
    destruct u; simpl; intros Hle; [ left; reflexivity | absurd | right ].
    destruct prop_sub_type; [| absurd].
    split; [ trivial | now eexists ].
  Qed.

  Lemma cuniv_sup_mon u u' v v' : (u <= u')%u -> (UType v <= UType v')%u ->
    (cuniv_sup u (UType v) <= cuniv_sup u' (UType v'))%u.
  Proof using Type.
    destruct u, u'; simpl; intros Hle Hle'; try absurd;
    lia.
  Qed.

  Lemma leq_cuniv_of_product_mon u u' v v' :
    (u <= u')%u ->
    (v <= v')%u ->
    (cuniv_of_product u v <= cuniv_of_product u' v')%u.
  Proof using Type.
    intros Hle1 Hle2.
    destruct v, v'; cbn in Hle2 |- *; auto.
    - destruct u'; cbn; assumption.
    - apply cuniv_sup_mon; assumption.
  Qed.

  Lemma impredicative_cuniv_product {l u} :
    is_uproplevel u ->
    (cuniv_of_product l u <= u)%u.
  Proof using Type. now destruct u. Qed.


  Global Instance leq_cuniverse_refl : Reflexive leq_cuniverse.
  Proof using Type.
    intros []; cbnr; lia.
  Qed.

  Global Instance leq_cuniverse_n_trans n : Transitive (leq_cuniverse_n (Z.of_nat n)).
  Proof using Type.
    intros [] [] []; cbnr; trivial; try absurd; lia.
  Qed.

  Global Instance leq_cuniverse_trans : Transitive leq_cuniverse.
  Proof using Type. apply (leq_cuniverse_n_trans 0). Qed.

  Global Instance lt_cuniverse_trans : Transitive lt_cuniverse.
  Proof using Type. apply (leq_cuniverse_n_trans 1). Qed.

  Global Instance leq_cuniverse_preorder : PreOrder leq_cuniverse :=
    Build_PreOrder _ _ _.

  Global Instance lt_cuniverse_str_order : StrictOrder lt_cuniverse.
  Proof using Type.
    split.
    - intros []; unfold complement; cbnr; lia.
    - exact _.
  Qed.

  Global Instance leq_cuniverse_antisym : Antisymmetric _ eq leq_cuniverse.
  Proof using Type.
    intros [] []; cbnr; try absurd.
    intros. f_equal; lia.
  Qed.

End ConcreteUniverses.


(** This inductive classifies which eliminations are allowed for inductive types
  in various sorts. *)
Inductive allowed_eliminations : Set :=
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny.
Derive NoConfusion EqDec for allowed_eliminations.


Definition is_allowed_elimination_cuniv (allowed : allowed_eliminations) : concreteUniverses -> Prop :=
  match allowed with
  | IntoSProp => is_usprop
  | IntoPropSProp => is_uproplevel
  | IntoSetPropSProp => is_uproplevel_or_set
  | IntoAny => fun _ => True
  end.


Module Universe.
  Inductive t_ :=
    lProp | lSProp | lType (_ : LevelAlgExpr.t).
  Derive NoConfusion for t_.

  Definition t := t_.

  Definition eqb (u1 u2 : t) : bool :=
    match u1, u2 with
    | lSProp, lSProp => true
    | lProp, lProp => true
    | lType e1, lType e2 => eqb e1 e2
    | _, _ => false
    end.

  #[global, program] Instance reflect_eq_universe : ReflectEq t :=
    { eqb := eqb }.
  Next Obligation.
    destruct x, y; cbn; try constructor; auto; try congruence.
    destruct (eqb_spec t0 t1); constructor. now f_equal.
    congruence.
  Qed.

  #[global] Instance eq_dec_univ : EqDec t := eq_dec.

  Definition on_sort (P: LevelAlgExpr.t -> Prop) (def: Prop) (s : t) :=
    match s with
    | lProp | lSProp => def
    | lType l => P l
    end.

  (** Create a universe representing the given level. *)
  Definition make (l : Level.t) : t :=
    lType (LevelAlgExpr.make (LevelExpr.make l)).

  Definition of_expr e := (lType (LevelAlgExpr.make e)).

  Definition add_to_exprs (e : LevelExpr.t) (u : t) : t :=
    match u with
    | lSProp | lProp => u
    | lType l => lType (add e l)
    end.

  Definition add_list_to_exprs (es : list LevelExpr.t) (u : t) : t :=
    match u with
    | lSProp | lProp => u
    | lType l => lType (add_list es l)
    end.

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    match u with
    | lSProp | lProp => true
    | lType l => LevelAlgExpr.is_levels l
    end.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    match u with
    | lSProp | lProp => true
    | lType l => LevelAlgExpr.is_level l
    end.

  Definition is_sprop (u : t) : bool :=
    match u with
      | lSProp => true
      | _ => false
    end.

  Definition is_prop (u : t) : bool :=
    match u with
      | lProp => true
      | _ => false
    end.

  Definition is_type_sort (u : t) : bool :=
    match u with
      | lType _ => true
      | _ => false
    end.

  Definition type0 : t := make Level.lzero.
  Definition type1 : t := lType (LevelAlgExpr.make LevelExpr.type1).

  Definition of_levels (l : PropLevel.t + Level.t) : t :=
    match l with
    | inl PropLevel.lSProp => lSProp
    | inl PropLevel.lProp => lProp
    | inr l => lType (LevelAlgExpr.make' l)
    end.

  (* Used for quoting. *)
  Definition from_kernel_repr (e : Level.t * bool) (es : list (Level.t * bool)) : t
    := lType (add_list (List.map LevelExpr.from_kernel_repr es)
                (LevelAlgExpr.make (LevelExpr.from_kernel_repr e))).

  (* Definition uex_to_kernel_repr (e : LevelExpr.t) : Level.t * bool := *)
  (*   match e with *)
  (*   | LevelExpr.npe (l, b) => (NoPropLevel.to_level l, b) *)
  (*   end. *)

  (* Definition to_kernel_repr (u : t) : list (Level.t * bool) *)
  (*   :=  map (LevelExpr.to_kernel_repr) (LevelExprSet.elements u). *)
  (* match u with *)
  (*      | lProp => [(Level.lProp, false)] *)
  (*      | lSProp => [(Level.lSProp, false)] *)
  (*      | lType l => map uex_to_kernel_repr (LevelExprSet.elements l) *)
  (*      end. *)

  (** The universe strictly above FOR TYPING (not cumulativity) *)

  Definition super (l : t) : t :=
    match l with
    | lSProp => type1
    | lProp => type1
    | lType l => lType (LevelAlgExpr.succ l)
    end.

  Definition sup (u v : t) : t :=
    match u,v with
    | lSProp, lProp => lProp
    | lProp, lSProp => lProp
    | (lSProp | lProp), u' => u'
    | u', (lSProp | lProp) => u'
    | lType l1, lType l2  => lType (LevelAlgExpr.sup l1 l2)
    end.

  Definition get_univ_exprs (u : t) (H1 : is_prop u = false) (H2 : is_sprop u = false) : LevelAlgExpr.t.
  destruct u; try discriminate; easy. Defined.

  (** Type of a product *)
  Definition sort_of_product (domsort rangsort : t) :=
    (* Prop and SProp impredicativity *)
    if Universe.is_prop rangsort || Universe.is_sprop rangsort then rangsort
    else Universe.sup domsort rangsort.

  Lemma eqb_refl u : eqb u u.
  Proof.
    destruct u; auto.
    now apply LevelExprSet.equal_spec.
  Qed.

  Definition get_is_level (u : t) : option Level.t :=
    match u with
    | lSProp => None
    | lProp => None
    | lType l => LevelAlgExpr.get_is_level l
    end.

  Definition to_cuniv v u :=
    match u with
    | lSProp => USProp
    | lProp => UProp
    | lType l => UType (val v l)
    end.

  Lemma val_make v l
    : to_cuniv v (make l) = UType (val v l).
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma make_inj x y :
    make x = make y -> x = y.
  Proof.
    destruct x, y; try now inversion 1.
  Qed.

End Universe.

Definition is_propositional u :=
  Universe.is_prop u || Universe.is_sprop u.

Notation "⟦ u ⟧_ v" := (Universe.to_cuniv v u) (at level 0, format "⟦ u ⟧_ v", v name) : univ_scope.


Lemma val_universe_sup v u1 u2 :
  Universe.to_cuniv v (Universe.sup u1 u2) = cuniv_sup (Universe.to_cuniv v u1) (Universe.to_cuniv v u2).
Proof.
  destruct u1 as [ | | l1]; destruct u2 as [ | | l2];cbn;try lia; auto.
  f_equal. apply val_sup.
Qed.

Lemma is_prop_val u :
  Universe.is_prop u -> forall v, Universe.to_cuniv v u = UProp.
Proof.
  destruct u as [| | u];try discriminate;auto.
Qed.

Lemma is_sprop_val u :
  Universe.is_sprop u -> forall v, Universe.to_cuniv v u = USProp.
Proof.
  destruct u as [| | u];try discriminate;auto.
Qed.

(*
Lemma val_zero_exprs v (l : LevelAlgExpr.t) : 0 <= val v l.
Proof.
  rewrite val_fold_right.
  destruct (LevelAlgExpr.exprs l) as [e u']; clear l; cbn.
  induction (List.rev u'); simpl.
  - destruct e as [npl_expr].
    destruct npl_expr as [t b].
    cbn.
    assert (0 <= val v t) by apply Level.val_zero.
    destruct b;lia.
  - pose proof (LevelExpr.val_zero a v); lia.
Qed. *)


Lemma val_is_prop u v :
  Universe.to_cuniv v u = UProp <-> Universe.is_prop u.
Proof.
  destruct u; auto;cbn in *; intuition congruence.
Qed.

Lemma val_is_sprop u v :
  Universe.to_cuniv v u = USProp <-> Universe.is_sprop u.
Proof.
  destruct u;auto;cbn in *; intuition congruence.
Qed.

Lemma is_prop_and_is_sprop_val_false u :
  Universe.is_prop u = false -> Universe.is_sprop u = false ->
  forall v, ∑ n, Universe.to_cuniv v u = UType n.
Proof.
  intros Hp Hsp v.
  destruct u; try discriminate. simpl. eexists; eauto.
Qed.

Lemma val_is_prop_false u v n :
  Universe.to_cuniv v u = UType n -> Universe.is_prop u = false.
Proof.
  pose proof (is_prop_val u) as H. destruct (Universe.is_prop u); cbnr.
  rewrite (H eq_refl v). discriminate.
Qed.

Lemma get_is_level_correct u l :
  Universe.get_is_level u = Some l -> u = Universe.lType (LevelAlgExpr.make' l).
Proof.
  intro H; destruct u; cbnr; try discriminate.
  f_equal; now apply levelalg_get_is_level_correct.
Qed.

Lemma eqb_true_iff u v :
  Universe.eqb u v <-> u = v.
Proof.
  split. 2: intros ->; apply Universe.eqb_refl.
  intro H.
  destruct u, v;auto;try discriminate.
  apply f_equal. now apply univ_expr_eqb_true_iff.
Qed.

Lemma sup_comm x1 x2 :
  Universe.sup x1 x2 = Universe.sup x2 x1.
Proof.
  destruct x1,x2;auto.
  cbn;apply f_equal;apply sup0_comm.
Qed.

Lemma is_not_prop_and_is_not_sprop u :
  Universe.is_prop u = false -> Universe.is_sprop u = false ->
  ∑ u', u = Universe.lType u'.
Proof.
  intros Hp Hsp.
  destruct u; try discriminate. now eexists.
Qed.

Lemma is_prop_sort_sup x1 x2 :
  Universe.is_prop (Universe.sup x1 x2)
  -> Universe.is_prop x2 \/ Universe.is_sprop x2 .
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sort_sup' x1 x2 :
  Universe.is_prop (Universe.sup x1 x2)
  -> Universe.is_prop x1 \/ Universe.is_sprop x1 .
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_or_sprop_sort_sup x1 x2 :
  Universe.is_sprop (Universe.sup x1 x2) -> Universe.is_sprop x2.
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sort_sup_prop x1 x2 :
  Universe.is_prop x1 && Universe.is_prop x2 ->
  Universe.is_prop (Universe.sup x1 x2).
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_or_sprop_sort_sup_prop x1 x2 :
  Universe.is_sprop x1 && Universe.is_sprop x2 ->
  Universe.is_sprop (Universe.sup x1 x2).
Proof. destruct x1,x2;auto. Qed.

Lemma is_prop_sup u s :
  Universe.is_prop (Universe.sup u s) ->
  (Universe.is_prop u \/ Universe.is_sprop u) /\
  (Universe.is_prop s \/ Universe.is_sprop s).
Proof. destruct u,s;auto. Qed.

Lemma is_sprop_sup_iff u s :
  Universe.is_sprop (Universe.sup u s) <->
  (Universe.is_sprop u /\ Universe.is_sprop s).
Proof. split;destruct u,s;intuition. Qed.

Lemma is_type_sup_r s1 s2 :
  Universe.is_type_sort s2 ->
  Universe.is_type_sort (Universe.sup s1 s2).
Proof. destruct s2; try absurd; destruct s1; cbnr; intros; absurd. Qed.

Lemma is_prop_sort_prod x2 x3 :
  Universe.is_prop (Universe.sort_of_product x2 x3)
  -> Universe.is_prop x3.
Proof.
  unfold Universe.sort_of_product.
  destruct x3;cbn;auto.
  intros;simpl in *;destruct x2;auto.
Qed.

Lemma is_sprop_sort_prod x2 x3 :
  Universe.is_sprop (Universe.sort_of_product x2 x3)
  -> Universe.is_sprop x3.
Proof.
  unfold Universe.sort_of_product.
  destruct x3;cbn;auto.
  intros;simpl in *;destruct x2;auto.
Qed.

Module ConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.
  Derive NoConfusion EqDec for t_.

  Definition t := t_.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition Le0 := Le 0.
  Definition Lt := Le 1.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Derive Signature for lt_.
  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X. lia.
    - intros ? ? ? X Y; invs X; invs Y; constructor. lia.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
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
    unfold eq. decide equality. apply Z.eq_dec.
  Qed.
End ConstraintType.

Module UnivConstraint.
  Definition t : Set := Level.t * ConstraintType.t * Level.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

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
      compare_cont (Level.compare l1 l1')
        (compare_cont (ConstraintType.compare t t')
                    (Level.compare l2 l2')).

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
    unfold eq. decide equality; apply eq_dec.
  Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End UnivConstraint.

Module ConstraintSet := MSetAVL.Make UnivConstraint.
Module ConstraintSetFact := WFactsOn UnivConstraint ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraint ConstraintSet.
Module CS := ConstraintSet.
Module ConstraintSetDecide := WDecide (ConstraintSet).
Ltac csets := ConstraintSetDecide.fsetdec.

Notation "(=_cset)" := ConstraintSet.Equal (at level 0).
Infix "=_cset" := ConstraintSet.Equal (at level 30).

Definition declared_cstr_levels levels (cstr : UnivConstraint.t) :=
  let '(l1,_,l2) := cstr in
  LevelSet.In l1 levels /\ LevelSet.In l2 levels.

Definition is_declared_cstr_levels levels (cstr : UnivConstraint.t) : bool :=
  let '(l1,_,l2) := cstr in
  LevelSet.mem l1 levels && LevelSet.mem l2 levels.

Lemma CS_union_empty s : ConstraintSet.union ConstraintSet.empty s =_cset s.
Proof.
  intros x; rewrite ConstraintSet.union_spec. lsets.
Qed.

Lemma CS_For_all_union f cst cst' : ConstraintSet.For_all f (ConstraintSet.union cst cst') ->
  ConstraintSet.For_all f cst.
Proof.
  unfold CS.For_all.
  intros IH x inx. apply (IH x).
  now eapply CS.union_spec; left.
Qed.

Lemma CS_For_all_add P x s : CS.For_all P (CS.add x s) -> P x /\ CS.For_all P s.
Proof.
  intros.
  split.
  * apply (H x), CS.add_spec; left => //.
  * intros y iny. apply (H y), CS.add_spec; right => //.
Qed.

#[global] Instance CS_For_all_proper P : Morphisms.Proper ((=_cset) ==> iff)%signature (ConstraintSet.For_all P).
Proof.
  intros s s' eqs.
  unfold CS.For_all. split; intros IH x inxs; apply (IH x);
  now apply eqs.
Qed.

(** {6 Universe instances} *)

Module Instance.

  (** A universe instance represents a vector of argument concreteUniverses
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
  Definition t := list name × (Instance.t × ConstraintSet.t).

  Definition make' : Instance.t -> ConstraintSet.t -> Instance.t × ConstraintSet.t := pair.
  Definition make (ids : list name) (inst_ctrs : Instance.t × ConstraintSet.t) : t := (ids, inst_ctrs).

  Definition empty : t := ([], (Instance.empty, ConstraintSet.empty)).

  Definition instance : t -> Instance.t := fun x => fst (snd x).
  Definition constraints : t -> ConstraintSet.t := fun x => snd (snd x).

  Definition dest : t -> list name * (Instance.t * ConstraintSet.t) := fun x => x.
End UContext.

Module AUContext.
  Definition t := list name × ConstraintSet.t.

  Definition make (ids : list name) (ctrs : ConstraintSet.t) : t := (ids, ctrs).
  Definition repr (x : t) : UContext.t :=
    let (u, cst) := x in
    (u, (mapi (fun i _ => Level.Var i) u, cst)).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (snd (repr uctx))).

  #[local]
  Existing Instance EqDec_ReflectEq.
  Definition inter (au av : AUContext.t) : AUContext.t :=
    let prefix := (split_prefix au.1 av.1).1.1 in
    let lvls := fold_left_i (fun s i _ => LevelSet.add (Level.Var i) s) prefix LevelSet.empty in
    let filter := ConstraintSet.filter (is_declared_cstr_levels lvls) in
    make prefix (ConstraintSet.union (filter au.2) (filter av.2)).
End AUContext.

Module ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.

  Definition levels : t -> LevelSet.t := fst.
  Definition constraints : t -> ConstraintSet.t := snd.

  Definition empty : t := (LevelSet.empty, ConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && ConstraintSet.is_empty (snd uctx).

  Definition equal (x y : t) : Prop :=
    x.1 =_lset y.1 /\ x.2 =_cset y.2.

  Definition subset (x y : t) : Prop :=
    LevelSet.Subset (levels x) (levels y) /\
    ConstraintSet.Subset (constraints x) (constraints y).

  Definition inter (x y : t) : t :=
    (LevelSet.inter (levels x) (levels y),
      ConstraintSet.inter (constraints x) (constraints y)).

  Definition inter_spec (x y : t) :
    subset (inter x y) x /\
      subset (inter x y) y /\
      forall z, subset z x -> subset z y -> subset z (inter x y).
  Proof.
    split; last split.
    1,2: split=> ?; [move=> /LevelSet.inter_spec [//]|move=> /ConstraintSet.inter_spec [//]].
    move=> ? [??] [??]; split=> ??;
    [apply/LevelSet.inter_spec|apply/ConstraintSet.inter_spec]; split; auto.
  Qed.

  Definition union (x y : t) : t :=
    (LevelSet.union (levels x) (levels y), ConstraintSet.union (constraints x) (constraints y)).

  Definition union_spec (x y : t) :
    subset x (union x y) /\
      subset y (union x y) /\
      forall z, subset x z -> subset y z -> subset (union x y) z.
  Proof.
    split; last split.
    1,2: split=> ??; [apply/LevelSet.union_spec|apply/ConstraintSet.union_spec ]; by constructor.
    move=> ? [??] [??]; split=> ?;
    [move=>/LevelSet.union_spec|move=>/ConstraintSet.union_spec]=>-[]; auto.
  Qed.
End ContextSet.

Notation "(=_cs)" := ContextSet.equal (at level 0).
Notation "(⊂_cs)" := ContextSet.subset (at level 0).
Infix "=_cs" := ContextSet.equal (at level 30).
Infix "⊂_cs" := ContextSet.subset (at level 30).

Lemma incl_cs_refl cs : cs ⊂_cs cs.
Proof.
  split; [lsets|csets].
Qed.

Lemma incl_cs_trans cs1 cs2 cs3 : cs1 ⊂_cs cs2 -> cs2 ⊂_cs cs3 -> cs1 ⊂_cs cs3.
Proof.
  intros [? ?] [? ?]; split; [lsets|csets].
Qed.

Lemma empty_contextset_subset u : ContextSet.empty ⊂_cs u.
Proof.
  red. split; cbn; [lsets|csets].
Qed.

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
  Derive NoConfusion EqDec for t.

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.

Inductive universes_decl : Type :=
| Monomorphic_ctx
| Polymorphic_ctx (cst : AUContext.t).

Derive NoConfusion for universes_decl.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx => LevelSet.empty
  | Polymorphic_ctx ctx => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx => ConstraintSet.empty
  | Polymorphic_ctx ctx => snd (snd (AUContext.repr ctx))
  end.

Section Univ.
  Context {cf: checker_flags}.

  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Lemma satisfies_union v φ1 φ2 :
    satisfies v (CS.union φ1 φ2)
    <-> (satisfies v φ1 /\ satisfies v φ2).
  Proof using Type.
    unfold satisfies. split.
    - intros H; split; intros c Hc; apply H; now apply CS.union_spec.
    - intros [H1 H2] c Hc; apply CS.union_spec in Hc; destruct Hc; auto.
  Qed.

  Lemma satisfies_subset φ φ' val :
    ConstraintSet.Subset φ φ' ->
    satisfies val φ' ->
    satisfies val φ.
  Proof using Type.
    intros sub sat ? isin.
    apply sat, sub; auto.
  Qed.

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition consistent_extension_on cs cstr :=
    forall v, satisfies v (ContextSet.constraints cs) -> exists v',
        satisfies v' cstr /\
          LevelSet.For_all (fun l => val v l = val v' l) (ContextSet.levels cs).

  Lemma consistent_extension_on_empty Σ :
    consistent_extension_on Σ CS.empty.
  Proof using Type.
    move=> v hv; exists v; split; [move=> ? /CS.empty_spec[]| move=> ??//].
  Qed.

  Lemma consistent_extension_on_union X cstrs
    (wfX : forall c, CS.In c X.2 -> LS.In c.1.1 X.1 /\ LS.In c.2 X.1) :
    consistent_extension_on X cstrs <->
    consistent_extension_on X (CS.union cstrs X.2).
  Proof using Type.
    split.
    2: move=> h v /h [v' [/satisfies_union [??] eqv']]; exists v'; split=> //.
    move=> hext v /[dup] vsat /hext [v' [v'sat v'eq]].
    exists v'; split=> //.
    apply/satisfies_union; split=> //.
    move=> c hc. destruct (wfX c hc).
    destruct (vsat c hc); constructor; rewrite -!v'eq //.
  Qed.

  Definition leq0_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> (Z.of_nat (val v u) <= Z.of_nat (val v u') - n)%Z.

  Definition leq_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    if check_univs then leq0_levelalg_n n φ u u' else True.

  Definition leq_universe_n_ {CS} leq_levelalg_n n (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => (n = 0)%Z
    | Universe.lType u, Universe.lType u' => leq_levelalg_n n φ u u'
    | Universe.lProp,   Universe.lType u => prop_sub_type
    | _, _ => False
    end.

  Definition leq_universe_n := leq_universe_n_ leq_levelalg_n.

  Definition leqb_universe_n_ leqb_levelalg_n b s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => negb b
    | Universe.lType u, Universe.lType u' => leqb_levelalg_n b u u'
    | Universe.lProp,   Universe.lType u => prop_sub_type
    | _, _ => false
    end.

  Definition eq0_levelalg φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> val v u = val v u'.

  Definition eq_levelalg φ (u u' : LevelAlgExpr.t) :=
    if check_univs then eq0_levelalg φ u u' else True.

  Definition eq_universe_ {CS} eq_levelalg (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => True
    | Universe.lType u, Universe.lType u' => eq_levelalg φ u u'
    | _, _ => False
    end.

  Definition eq_universe := eq_universe_ eq_levelalg.

  Definition lt_levelalg := leq_levelalg_n 1.
  Definition leq_levelalg := leq_levelalg_n 0.
  Definition lt_universe := leq_universe_n 1.
  Definition leq_universe := leq_universe_n 0.

  Definition compare_universe (pb : conv_pb) :=
    match pb with
    | Conv => eq_universe
    | Cumul => leq_universe
    end.

  Lemma leq_levelalg_leq_levelalg_n (φ : ConstraintSet.t) u u' :
    leq_levelalg φ u u' <-> leq_levelalg_n 0 φ u u'.
  Proof using Type. intros. reflexivity. Qed.

  Lemma leq_universe_leq_universe_n (φ : ConstraintSet.t) u u' :
    leq_universe φ u u' <-> leq_universe_n 0 φ u u'.
  Proof using Type. intros. reflexivity. Qed.

  (* ctrs are "enforced" by φ *)

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Lemma valid_subset φ φ' ctrs
    : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof using Type.
    unfold valid_constraints.
    destruct check_univs; [|trivial].
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof using Type. split; lia. Qed.

  (* Lemma llt_lt n m : (n < m)%u -> (n < m)%Z.
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
  Proof. lled; lia. Qed. *)


  (** **** Lemmas about eq and leq **** *)

  Ltac unfold_univ_rel0 :=
    unfold eq0_levelalg, leq0_levelalg_n in *;
    intros v Hv; cbnr.

  Ltac unfold_univ_rel :=
    unfold eq_levelalg, leq_levelalg, lt_levelalg, leq_levelalg_n in *;
    destruct check_univs; [unfold_univ_rel0 | trivial].


  Global Instance eq_levelalg_refl φ : Reflexive (eq_levelalg φ).
  Proof using Type.
    intros u; unfold_univ_rel.
  Qed.

  Global Instance eq_universe_refl φ : Reflexive (eq_universe φ).
  Proof using Type.
    intros []; cbnr.
  Qed.

  Global Instance leq_levelalg_n_refl φ : Reflexive (leq_levelalg φ).
  Proof using Type.
    intros u; unfold_univ_rel. lia.
  Qed.

  Global Instance leq_universe_refl φ : Reflexive (leq_universe φ).
  Proof using Type.
    intros []; cbnr.
  Qed.

  Global Instance eq_levelalg_sym φ : Symmetric (eq_levelalg φ).
  Proof using Type.
    intros u u' H; unfold_univ_rel.
    specialize (H v Hv); lia.
  Qed.

  Global Instance eq_universe_sym φ : Symmetric (eq_universe φ).
  Proof using Type.
    intros [] []; cbnr; auto.
    now symmetry.
  Qed.

  Global Instance eq_levelalg_trans φ : Transitive (eq_levelalg φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_univ_rel.
    specialize (H1 v Hv); specialize (H2 v Hv); lia.
  Qed.

  Global Instance eq_universe_trans φ : Transitive (eq_universe φ).
  Proof using Type.
    intros [] [] []; cbnr; trivial; try absurd.
    etransitivity; eauto.
  Qed.

  Global Instance leq_levelalg_n_trans n φ : Transitive (leq_levelalg_n (Z.of_nat n) φ).
  Proof using Type.
    intros u u' u'' H1 H2; unfold_univ_rel.
    specialize (H1 v Hv); specialize (H2 v Hv); lia.
  Qed.

  Global Instance leq_universe_n_trans n φ : Transitive (leq_universe_n (Z.of_nat n) φ).
  Proof using Type.
    intros [] [] []; cbnr; trivial; try absurd.
    now etransitivity.
  Qed.

  Global Instance leq_universe_trans φ : Transitive (leq_universe φ).
  Proof using Type. apply (leq_universe_n_trans 0). Qed.

  Global Instance lt_universe_trans φ : Transitive (lt_universe φ).
  Proof using Type. apply (leq_universe_n_trans 1). Qed.

  Lemma eq0_leq0_levelalg φ u u' :
    eq0_levelalg φ u u' <-> leq0_levelalg_n 0 φ u u' /\ leq0_levelalg_n 0 φ u' u.
  Proof using Type.
    split.
    - intros H. split; unfold eq0_levelalg, leq_levelalg_n in *;
      intros v Hv; specialize (H v Hv); lia.
    - intros [H1 H2]. unfold eq0_levelalg, leq_levelalg_n in *.
      intros v Hv. specialize (H1 v Hv); specialize (H2 v Hv); lia.
  Qed.

  Lemma eq_leq_levelalg φ u u' :
    eq_levelalg φ u u' <-> leq_levelalg φ u u' /\ leq_levelalg φ u' u.
  Proof using Type.
    split.
    - intros H. split; unfold_univ_rel; specialize (H v Hv); lia.
    - intros [H1 H2]. unfold_univ_rel. specialize (H1 v Hv); specialize (H2 v Hv); lia.
  Qed.

  Lemma eq_leq_universe φ u u' :
    eq_universe φ u u' <-> leq_universe φ u u' /\ leq_universe φ u' u.
  Proof using Type.
    destruct u, u'; cbnr; intuition auto.
    all: now apply eq_leq_levelalg.
  Qed.

  Lemma leq_levelalg_sup0_l φ u1 u2 : leq_levelalg φ u1 (LevelAlgExpr.sup u1 u2).
  Proof using Type. unfold_univ_rel. rewrite val_sup; lia. Qed.

  Lemma leq_levelalg_sup0_r φ u1 u2 : leq_levelalg φ u2 (LevelAlgExpr.sup u1 u2).
  Proof using Type. unfold_univ_rel. rewrite val_sup; lia. Qed.

  Lemma leq_levelalg_sup0_mon φ u1 u1' u2 u2' : leq_levelalg φ u1 u1' -> leq_levelalg φ u2 u2' ->
    leq_levelalg φ (LevelAlgExpr.sup u1 u2) (LevelAlgExpr.sup u1' u2').
  Proof using Type.
    intros H1 H2; unfold_univ_rel.
    specialize (H1 v Hv); specialize (H2 v Hv).
    rewrite !val_sup. lia.
  Qed.

  Lemma leq_universe_sup_l φ u1 s2 :
    let s1 := Universe.lType u1 in
    leq_universe φ s1 (Universe.sup s1 s2).
  Proof using Type.
    destruct s2 as [| | u2]; cbnr.
    apply leq_levelalg_sup0_l.
  Qed.

  Lemma leq_universe_sup_r φ s1 u2 :
    let s2 := Universe.lType u2 in
    leq_universe φ s2 (Universe.sup s1 s2).
  Proof using Type.
    destruct s1 as [| | u1]; cbnr.
    apply leq_levelalg_sup0_r.
  Qed.

  Lemma leq_universe_product φ (s1 s2 : Universe.t)
    : leq_universe φ s2 (Universe.sort_of_product s1 s2).
  Proof using Type.
    destruct s2 as [| | u2].
    - apply leq_universe_refl.
    - apply leq_universe_refl.
    - apply leq_universe_sup_r.
  Qed.
  (* Rk: [leq_universe φ s1 (sort_of_product s1 s2)] does not hold due to
     impredicativity. *)

  Global Instance eq_universe_leq_universe φ : subrelation (eq_universe φ) (leq_universe φ).
  Proof using Type.
    intros u u'. apply eq_leq_universe.
  Qed.

  Global Instance eq_levelalg_equivalence φ : Equivalence (eq_levelalg φ) := Build_Equivalence _ _ _ _.

  Global Instance leq_levelalg_preorder φ : PreOrder (leq_levelalg φ) :=
    {| PreOrder_Transitive := leq_levelalg_n_trans 0 _ |}.

  Global Instance lt_levelalg_str_order {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_levelalg φ).
  Proof using Type.
    split.
    - intros u; unfold complement, lt_levelalg, leq_levelalg_n; cbn.
      rewrite c; destruct H as [v Hv]; intros nH; specialize (nH v Hv); lia.
    - apply (leq_levelalg_n_trans 1).
  Qed.

  Global Instance leq_levelalg_antisym φ
    : Antisymmetric _ (eq_levelalg φ) (leq_levelalg φ).
  Proof using Type. intros t u tu ut. now apply eq_leq_levelalg. Qed.

  Global Instance leq_levelalg_partial_order φ
    : PartialOrder (eq_levelalg φ) (leq_levelalg φ).
  Proof.
    intros x y; split; apply eq_leq_levelalg.
  Defined.


  Global Instance eq_universe_equivalence φ : Equivalence (eq_universe φ) := Build_Equivalence _ _ _ _.

  Global Instance leq_universe_preorder φ : PreOrder (leq_universe φ) := Build_PreOrder _ _ _.

  Global Instance lt_universe_str_order {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_universe φ).
  Proof using Type.
    split.
    - intros []; unfold complement; cbn; [lia|lia|].
      apply @StrictOrder_Irreflexive; apply @lt_levelalg_str_order; assumption.
    - exact _.
  Qed.

  Global Instance leq_universe_antisym φ
    : Antisymmetric _ (eq_universe φ) (leq_universe φ).
  Proof using Type. intros t u tu ut. now apply eq_leq_universe. Qed.

  Global Instance leq_universe_partial_order φ
    : PartialOrder (eq_universe φ) (leq_universe φ).
  Proof.
    intros x y; split; apply eq_leq_universe.
  Defined.

  Global Instance compare_universe_subrel pb Σ : subrelation (eq_universe Σ) (compare_universe pb Σ).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_refl pb Σ : Reflexive (compare_universe pb Σ).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_trans pb Σ : Transitive (compare_universe pb Σ).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_universe_preorder pb Σ : PreOrder (compare_universe pb Σ).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Definition eq_universe_leq_universe' φ u u'
    := @eq_universe_leq_universe φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_universe_leq_universe' leq_universe_refl' : core.

  Lemma cmp_universe_subset ctrs ctrs' pb t u
    : ConstraintSet.Subset ctrs ctrs'
      -> compare_universe pb ctrs t u -> compare_universe pb ctrs' t u.
  Proof using Type.
    intros Hctrs.
    destruct pb, t, u; cbnr; trivial.
    all: intros H; unfold_univ_rel;
    apply H.
    all: eapply satisfies_subset; eauto.
  Qed.

  Lemma eq_universe_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> eq_universe ctrs t u -> eq_universe ctrs' t u.
  Proof using Type. apply cmp_universe_subset with (pb := Conv). Qed.

  Lemma leq_universe_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> leq_universe ctrs t u -> leq_universe ctrs' t u.
  Proof using Type. apply cmp_universe_subset with (pb := Cumul). Qed.

  (** Elimination restriction *)

  Definition is_lSet φ s := eq_universe φ s Universe.type0.
    (* Unfolded definition :
    match s with
    | Universe.lType u =>
      if check_univs then forall v, satisfies v φ -> val v u = 0 else True
    | _ => False
    end. *)

  Definition is_allowed_elimination φ allowed : Universe.t -> Prop :=
    match allowed with
    | IntoSProp => Universe.is_sprop
    | IntoPropSProp => is_propositional
    | IntoSetPropSProp => fun s => is_propositional s \/ is_lSet φ s
    | IntoAny => fun s => True
    end.

  (* Is [a] a subset of [a']? *)
  Definition allowed_eliminations_subset (a a' : allowed_eliminations) : bool :=
    match a, a' with
    | IntoSProp, _
    | IntoPropSProp, (IntoPropSProp | IntoSetPropSProp | IntoAny)
    | IntoSetPropSProp, (IntoSetPropSProp | IntoAny)
    | IntoAny, IntoAny => true
    | _, _ => false
    end.

  Lemma allowed_eliminations_subset_impl φ a a' s
    : allowed_eliminations_subset a a' ->
      is_allowed_elimination φ a s -> is_allowed_elimination φ a' s.
  Proof using Type.
    destruct a, a'; cbnr; trivial;
    destruct s; cbnr; trivial;
    intros H1 H2; try absurd; constructor; trivial.
  Qed.

End Univ.

Ltac unfold_univ_rel0 :=
  unfold eq0_levelalg, leq0_levelalg_n in *;
  intros v Hv; cbnr.

Ltac unfold_univ_rel :=
  unfold is_allowed_elimination, is_lSet,
  leq_universe, eq_universe, leq_universe_n, leq_universe_n_, eq_universe_,
  eq_levelalg, leq_levelalg, lt_levelalg, leq_levelalg_n in *;
  destruct check_univs; [unfold_univ_rel0 | trivial].

Tactic Notation "unfold_univ_rel" "eqn" ":"ident(H) :=
  unfold is_allowed_elimination, is_lSet,
  leq_universe, eq_universe, leq_universe_n, leq_universe_n_, eq_universe_,
  eq_levelalg, leq_levelalg, lt_levelalg, leq_levelalg_n in *;
  destruct check_univs eqn:H; [unfold_univ_rel0 | trivial].

(* Ltac prop_non_prop :=
  match goal with
  | |- context[ Universe.is_prop ?u || Universe.is_sprop ?u]  =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  | H : context[ Universe.is_prop ?u || Universe.is_sprop ?u] |- _ =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  end. *)

Ltac cong := intuition congruence.


Lemma leq_universe_product_mon {cf} ϕ s1 s1' s2 s2' :
  leq_universe ϕ s1 s1' ->
  leq_universe ϕ s2 s2' ->
  leq_universe ϕ (Universe.sort_of_product s1 s2) (Universe.sort_of_product s1' s2').
Proof.
  destruct s2 as [| | u2], s2' as [| | u2']; cbnr; try absurd;
  destruct s1 as [| | u1], s1' as [| | u1']; cbnr; try absurd; trivial.
  - intros _ H2; etransitivity; [apply H2 | apply leq_levelalg_sup0_r].
  - apply leq_levelalg_sup0_mon.
Qed.

Lemma impredicative_product {cf} {ϕ l u} :
  Universe.is_prop u ->
  leq_universe ϕ (Universe.sort_of_product l u) u.
Proof.
  unfold Universe.sort_of_product.
  intros ->. reflexivity.
Qed.

Section UniverseLemmas.
  Context {cf: checker_flags}.

  Lemma sup0_idem s : LevelAlgExpr.sup s s = s.
  Proof using Type.
    apply eq_univ'; cbn.
    intro; rewrite !LevelExprSet.union_spec. intuition.
  Qed.

  Lemma sup_idem s : Universe.sup s s = s.
  Proof using Type.
    destruct s; cbn; auto.
    apply f_equal.
    apply sup0_idem.
  Qed.

  Lemma sort_of_product_idem s
    : Universe.sort_of_product s s = s.
  Proof using Type.
    unfold Universe.sort_of_product; destruct s; try reflexivity.
    apply sup_idem.
  Qed.

  Lemma sup0_assoc s1 s2 s3 :
    LevelAlgExpr.sup s1 (LevelAlgExpr.sup s2 s3) = LevelAlgExpr.sup (LevelAlgExpr.sup s1 s2) s3.
  Proof using Type.
    apply eq_univ'; cbn. symmetry; apply LevelExprSetProp.union_assoc.
  Qed.

  Instance proper_sup0_eq_levelalg φ :
    Proper (eq_levelalg φ ==> eq_levelalg φ ==> eq_levelalg φ) LevelAlgExpr.sup.
  Proof using Type.
    intros u1 u1' H1 u2 u2' H2.
    unfold_univ_rel.
    specialize (H1 v Hv); specialize (H2 v Hv).
    rewrite !val_sup. lia.
  Qed.

  Instance universe_sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) Universe.sup.
  Proof using Type.
    intros [| | u1] [| |u1'] H1 [| |u2] [| |u2'] H2; cbn in *; try absurd; auto.
    now apply proper_sup0_eq_levelalg.
  Qed.

  Lemma sort_of_product_twice u s :
    Universe.sort_of_product u (Universe.sort_of_product u s)
    = Universe.sort_of_product u s.
  Proof using Type.
    destruct u,s; cbnr.
    now rewrite sup0_assoc sup0_idem.
  Qed.
End UniverseLemmas.


Section no_prop_leq_type.
  Context {cf: checker_flags}.
  Context (ϕ : ConstraintSet.t).

  Lemma succ_inj x y : LevelExpr.succ x = LevelExpr.succ y -> x = y.
  Proof using Type.
    unfold LevelExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x :
    LevelExprSet.In x (LevelAlgExpr.succ l) <->
    exists x', LevelExprSet.In x' l /\ x = LevelExpr.succ x'.
  Proof using Type.
    rewrite map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (LevelExpr.succ l) = val v l + 1.
  Proof using Type.
    destruct l as []; simpl. cbn. lia.
  Qed.

  Lemma val_map_succ v l : val v (LevelAlgExpr.succ l) = val v l + 1.
  Proof using Type.
    pose proof (spec_map_succ l).
    set (n := LevelAlgExpr.succ l) in *.
    destruct (val_In_max l v) as [max [inmax eqv]]. rewrite <-eqv.
    rewrite val_caract. split.
    intros.
    specialize (proj1 (H _) H0) as [x' [inx' eq]]. subst e.
    rewrite val_succ. eapply (val_In_le _ v) in inx'. rewrite <- eqv in inx'.
    simpl in *. unfold LevelExprSet.elt, LevelExpr.t in *. lia.
    exists (LevelExpr.succ max). split. apply H.
    exists max; split; auto.
    now rewrite val_succ.
  Qed.

  Lemma leq_universe_super s s' :
    leq_universe ϕ s s' ->
    leq_universe ϕ (Universe.super s) (Universe.super s').
  Proof using Type.
    destruct s as [| | u1], s' as [| | u1']; cbnr; try absurd;
    intros H; unfold_univ_rel;
    rewrite !val_map_succ. lia.
    specialize (H v Hv). lia.
  Qed.

  Lemma leq_universe_props s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    match s1, s2 with
    | Universe.lProp, Universe.lProp => True
    | Universe.lSProp, Universe.lSProp => True
    | Universe.lProp, Universe.lSProp => False
    | Universe.lSProp, Universe.lProp => False
    | Universe.lProp, Universe.lType _ => prop_sub_type
    | Universe.lSProp, Universe.lType _ => False
    | Universe.lType l, Universe.lType l' => True
    | Universe.lType _, _ => False
    end.
  Proof using Type.
    destruct s1, s2; cbnr; trivial.
  Qed.

  Lemma leq_universe_prop_r s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    Universe.is_prop s2 -> Universe.is_prop s1.
  Proof using Type.
    intros Hcf cu.
    destruct s2; cbn; [ | absurd | absurd].
    destruct s1; cbn; [ auto | absurd | absurd].
  Qed.

  Lemma leq_universe_sprop_r s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    Universe.is_sprop s2 -> Universe.is_sprop s1.
  Proof using Type.
    intros Hcf cu.
    destruct s2; cbn; [ absurd | | absurd].
    destruct s1; cbn; [ absurd | auto | absurd].
  Qed.

  Lemma leq_universe_prop_no_prop_sub_type s1 s2 :
    check_univs ->
    prop_sub_type = false ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    Universe.is_prop s1 -> Universe.is_prop s2.
  Proof using Type.
    intros Hcf ps cu.
    destruct s1; cbn; [ | absurd | absurd].
    rewrite ps.
    destruct s2; cbn; [ auto | absurd | absurd].
  Qed.

  Lemma leq_universe_sprop_l s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    Universe.is_sprop s1 -> Universe.is_sprop s2.
  Proof using Type.
    intros Hcf cu.
    destruct s1; cbn; [ absurd | | absurd].
    destruct s2; cbn; [ absurd | auto | absurd].
  Qed.

  Hint Resolve leq_universe_sprop_l leq_universe_sprop_r
        leq_universe_prop_r
        leq_universe_prop_no_prop_sub_type
        : univ_lemmas.

  Lemma leq_prop_prop {l l'} :
    Universe.is_prop l -> Universe.is_prop l' ->
    leq_universe ϕ l l'.
  Proof using Type.
    destruct l, l'; cbnr; absurd.
  Qed.

  Lemma leq_sprop_sprop {l l'} :
    Universe.is_sprop l -> Universe.is_sprop l' ->
    leq_universe ϕ l l'.
  Proof using Type.
    destruct l, l'; cbnr; absurd.
  Qed.

  Lemma leq_prop_is_prop_sprop {s1 s2} :
    check_univs ->
    prop_sub_type = false ->
    consistent ϕ ->
    leq_universe ϕ s1 s2 ->
    is_propositional s1 <-> is_propositional s2.
  Proof using Type.
    intros Hcf ps cu.
    destruct s1, s2; cbn; try absurd; intros H; split; trivial.
    now rewrite ps in H.
  Qed.

  Lemma is_prop_gt s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ (Universe.super s1) s2 -> Universe.is_prop s2 -> False.
  Proof using Type.
    intros Hcf cu Hleq Hprop.
    apply leq_universe_prop_r in Hleq; tas.
    now destruct s1.
  Qed.

  Lemma is_sprop_gt s1 s2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ (Universe.super s1) s2 -> Universe.is_sprop s2 -> False.
  Proof using Type.
    intros Hcf cu Hleq Hprop.
    apply leq_universe_sprop_r in Hleq; tas.
    now destruct s1.
  Qed.

End no_prop_leq_type.


(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t := Level.Level "__metacoq_fresh_level__".
(* This universe is a hack used in plugins to generate fresh concreteUniverses *)
Definition fresh_universe : Universe.t := Universe.make fresh_level.

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Notation "x @[ u ]" := (subst_instance u x) (at level 3,
  format "x @[ u ]").

#[global] Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
            Level.lzero | Level.Level _ => l
          | Level.Var n => List.nth n u Level.lzero
          end.

#[global] Instance subst_instance_cstr : UnivSubst UnivConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

#[global] Instance subst_instance_cstrs : UnivSubst ConstraintSet.t :=
  fun u ctrs => ConstraintSet.fold (fun c => ConstraintSet.add (subst_instance_cstr u c))
                                ctrs ConstraintSet.empty.

#[global] Instance subst_instance_level_expr : UnivSubst LevelExpr.t :=
  fun u e => match e with
          | (Level.lzero, _)
          | (Level.Level _, _) => e
          | (Level.Var n, b) =>
            match nth_error u n with
            | Some l => (l,b)
            | None => (Level.lzero, b)
            end
          end.

#[global] Instance subst_instance_univ0 : UnivSubst LevelAlgExpr.t :=
  fun u => map (subst_instance_level_expr u).

#[global] Instance subst_instance_univ : UnivSubst Universe.t :=
  fun u e => match e with
          | Universe.lProp | Universe.lSProp => e
          | Universe.lType l => Universe.lType (subst_instance u l)
          end.

#[global] Instance subst_instance_instance : UnivSubst Instance.t :=
  fun u u' => List.map (subst_instance_level u) u'.

(** Tests that the term is closed over [k] universe variables *)
Section Closedu.
  Context (k : nat).

  Definition closedu_level (l : Level.t) :=
    match l with
    | Level.Var n => (n <? k)%nat
    | _ => true
    end.

  Definition closedu_level_expr (s : LevelExpr.t) :=
    closedu_level (LevelExpr.get_level s).

  Definition closedu_universe_levels (u : LevelAlgExpr.t) :=
    LevelExprSet.for_all closedu_level_expr u.

  Definition closedu_universe (u : Universe.t) :=
    match u with
    | Universe.lSProp | Universe.lProp => true
    | Universe.lType l => closedu_universe_levels l
    end.

  Definition closedu_instance (u : Instance.t) :=
    forallb closedu_level u.
End Closedu.

(** Universe-closed terms are unaffected by universe substitution. *)
Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level u l
  : closedu_level 0 l -> subst_instance_level u l = l.
  Proof.
    destruct l; cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_level_expr u e
    : closedu_level_expr 0 e -> subst_instance_level_expr u e = e.
  Proof.
    intros.
    destruct e as [t b]. destruct t;cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_univ u s
    : closedu_universe 0 s -> subst_instance_univ u s = s.
  Proof.
    intro H.
    destruct s as [| | t]; cbnr.
    apply f_equal. apply eq_univ'.
    destruct t as [ts H1].
    unfold closedu_universe_levels in *;cbn in *.
    intro e; split; intro He.
    - apply map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      apply LevelExprSet.for_all_spec in H; proper.
      exact (H _ He').
      now subst.
    - apply map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply LevelExprSet.for_all_spec in H; proper. now apply H.
  Qed.

  Lemma closedu_subst_instance u t
    : closedu_instance 0 t -> subst_instance u t = t.
  Proof.
    intro H. apply forall_map_id_spec.
    apply Forall_forall; intros l Hl.
    apply closedu_subst_instance_level.
    eapply forallb_forall in H; eassumption.
  Qed.

End UniverseClosedSubst.

#[global]
Hint Resolve closedu_subst_instance_level closedu_subst_instance_level_expr
     closedu_subst_instance_univ closedu_subst_instance : substu.

(** Substitution of a universe-closed instance of the right size
    produces a universe-closed term. *)
Section SubstInstanceClosed.
  Context (u : Instance.t) (Hcl : closedu_instance 0 u).

  Lemma subst_instance_level_closedu l
    : closedu_level #|u| l -> closedu_level 0 (subst_instance_level u l).
  Proof using Hcl.
    destruct l; cbnr.
    unfold closedu_instance in Hcl.
    destruct (nth_in_or_default n u Level.lzero).
    - intros _. eapply forallb_forall in Hcl; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_level_expr_closedu e :
    closedu_level_expr #|u| e -> closedu_level_expr 0 (subst_instance_level_expr u e).
  Proof using Hcl.
    destruct e as [l b]. destruct l;cbnr.
    case_eq (nth_error u n); cbnr. intros [] Hl X; cbnr.
    apply nth_error_In in Hl.
    eapply forallb_forall in Hcl; tea.
    discriminate.
  Qed.

  Lemma subst_instance_univ_closedu s
    : closedu_universe #|u| s -> closedu_universe 0 (subst_instance_univ u s).
  Proof using Hcl.
    intro H.
    destruct s as [| |t]; cbnr.
    destruct t as [l Hl].
    apply LevelExprSet.for_all_spec; proper.
    intros e He. eapply map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply LevelExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.

  Lemma subst_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance u t).
  Proof using Hcl.
    intro H. etransitivity. eapply forallb_map.
    eapply forallb_impl; tea.
    intros l Hl; cbn. apply subst_instance_level_closedu.
  Qed.
End SubstInstanceClosed.

#[global]
Hint Resolve subst_instance_level_closedu subst_instance_level_expr_closedu
     subst_instance_univ_closedu subst_instance_closedu : substu.


Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lzero => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ^ string_of_nat n
  end.

Definition string_of_level_expr (e : LevelExpr.t) : string :=
  let '(l, n) := e in string_of_level l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition string_of_sort (u : Universe.t) :=
  match u with
  | Universe.lSProp => "SProp"
  | Universe.lProp => "Prop"
  | Universe.lType l => "Type(" ^ string_of_list string_of_level_expr (LevelExprSet.elements l) ^ ")"
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (ctx : UContext.t).
Derive NoConfusion for universes_entry.

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry (Universes.AUContext.repr ctx)
  | Monomorphic_ctx => Monomorphic_entry ContextSet.empty
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx c => fst (snd (AUContext.repr c))
  end.
(* TODO: duplicate of polymorphic_instance *)
Definition abstract_instance decl :=
  match decl with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
  end.

Definition print_universe_instance u :=
  match u with
  | [] => ""
  | _ => "@{" ^ print_list string_of_level " " u ^ "}"
  end.

Definition print_lset t :=
  print_list string_of_level " " (LevelSet.elements t).

Definition print_constraint_type d :=
  match d with
  | ConstraintType.Le n =>
    if (n =? 0)%Z then "<=" else
    if (n =? 1)%Z then "<" else
    if (n <? 0)%Z then "<=" ^ string_of_nat (Z.to_nat (Z.abs n)) ^ " + "
    else " + " ^ string_of_nat (Z.to_nat n) ^ " <= "
  | ConstraintType.Eq => "="
  end.

Definition print_constraint_set t :=
  print_list (fun '(l1, d, l2) => string_of_level l1 ^ " " ^
                         print_constraint_type d ^ " " ^ string_of_level l2)
             " /\ " (ConstraintSet.elements t).
