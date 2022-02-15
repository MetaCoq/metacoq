From Coq Require Import MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils BasicAst config.
From Equations Require Import Equations.
Require Import ssreflect.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Implicit Types (cf : checker_flags).

Ltac absurd :=
  match goal with
  | [H : False |- _] => elim H
  end.
#[global]
Hint Extern 10 => absurd : core.
(** * Valuations *)

(** A valuation is a universe level (nat) given for each
    universe variable (Level.t).
    It is >= for polymorphic universes and > 0 for monomorphic universes. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Inductive universes := 
  | UProp 
  | USProp
  | UType (i : nat).
Derive NoConfusion EqDec for universes.

Class Evaluable (A : Type) := val : valuation -> A -> nat.

(** This inductive classifies which eliminations are allowed for inductive types
  in various sorts. *)
Inductive allowed_eliminations : Set :=
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny.
Derive NoConfusion EqDec for allowed_eliminations.

(** Levels are Set or Level or Var *)
Module Level.
  Inductive t_ : Set :=
  | lzero
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices *).
  Derive NoConfusion EqDec for t_.

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

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (Level s)
  | ltSetVar n : lt_ lzero (Var n)
  | ltLevelLevel s s' : string_lt s s' -> lt_ (Level s) (Level s')
  | ltLevelVar s n : lt_ (Level s) (Var n)
  | ltVarVar n n' : Nat.lt n n' -> lt_ (Var n) (Var n').
  Derive Signature for lt_.

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

Module LevelSet := MSetAVL.Make Level.
Module LevelSetFact := WFactsOn Level LevelSet.
Module LevelSetProp := WPropertiesOn Level LevelSet.
Module LevelSetDecide := WDecide (LevelSet).
Module LS := LevelSet.
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

Module UnivExpr.
  (* npe = no prop expression *)
  Definition t := (Level.t * nat)%type.

  Global Instance Evaluable : Evaluable t
    := fun v l => (snd l + val v (fst l)).

  Definition succ (l : t) := (fst l, S (snd l)).

  Definition get_level (e : t) : Level.t := fst e.

  Definition get_noprop (e : UnivExpr.t) := Some (fst e).

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

(* We have decidable equality w.r.t leibniz equality for sets of levels.
  This means universes also have a decidable equality. *)
#[global] Instance univexprset_eq_dec : Classes.EqDec UnivExprSet.t.
Proof.
  intros p p'.
  destruct (UnivExprSet.eq_dec p p').
  - now left; eapply UnivExprSet.eq_leibniz in e.
  - right. intros ->. apply n. reflexivity.
Qed.

Module Universe.
  (** A universe is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty *)
  Record nonEmptyUnivExprSet
           := { t_set : UnivExprSet.t ;
                t_ne  : UnivExprSet.is_empty t_set = false }.

  Derive NoConfusion for nonEmptyUnivExprSet.
  
  (** This needs a propositional UIP proof to show that [is_empty = false] is a set *)
  Set Equations With UIP.
  #[global] Instance nonEmptyUnivExprSet_eqdec : EqDec nonEmptyUnivExprSet.
  Proof. eqdec_proof. Qed.

  Inductive t_ :=
    lProp | lSProp | lType (_ : nonEmptyUnivExprSet).
  Derive NoConfusion for t_.

  #[global] Instance t_eqdec : EqDec t_.
  Proof. eqdec_proof. Qed.
  
  Definition t := t_.

  Coercion t_set : nonEmptyUnivExprSet >-> UnivExprSet.t.

  Definition eqb (u1 u2 : t) : bool :=
    match u1, u2 with
    | lSProp, lSProp => true
    | lProp, lProp => true
    | lType e1, lType e2 => UnivExprSet.equal e1.(t_set) e2.(t_set)
    | _,_ => false
    end.

  Definition make' (e : UnivExpr.t) : nonEmptyUnivExprSet
    := {| t_set := UnivExprSet.singleton e;
          t_ne := eq_refl |}.

  (** Create a universe representing the given level. *)
  Definition make (l : Level.t) : t :=
    lType (make' (UnivExpr.make l)).

  Definition of_expr e := (lType (make' e)).

  Lemma not_Empty_is_empty s :
    ~ UnivExprSet.Empty s -> UnivExprSet.is_empty s = false.
  Proof.
    intro H. apply not_true_is_false. intro H'.
    apply H. now apply UnivExprSetFact.is_empty_2 in H'.
  Qed.

  Program Definition add (e : UnivExpr.t) (u : nonEmptyUnivExprSet) : nonEmptyUnivExprSet
    := {| t_set := UnivExprSet.add e u |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    eapply H. eapply UnivExprSet.add_spec.
    left; reflexivity.
  Qed.

  Definition add_to_exprs (e : UnivExpr.t) (u : t) : t :=
    match u with
    | lSProp |lProp => u
    | lType l => lType (add e l)
    end.

  Lemma add_spec e u e' :
    UnivExprSet.In e' (add e u) <-> e' = e \/ UnivExprSet.In e' u.
  Proof.
    apply UnivExprSet.add_spec.
  Qed.

  Definition add_list : list UnivExpr.t -> nonEmptyUnivExprSet -> nonEmptyUnivExprSet
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

  Definition add_list_to_exprs (es : list UnivExpr.t) (u : t) : t :=
    match u with
    | lSProp |lProp => u
    | lType l => lType (add_list es l)
    end.

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
      match u with
      | lProp | lSProp => true
      | lType l =>  UnivExprSet.for_all UnivExpr.is_level l
      end.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    match u with
    | lProp | lSProp => true
    | lType l => (UnivExprSet.cardinal l =? 1)%nat && is_levels u
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

  Definition type0 : t := make Level.lzero.
  Definition type1 : t := lType (make' UnivExpr.type1).

  Definition of_levels (l : PropLevel.t + Level.t) : t :=
    match l with
    | inl PropLevel.lSProp => lSProp
    | inl PropLevel.lProp => lProp
    | inr l => lType (make' (l, 0%nat))
    end.

  (* Used for quoting. *)
  Definition from_kernel_repr (e : Level.t * bool) (es : list (Level.t * bool)) : t
    := lType (add_list (map UnivExpr.from_kernel_repr es)
                (make' (UnivExpr.from_kernel_repr e))).

  (* Definition uex_to_kernel_repr (e : UnivExpr.t) : Level.t * bool := *)
  (*   match e with *)
  (*   | UnivExpr.npe (l, b) => (NoPropLevel.to_level l, b) *)
  (*   end. *)

  (* Definition to_kernel_repr (u : t) : list (Level.t * bool) *)
  (*   :=  map (UnivExpr.to_kernel_repr) (UnivExprSet.elements u). *)
  (* match u with *)
  (*      | lProp => [(Level.lProp, false)] *)
  (*      | lSProp => [(Level.lSProp, false)] *)
  (*      | lType l => map uex_to_kernel_repr (UnivExprSet.elements l) *)
  (*      end. *)


  (** The non empty / sorted / without dup list of univ expressions, the
      components of the pair are the head and the tail of the (non empty) list *)
  Program Definition exprs (u : nonEmptyUnivExprSet) : UnivExpr.t * list UnivExpr.t
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

  (* Lemma exprs_make l : Universe.exprs (Universe.make l) = (UnivExpr.make l, []). *)
  (* Proof. reflexivity. Defined. *)


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

  Lemma In_exprs (u : nonEmptyUnivExprSet) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (Universe.exprs u).1 \/ In e (Universe.exprs u).2.
  Proof.
    etransitivity. symmetry. apply UnivExprSet.elements_spec1.
    pose proof (Universe.exprs_spec' u) as H.
    destruct (Universe.exprs u) as [e' l]; cbn in *.
    rewrite <- H; clear. etransitivity. apply InA_cons.
    eapply or_iff_compat_l. apply InA_In_eq.
  Qed.

  Lemma In_exprs_rev (u : nonEmptyUnivExprSet) (e : UnivExpr.t) :
    UnivExprSet.In e u
    <-> e = (Universe.exprs u).1 \/ In e (List.rev (Universe.exprs u).2).
  Proof.
    etransitivity. eapply In_exprs.
    apply or_iff_compat_l. apply in_rev.
  Qed.

  Definition map (f : UnivExpr.t -> UnivExpr.t) (u : nonEmptyUnivExprSet) : nonEmptyUnivExprSet :=
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
    match l with
    | lSProp => type1
    | lProp => type1
    | lType l => lType (map UnivExpr.succ l)
    end.

  (** The l.u.b. of 2 non-prop universe sets *)
  Program Definition sup0 (u v : nonEmptyUnivExprSet) : nonEmptyUnivExprSet :=
    {| t_set := UnivExprSet.union u v |}.
  Next Obligation.
    apply not_Empty_is_empty; intro H.
    assert (HH: UnivExprSet.Empty u). {
      intros x Hx. apply (H x).
      eapply UnivExprSet.union_spec. now left. }
    apply UnivExprSetFact.is_empty_1 in HH.
    rewrite t_ne in HH; discriminate.
  Qed.

  Definition sup (u v : t) : t :=
    match u,v with
    | lSProp, lProp => lProp
    | lProp, lSProp => lProp
    | (lSProp | lProp), u' => u'
    | u', (lSProp | lProp) => u'
    | lType l1, lType l2  => lType (sup0 l1 l2)
    end.

  Definition get_univ_exprs (u : t) (H1 : is_prop u = false) (H2 : is_sprop u = false) : nonEmptyUnivExprSet.
  destruct u; try discriminate;easy. Defined.

  (** Type of a product *)
  Definition sort_of_product (domsort rangsort : t) :=
    (* Prop and SProp impredicativity *)
    if Universe.is_prop rangsort || Universe.is_sprop rangsort then rangsort
    else Universe.sup domsort rangsort.

  Lemma eqb_refl u : eqb u u.
  Proof.
    destruct u;auto.
    now apply UnivExprSet.equal_spec.
  Qed.

  Lemma elements_not_empty (u : Universe.nonEmptyUnivExprSet) : UnivExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold UnivExprSet.is_empty, UnivExprSet.elements,
    UnivExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
  Qed.

  Definition get_is_level (u : t) : option Level.t :=
    match u with
    | lSProp => None
    | lProp => None
    | lType l => match UnivExprSet.elements l with
                 [(l, 0%nat)] => Some l
               | _ => None
               end
    end.

  Global Instance Evaluable' : Evaluable nonEmptyUnivExprSet
    := fun v u => let '(e, u) := Universe.exprs u in
               List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  Definition univ_val :=
    fun v u => match u with
            | lSProp => USProp
            | lProp => UProp
            | lType l => UType (val v l)
            end.

  Lemma val_make' v e
    : val v (make' e) = val v e.
  Proof.
    reflexivity.
  Qed.

  Lemma val_make v l
    : univ_val v (make l) = UType (val v l).
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma val_make_npl v (l : Level.t)
    : univ_val v (make l) = UType (val v l).
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

(** This coercion allows to see the universes as a [UnivExprSet.t] *)
Coercion Universe.t_set : Universe.nonEmptyUnivExprSet >-> UnivExprSet.t.

Declare Scope univ_scope.
Delimit Scope univ_scope with u.

Notation "⟦ u ⟧_ v" := (Universe.univ_val v u) (at level 0, format "⟦ u ⟧_ v", v name) : univ_scope.

Ltac u :=
 change LevelSet.elt with Level.t in *;
 change UnivExprSet.elt with UnivExpr.t in *.
 (* change ConstraintSet.elt with UnivConstraint.t in *. *)


Lemma val_fold_right (u : Universe.nonEmptyUnivExprSet) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (Universe.exprs u).1)
                       (List.rev (Universe.exprs u).2).
Proof.
  unfold val at 1, Universe.Evaluable'.
  destruct (Universe.exprs u).
  now rewrite fold_left_rev_right.
Qed.

Lemma val_In_le (u : Universe.nonEmptyUnivExprSet) v e :
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

Lemma val_In_max (u : Universe.nonEmptyUnivExprSet) v :
  exists e, UnivExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply Universe.In_exprs_rev. }
  rewrite val_fold_right. destruct (Universe.exprs u) as [e l]; cbn in *.
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

Lemma val_ge_caract (u : Universe.nonEmptyUnivExprSet) v k :
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
      destruct (Nat.max_dec (val v a) (fold_right (fun e0 x => Nat.max (val v e0) x)
                                                 (val v e) l0)) as [H'|H'];
        rewrite H'; clear H'.
      * apply H. right. now constructor.
      * apply IHl0. intros x [H0|H0]; apply H. now left.
        right; now constructor 2.
  - intros H e He. eapply val_In_le in He. etransitivity; eassumption.
Qed.

Lemma val_le_caract (u : Universe.nonEmptyUnivExprSet) v k :
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



Lemma val_caract (u : Universe.nonEmptyUnivExprSet) v k :
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
  : val v (Universe.add e s) = Nat.max (val v e) (val v s).
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
  val v (Universe.sup0 s1 s2) = Nat.max (val v s1) (val v s2).
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

Ltac proper := let H := fresh in try (intros ? ? H; destruct H; reflexivity).

Lemma for_all_elements (P : UnivExpr.t -> bool) u :
  UnivExprSet.for_all P u = forallb P (UnivExprSet.elements u).
Proof.
  apply UnivExprSetFact.for_all_b; proper.
Qed.

Definition univ_val_max v1 v2 :=
  match v1, v2 with
  | UProp, UProp => UProp
  | USProp, USProp => USProp
  | UType v, UType v' => UType (Nat.max v v')
  | _, UType _ => v2
  | UType _, _ => v1
  | UProp, USProp => UProp
  | USProp, UProp => UProp
  end.

Lemma val_universe_sup v u1 u2 :
  Universe.univ_val v (Universe.sup u1 u2) = univ_val_max (Universe.univ_val v u1) (Universe.univ_val v u2).
Proof.
  destruct u1 as [ | | l1]; destruct u2 as [ | | l2];cbn;try lia; auto.
  f_equal. apply val_sup.
Qed.

Lemma is_prop_val u :
  Universe.is_prop u -> forall v, Universe.univ_val v u = UProp.
Proof.
  destruct u as [| | u];try discriminate;auto.
Qed.

Lemma is_sprop_val u :
  Universe.is_sprop u -> forall v, Universe.univ_val v u = USProp.
Proof.
  destruct u as [| | u];try discriminate;auto.
Qed.

(* 
Lemma val_zero_exprs v (l : Universe.nonEmptyUnivExprSet) : 0 <= val v l.
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


Lemma val_is_prop u v :
  Universe.univ_val v u = UProp <-> Universe.is_prop u.
Proof.
  destruct u; auto;cbn in *; intuition congruence.
Qed.

Lemma val_is_sprop u v :
  Universe.univ_val v u = USProp <-> Universe.is_sprop u.
Proof.
  destruct u;auto;cbn in *; intuition congruence.
Qed.

Lemma is_prop_and_is_sprop_val_false u :
  Universe.is_prop u = false -> Universe.is_sprop u = false -> 
  forall v, ∑ n, Universe.univ_val v u = UType n.
Proof.
  intros Hp Hsp v.
  destruct u; try discriminate. simpl. eexists; eauto.
Qed.

Lemma val_is_prop_false u v n :
  Universe.univ_val v u = UType n -> Universe.is_prop u = false.
Proof.
  pose proof (is_prop_val u) as H. destruct (Universe.is_prop u); cbnr.
  rewrite (H eq_refl v). discriminate.
Qed.

Lemma eq_univ (u v : Universe.nonEmptyUnivExprSet) :
  u = v :> UnivExprSet.t -> u = v.
Proof.
  destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
  now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma eq_univ' (u v : Universe.nonEmptyUnivExprSet) :
  UnivExprSet.Equal u v -> u = v.
Proof.
  intro H. now apply eq_univ, UnivExprSet.eq_leibniz.
Qed.

Lemma eq_univ'' (u v : Universe.nonEmptyUnivExprSet) :
  UnivExprSet.elements u = UnivExprSet.elements v -> u = v.
Proof.
  intro H. apply eq_univ.
  destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
  destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
  destruct H. now rewrite (uip_bool _ _ u2 v2).
Qed.

Lemma get_is_level_correct u l :
  Universe.get_is_level u = Some l -> u = Universe.make l.
Proof.
  intro H.
  destruct u eqn:Hu;cbn in *.
  - inversion H;subst;reflexivity.
  - inversion H;subst;reflexivity.
  - unfold Universe.make.
    destruct (UnivExprSet.elements _) as [|l0 L] eqn:Hu1; [discriminate|].
    destruct l0, L; try discriminate.
    * destruct n,n0;inversion H;subst.
      apply f_equal.
      apply eq_univ'';unfold UnivExpr.make.
      cbn. simpl in Hu1. rewrite Hu1. reflexivity.
    * destruct e,n0;inversion H;subst.
Qed.

Lemma univ_expr_eqb_true_iff (u v : Universe.nonEmptyUnivExprSet) :
  UnivExprSet.equal u v <-> u = v.
Proof.
  split.
  - intros.
    apply eq_univ'. now apply UnivExprSet.equal_spec.
  - intros ->. now apply UnivExprSet.equal_spec.
Qed.

Lemma eqb_true_iff u v :
  Universe.eqb u v <-> u = v.
Proof.
  split. 2: intros ->; apply Universe.eqb_refl.
  intro H.
  destruct u,v;auto;try discriminate.
  apply f_equal. now apply univ_expr_eqb_true_iff.
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

Lemma UnivExprSet_For_all_exprs (P : UnivExpr.t -> Prop) (u : Universe.nonEmptyUnivExprSet)
  : UnivExprSet.For_all P u
    <-> P (Universe.exprs u).1 /\ Forall P (Universe.exprs u).2.
Proof.
  etransitivity.
  - eapply iff_forall; intro e. eapply imp_iff_compat_r.
    apply Universe.In_exprs.
  - cbn; split.
    + intro H. split. apply H. now left.
      apply Forall_forall. intros x H0.  apply H; now right.
    + intros [H1 H2] e [He|He]. subst e; tas.
      eapply Forall_forall in H2; tea.
Qed.

Lemma sup0_comm x1 x2 :
  Universe.sup0 x1 x2 = Universe.sup0 x2 x1.
Proof.
  apply eq_univ'; simpl. unfold UnivExprSet.Equal.
  intros H. rewrite !UnivExprSet.union_spec. intuition.
Qed.

Lemma sup_comm x1 x2 :
  Universe.sup x1 x2 = Universe.sup x2 x1.
Proof.
  destruct x1,x2;auto.
  cbn;apply f_equal;apply sup0_comm.
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

Module ConstraintSet := MSetAVL.Make UnivConstraint.
Module ConstraintSetFact := WFactsOn UnivConstraint ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraint ConstraintSet.
Module CS := ConstraintSet.

Lemma CS_union_empty s : ConstraintSet.Equal (ConstraintSet.union ConstraintSet.empty s) s.
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

#[global] Instance CS_For_all_proper P : Morphisms.Proper (CS.Equal ==> iff)%signature (ConstraintSet.For_all P).
Proof.
  intros s s' eqs.
  unfold CS.For_all. split; intros IH x inxs; apply (IH x);
  now apply eqs.
Qed.

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
  Definition t := list name × ConstraintSet.t.

  Definition make (ids : list name) (ctrs : ConstraintSet.t) : t := (ids, ctrs).
  Definition repr (x : t) : UContext.t :=
    let (u, cst) := x in
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
  Derive NoConfusion EqDec for t.

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.

Inductive universes_decl : Type :=
| Monomorphic_ctx (ctx : ContextSet.t)
| Polymorphic_ctx (cst : AUContext.t).

Derive NoConfusion for universes_decl.

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
  | Polymorphic_ctx ctx => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => snd ctx
  | Polymorphic_ctx ctx => snd (AUContext.repr ctx)
  end.

Definition univ_le_n {cf:checker_flags} n u u' := 
  match u, u' with
  | UProp, UProp
  | USProp, USProp => (n = 0)%Z
  | UType u, UType u' => (Z.of_nat u <= Z.of_nat u' - n)%Z
  | UProp, UType u => 
    if prop_sub_type then True else False
  | _, _ => False
  end.

Notation "x <_ n y" := (univ_le_n n x y) (at level 10, n name) : univ_scope.
Notation "x < y" := (univ_le_n 1 x y) : univ_scope.
Notation "x <= y" := (univ_le_n 0 x y) : univ_scope.

Ltac lle := unfold univ_le_n in *.
Ltac lled := lle; match goal with
                  | H : prop_sub_type = true |- _ => rewrite H in *
                  | H : prop_sub_type = false |- _ => rewrite H in *
                  | H : is_true prop_sub_type |- _ => rewrite H in *
                  | _ => destruct prop_sub_type eqn:?Hb
                  end.

Ltac prop_non_prop :=
  match goal with
  | |- context[ Universe.is_prop ?u || Universe.is_sprop ?u]  =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  | H : context[ Universe.is_prop ?u || Universe.is_sprop ?u] |- _ =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  end.

Section Univ.
  Context {cf:checker_flags}.

  Global Instance lle_refl : Reflexive (univ_le_n 0).
  Proof.
    intro x. destruct x; simpl; lia.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof. split; lia. Qed.


  Global Instance le_n_trans n : Transitive (univ_le_n (Z.of_nat n)).
  Proof.
    intros [] [] []; unfold univ_le_n; simpl; try lia; try (destruct prop_sub_type; lia).
  Qed.

  Global Instance lle_trans : Transitive (univ_le_n 0).
  Proof. apply (le_n_trans 0). Qed.

  Global Instance llt_trans : Transitive (univ_le_n 1).
  Proof. apply (le_n_trans 1). Qed.

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

  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition eq_universe0 (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Universe.univ_val v u = Universe.univ_val v u').

  Definition leq_universe_n n (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (univ_le_n n (Universe.univ_val v u) (Universe.univ_val v u'))%u.

  Definition leq_universe0 (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Universe.univ_val v u <= Universe.univ_val v u')%u.

  Lemma leq_universe0_leq_universe_n (φ : ConstraintSet.t) u u' :
    leq_universe0 φ u u' <-> leq_universe_n 0 φ u u'.
  Proof. intros. reflexivity. Qed.

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
    intros s vH;cbn;reflexivity.
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
    intro H; split; intros v Hv; specialize (H v Hv); now rewrite H.
    intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
    unfold univ_le_n in *.
    destruct (Universe.univ_val v u), (Universe.univ_val v u'); try now auto.
  Qed.

  Lemma leq_universe0_sup_l φ s1 s2 :
    Universe.is_prop s1 = false -> Universe.is_sprop s1 = false -> 
    leq_universe0 φ s1 (Universe.sup s1 s2).
  Proof.
    intros H1 H2 v Hv.
    specialize (is_prop_and_is_sprop_val_false _ H1 H2 v) as [n Hzero].
    rewrite val_universe_sup Hzero. destruct (Universe.univ_val v s2); simpl; lia.
  Qed.

  Lemma leq_universe0_sup_r φ s1 s2 :
    Universe.is_prop s2 = false -> Universe.is_sprop s2 = false -> 
    leq_universe0 φ s2 (Universe.sup s1 s2).
  Proof.
    intros H1 H2 v Hv.
    specialize (is_prop_and_is_sprop_val_false _ H1 H2 v) as [n Hzero].
    rewrite val_universe_sup Hzero.
    destruct (Universe.univ_val v s1); simpl; lia.
  Qed.

  Lemma leq_universe0_sup_l' φ (s1 s2 : Universe.nonEmptyUnivExprSet) :
    leq_universe0 φ (Universe.lType s1) (Universe.lType (Universe.sup0 s1 s2)).
  Proof.
    intros v Hv. cbn. rewrite val_sup. lia.
  Qed.

  Lemma leq_universe0_sup_r' φ (s1 s2 : Universe.nonEmptyUnivExprSet) :
    leq_universe0 φ (Universe.lType s2) (Universe.lType (Universe.sup0 s1 s2)).
  Proof.
    intros v Hv. cbn. rewrite val_sup. lia.
  Qed.

  Lemma leq_universe_product φ (s1 s2 : Universe.t)
    : leq_universe φ s2 (Universe.sort_of_product s1 s2).
  Proof.
    unfold leq_universe; destruct check_univs; [cbn|constructor].
    unfold Universe.sort_of_product.
    destruct s2; cbn; try apply leq_universe0_refl.
    destruct s1;cbn;try apply leq_universe0_refl.
    apply leq_universe0_sup_r'.
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

  Global Instance llt_str_order : StrictOrder (univ_le_n 1).
  Proof.
    split.
    - intros x H. destruct x; simpl in *; lia.
    - exact _.
  Qed.


  Global Instance lle_antisym : Antisymmetric _ eq (univ_le_n 0).
  Proof.
    intros [] []; simpl; try reflexivity; auto.
    intros. f_equal; lia.
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

  Definition eq_universe_leq_universe' φ u u'
    := @eq_universe_leq_universe φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_universe_leq_universe' leq_universe_refl' : core.

  (** Elimination restriction *)

  Definition is_allowed_elimination0
             φ (into : Universe.t) (allowed : allowed_eliminations) : Prop :=
    forall v,
      satisfies v φ ->
      match allowed, Universe.univ_val v into with
      | IntoSProp, USProp
      | IntoPropSProp, (UProp | USProp)
      | IntoSetPropSProp, (UProp | USProp | UType 0)
      | IntoAny, _ => True
      | _, _ => False
      end.
  
  Definition is_allowed_elimination φ into allowed :=
    if check_univs then is_allowed_elimination0 φ into allowed else True.
  
  (* Is [a] a subset of [a']? *)
  Definition allowed_eliminations_subset (a a' : allowed_eliminations) : bool :=
    match a, a' with
    | IntoSProp, _
    | IntoPropSProp, (IntoPropSProp | IntoSetPropSProp | IntoAny)
    | IntoSetPropSProp, (IntoSetPropSProp | IntoAny)
    | IntoAny, IntoAny => true
    | _, _ => false
    end.

End Univ.

(* This universe is a hack used in plugings to generate fresh universes *)
Definition fresh_universe : Universe.t. exact Universe.type0. Qed.
(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t. exact Level.lzero. Qed.


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

#[global] Instance subst_instance_level_expr : UnivSubst UnivExpr.t :=
  fun u e => match e with
          | (Level.lzero, _)
          | (Level.Level _, _) => e
          | (Level.Var n, b) =>
            match nth_error u n with
            | Some l => (l,b)
            | None => (Level.lzero, b)
            end
          end.

#[global] Instance subst_instance_univ0 : UnivSubst Universe.nonEmptyUnivExprSet :=
  fun u => Universe.map (subst_instance_level_expr u).

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

  Definition closedu_level_expr (s : UnivExpr.t) :=
    closedu_level (UnivExpr.get_level s).

  Definition closedu_universe_levels (u : Universe.nonEmptyUnivExprSet) :=
    UnivExprSet.for_all closedu_level_expr u.

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
    destruct s;auto;cbn in *.
    apply f_equal. apply eq_univ'.
    destruct n as [ts H1].
    unfold closedu_universe_levels in *;cbn in *.
    intro e; split; intro He.
    - apply Universe.map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      apply UnivExprSet.for_all_spec in H; proper.
      exact (H _ He').
      now subst. 
    - apply Universe.map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply UnivExprSet.for_all_spec in H; proper. now apply H.
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
  Proof.
    destruct l; cbnr.
    unfold closedu_instance in Hcl.
    destruct (nth_in_or_default n u Level.lzero).
    - intros _. eapply forallb_forall in Hcl; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_level_expr_closedu e :
    closedu_level_expr #|u| e -> closedu_level_expr 0 (subst_instance_level_expr u e).
  Proof.
    destruct e as [l b]. destruct l;cbnr.
    case_eq (nth_error u n); cbnr. intros [] Hl X; cbnr.
    apply nth_error_In in Hl.
    eapply forallb_forall in Hcl; tea.
    discriminate.
  Qed.

  Lemma subst_instance_univ_closedu s
    : closedu_universe #|u| s -> closedu_universe 0 (subst_instance_univ u s).
  Proof.
    intro H.
    destruct s;cbnr.
    destruct n as [l Hl].
    apply UnivExprSet.for_all_spec; proper.
    intros e He. eapply Universe.map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply UnivExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.

  Lemma subst_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance u t).
  Proof.
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

Definition string_of_level_expr (e : UnivExpr.t) : string :=
  let '(l, n) := e in string_of_level l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition string_of_sort (u : Universe.t) :=
  match u with
  | Universe.lSProp => "SProp"
  | Universe.lProp => "Prop"
  | Universe.lType l => "Type(" ^ string_of_list string_of_level_expr (UnivExprSet.elements l) ^ ")"
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (names : list name) (ctx : UContext.t).
Derive NoConfusion for universes_entry.

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry (fst ctx) (Universes.AUContext.repr ctx)
  | Monomorphic_ctx ctx => Monomorphic_entry ctx
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx c => Instance.empty
  | Polymorphic_ctx c => fst (AUContext.repr c)
  end.
(* todo: duplicate of polymorphic_instance *)
Definition abstract_instance decl :=
  match decl with
  | Monomorphic_ctx _ => Instance.empty
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
 
Lemma val_universe_sup_not_prop vv v u :
  Universe.is_prop v = false -> Universe.is_sprop v = false ->
  ∑ n, Universe.univ_val vv (Universe.sup u v) = UType n.
Proof.
  intros Hp Hsp.
  destruct u,v;cbn;try discriminate;try lia; try apply val_zero_exprs;
  eexists; eauto.
Qed.

Lemma univ_le_prop_inv {cf:checker_flags} u : (u <= UProp)%u -> u = UProp.
Proof. destruct u; simpl; try congruence; auto. Qed.

Lemma univ_le_sprop_inv {cf:checker_flags} u : (u <= USProp)%u -> u = USProp.
Proof. destruct u; simpl; try congruence; auto. Qed.

Lemma univ_prop_le_inv {cf:checker_flags} u : (UProp <= u)%u -> 
  (u = UProp \/ (prop_sub_type /\ exists n, u = UType n)).
Proof. destruct u; simpl; try congruence; auto.
  destruct prop_sub_type; firstorder auto.
  right; split; auto. exists i. auto.
Qed.

Ltac cong := intuition congruence.

Lemma univ_val_max_mon {cf:checker_flags} u u' v v' : (u <= u')%u -> (UType v <= UType v')%u -> 
  (univ_val_max u (UType v) <= univ_val_max u' (UType v'))%u.
Proof.
  intros.
  destruct u, u'; simpl in *; auto. lia. lia.
Qed.

Lemma leq_universe_product_mon {cf: checker_flags} ϕ u u' v v' :
  leq_universe ϕ u u' ->
  leq_universe ϕ v v' ->
  leq_universe ϕ (Universe.sort_of_product u v) (Universe.sort_of_product u' v').
Proof.
  unfold leq_universe in *; destruct check_univs; [|trivial].
  intros H1 H2 vv Hv. specialize (H1 _ Hv). specialize (H2 _ Hv).
  cbn in *. unfold Universe.sort_of_product.
  destruct (Universe.is_prop v) eqn:e, (Universe.is_prop v') eqn:f;
    destruct (Universe.is_sprop v) eqn:e1, (Universe.is_sprop v') eqn:f1;
    rewrite ?val_universe_sup;cbn; rewrite ?val_universe_sup; auto.
  - destruct v;discriminate.
  - apply is_prop_val with (v:=vv) in e.
    specialize (is_prop_and_is_sprop_val_false _ f f1 vv) as [n HH].
    rewrite e HH.
    rewrite e HH in H2. simpl in H2.
    simpl. destruct (Universe.univ_val vv u') eqn:eq; simpl; auto.
  - destruct v';discriminate.
  - apply is_prop_val with (v:=vv) in f.
    specialize (is_prop_and_is_sprop_val_false _ e e1 vv) as [n HH].
    rewrite f in H2. eapply univ_le_prop_inv in H2. cong.
  - apply is_sprop_val with (v:=vv) in e1.
    specialize (is_prop_and_is_sprop_val_false _ f f1 vv) as [n HH].
    rewrite HH e1 in H2. now simpl in H2.
  - apply is_sprop_val with (v:=vv) in f1.
    specialize (is_prop_and_is_sprop_val_false _ e e1 vv) as [n HH].
    rewrite f1 in H2. apply univ_le_sprop_inv in H2; cong.
  - specialize (is_prop_and_is_sprop_val_false _ e e1 vv) as [n HH].
    specialize (is_prop_and_is_sprop_val_false _ f f1 vv) as [n' HH'].
    rewrite HH HH'. apply univ_val_max_mon; auto.
    now rewrite <- HH, <- HH'.
Qed.

Lemma impredicative_product {cf:checker_flags} {ϕ l u} :
  Universe.is_prop u ->
  leq_universe ϕ (Universe.sort_of_product l u) u.
Proof.
  unfold Universe.sort_of_product.
  intros ->. reflexivity.
Qed.

Section UniverseLemmas.
  Context {cf:checker_flags}.

  Ltac unfold_eq_universe
    := unfold eq_universe in *; destruct check_univs; [intros v Hv|trivial].

  Lemma sup0_idem s : Universe.sup0 s s = s.
  Proof.
    apply eq_univ'; cbn.
    intro; rewrite !UnivExprSet.union_spec. intuition.
  Qed.

  Lemma sup_idem s : Universe.sup s s = s.
  Proof.
    destruct s;cbn;auto.
    apply f_equal.
    apply eq_univ'; cbn.
    intro; rewrite !UnivExprSet.union_spec. intuition.
  Qed.

  Lemma sort_of_product_idem s
    : Universe.sort_of_product s s = s.
  Proof.
    unfold Universe.sort_of_product.
    destruct (Universe.is_prop s), (Universe.is_sprop s); trea;cbn.
    apply sup_idem.
  Qed.

  Lemma sup0_assoc s1 s2 s3 :
    Universe.sup0 s1 (Universe.sup0 s2 s3) = Universe.sup0 (Universe.sup0 s1 s2) s3.
  Proof.
    apply eq_univ'; cbn. symmetry; apply UnivExprSetProp.union_assoc.
  Qed.

  Instance universe_sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) Universe.sup.
  Proof.
    intros s1 s1' H1 s2 s2' H2.
    unfold_eq_universe. specialize (H1 v Hv). specialize (H2 v Hv).
    rewrite !val_universe_sup.
    now rewrite H1 H2.
  Qed.

  Lemma sort_of_product_twice u s :
    Universe.sort_of_product u (Universe.sort_of_product u s)
    = Universe.sort_of_product u s.
  Proof.
    destruct u,s;auto.
    unfold Universe.sort_of_product;cbn.
    now rewrite sup0_assoc sup0_idem.
  Qed.
End UniverseLemmas.


Section no_prop_leq_type.
  Context {cf:checker_flags}.
  Context (ϕ : ConstraintSet.t).

  Lemma succ_inj x y : UnivExpr.succ x = UnivExpr.succ y -> x = y.
  Proof.
    unfold UnivExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x : 
    UnivExprSet.In x (Universe.map UnivExpr.succ l) <-> 
    exists x', UnivExprSet.In x' l /\ x = UnivExpr.succ x'.
  Proof.
    rewrite Universe.map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (UnivExpr.succ l) = val v l + 1.
  Proof.
    destruct l as []; simpl. cbn. lia. 
  Qed.

  Lemma val_map_succ v l : val v (Universe.map UnivExpr.succ l) = val v l + 1.
  Proof.
    remember (Universe.map UnivExpr.succ l) eqn:eq.
    pose proof (spec_map_succ l). rewrite <- eq in H.
    clear eq.
    destruct (val_In_max l v) as [max [inmax eqv]]. rewrite <-eqv.
    rewrite val_caract. split.
    intros.
    specialize (proj1 (H _) H0) as [x' [inx' eq]]. subst e.
    rewrite val_succ. eapply (val_In_le _ v) in inx'. rewrite <- eqv in inx'.
    simpl in *. unfold UnivExprSet.elt, UnivExpr.t in *. lia.
    exists (UnivExpr.succ max). split. apply H.
    exists max; split; auto.
    now rewrite val_succ.
  Qed.
  
  Lemma leq_universe_super u u' :
    leq_universe ϕ u u' ->
    leq_universe ϕ (Universe.super u) (Universe.super u').
  Proof.
    unfold leq_universe. destruct check_univs; [|trivial].
    intros H v Hv. specialize (H v Hv). simpl in *.
    destruct u as [| |], u' as  [| |]; lled; cbn -[Z.add] in *; try lia;
    rewrite !val_map_succ; lia.
  Qed.

  Lemma leq_universe_props u1 u2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ u1 u2 ->
    match u1, u2 with
    | Universe.lProp, Universe.lProp => True
    | Universe.lSProp, Universe.lSProp => True
    | Universe.lProp, Universe.lSProp => False
    | Universe.lSProp, Universe.lProp => False
    | Universe.lProp, Universe.lType _ => prop_sub_type
    | Universe.lSProp, Universe.lType _ => False
    | Universe.lType l, Universe.lType l' => True
    | Universe.lType _, _ => False
    end.
  Proof.
    intros cu [v Hv].
    unfold leq_universe. rewrite cu.
    intros Hle. specialize (Hle _ Hv).
    destruct u1, u2; simpl; auto.
    simpl in Hle. now destruct prop_sub_type.
  Qed.

  Lemma leq_universe_prop_r u1 u2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ u1 u2 ->
    Universe.is_prop u2 -> Universe.is_prop u1.
  Proof.
    intros Hcf cu le.
    apply leq_universe_props in le; auto.
    destruct u1, u2; simpl in *; auto.
  Qed.

  Lemma leq_universe_sprop_r u1 u2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ u1 u2 ->
    Universe.is_sprop u2 -> Universe.is_sprop u1.
  Proof.
    intros Hcf cu le.
    apply leq_universe_props in le; auto.
    destruct u1, u2; simpl in *; auto.
  Qed.
  
  Lemma leq_universe_prop_no_prop_sub_type u1 u2 :
    check_univs ->
    prop_sub_type = false ->
    consistent ϕ ->
    leq_universe ϕ u1 u2 ->
    Universe.is_prop u1 -> Universe.is_prop u2.
  Proof.
    intros Hcf cu ps le.
    apply leq_universe_props in le; auto.
    destruct u1, u2; simpl in *; auto.
    cong.
  Qed.

  Lemma leq_universe_sprop_l u1 u2 :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ u1 u2 ->
    Universe.is_sprop u1 -> Universe.is_sprop u2.
  Proof.
    intros Hcf cu le.
    apply leq_universe_props in le; auto.
    destruct u1, u2; simpl in *; auto.
  Qed.

  Hint Resolve leq_universe_sprop_l leq_universe_sprop_r
       leq_universe_prop_r
       leq_universe_prop_no_prop_sub_type
       : univ_lemmas.
  
  Lemma leq_prop_prop {l l'} :
    Universe.is_prop l -> Universe.is_prop l' ->
    leq_universe ϕ l l'.
  Proof.
    red. destruct check_univs; [|trivial].
    intros H1 H2 v Hv. eapply is_prop_val in H1; eapply is_prop_val in H2.
    rewrite -> H1, H2. lled; lia.
  Qed.

  Lemma leq_sprop_sprop {l l'} :
    Universe.is_sprop l -> Universe.is_sprop l' ->
    leq_universe ϕ l l'.
  Proof.
    red. destruct check_univs; [|trivial].
    intros H1 H2 v Hv. eapply is_sprop_val in H1; eapply is_sprop_val in H2.
    rewrite -> H1, H2. lled; lia.
  Qed.
  
  Lemma leq_prop_is_prop_sprop {x s} :
    check_univs ->
    prop_sub_type = false ->
    consistent ϕ ->
    leq_universe ϕ x s ->
    (Universe.is_prop s \/ Universe.is_sprop s <-> Universe.is_prop x \/ Universe.is_sprop x).
  Proof.
    intros H H0 H1 H2; split;intros Hor; destruct Hor; eauto with univ_lemmas.
  Qed.

  Lemma is_prop_gt l l' :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ (Universe.super l) l' -> Universe.is_prop l' -> False.
  Proof.
    intros Hcf [v Hv] H1 H2. rewrite /leq_universe Hcf in H1.
    eapply is_prop_val with (v:=v) in H2. specialize (H1 _ Hv).
    rewrite H2 in H1. destruct l as [| |]; destruct l'; lled; cbn -[Z.add] in *; lia.
  Qed.
  
  Lemma is_sprop_gt l l' :
    check_univs ->
    consistent ϕ ->
    leq_universe ϕ (Universe.super l) l' -> Universe.is_sprop l' -> False.
  Proof.
    intros Hcf [v Hv] H1 H2. rewrite /leq_universe Hcf in H1.
    eapply is_sprop_val with (v:=v) in H2. specialize (H1 _ Hv).
    rewrite H2 in H1. destruct l as [| |]; destruct l'; lled; cbn -[Z.add] in *; lia.
  Qed.

End no_prop_leq_type.

Definition compare_universe {cf:checker_flags} (pb : conv_pb) :=
  match pb with
  | Conv => eq_universe
  | Cumul => leq_universe
  end.
  
#[global] Instance compare_universe_subrel {cf} pb Σ : RelationClasses.subrelation (eq_universe Σ) (compare_universe pb Σ).
Proof.
  destruct pb; tc.
Qed.

#[global]
Instance compare_universe_refl {cf} pb Σ : RelationClasses.Reflexive (compare_universe pb Σ).
Proof.
  destruct pb; tc.
Qed.

#[global]
Instance compare_universe_trans {cf} pb Σ : RelationClasses.Transitive (compare_universe pb Σ).
Proof.
  destruct pb; tc.
Qed.

#[global]
Instance compare_universe_preorder {cf} pb Σ : RelationClasses.PreOrder (compare_universe pb Σ).
Proof.
  destruct pb; tc.
Qed.