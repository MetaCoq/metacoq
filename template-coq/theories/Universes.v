From Coq Require Import MSetList MSetFacts MSetProperties MSetDecide.
From Coq Require Import Structures.OrdersEx.
From MetaCoq.Template Require Import utils BasicAst config.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Local Open Scope nat_scope.
Local Open Scope string_scope2.


Ltac absurd :=
  match goal with
  | [H : False |- _] => elim H
  end.
Hint Extern 10 => absurd : core.
(** * Valuations *)

Inductive universe_family :=
  | UProp
  | USProp
  | UType
  | UGlobal (_ : string) (* name of a global sort *).
Derive NoConfusion EqDec for universe_family.

Definition is_impredicative (u : universe_family) :=
  match u with
  | UProp | USProp => true
  | _ => false
  end.

(** A valuation is a universe level (nat) given for each universe variable
    (Level.t) and a sort family (universe_family) for each sort variables.
    It is >= for polymorphic universes and > 0 for monomorphic universes. *)
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat ;
    valuation_sort : nat -> universe_family }.

Definition universes : Type := universe_family * nat.

Class Evaluable (A : Type) := val : valuation -> A -> nat.

(** This inductive classifies which eliminations are allowed for inductive types
  in various sorts. *)
(* KM: will be managed by universe family constraints instead *)
Inductive allowed_eliminations : Set :=
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny.
Derive NoConfusion EqDec for allowed_eliminations.

Definition globally_eliminable (u1 u2 : universe_family) : bool :=
  match u1, u2 with
  | UType, _
  | UProp, (UProp | USProp)
  | USProp, USProp => true
  | UGlobal s1, UGlobal s2 => (s1 =? s2)%string
  | _, _ => false
  end.

Inductive global_sort_elimination : forall(u1 u2 : universe_family), Prop :=
(* caveat there are 2 ways to derive that Type is eliminable into Type *)
 | GSERefl u : global_sort_elimination u u
 | GSETypeInitial u : global_sort_elimination UType u
 | GSEPropSProp : global_sort_elimination UProp USProp
 (* | GSEMedExn : global_sort_elimination (UGlobal "med") (UGlobal "exn") *)
 .

Lemma global_sort_eliminationP u1 u2 : reflect (global_sort_elimination u1 u2) (globally_eliminable u1 u2).
Proof.
  case: u1 u2=> [|||s1][|||s2] /=; last case: (eqb_spec s1 s2)=> [->|hs]; constructor; try constructor.
  all:move=> h; depelim h.
  apply hs; reflexivity.
Qed.

(* Goal forall u1 u2, globally_eliminable u1 u2 -> global_sort_elimination u1 u2.
Proof.
  (* f : A -> B
    Goal : A -> ...
  *)
  (* move=> /f. *)
  (* Goal : B -> ... *)
  move=> u1 u2 /global_sort_eliminationP.
  apply/global_sort_eliminationP. *)


(** * Sorts *)


Module SortFamily.

  (* Putting both Prop and SProp for simplifying the modification
     Consider replacing Prop by an impredicative sort and defining
     Prop as a global sort above this impredicative sort.
     (SProp does have some specific handling in conversion so it
     might be better to keep it)
   *)
  Inductive t_ :=
  | sfProp
  | sfSProp
  | sfType
  | sfGlobal (_ : string) (* name of a global sort *)
  | sfVar (_ : nat)(* these are debruijn indices *).
  Derive NoConfusion EqDec for t_.

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | ltSFTypeProp : lt_ sfType sfProp
  | ltSFTypeSProp : lt_ sfType sfSProp
  | ltSFTypeGlobal (s : string) : lt_ sfType (sfGlobal s)
  | ltSFTypeVar (n : nat) : lt_ sfType (sfVar n)
  | ltSFPropSProp : lt_ sfProp sfSProp
  | ltSFPropGlobal (s : string) : lt_ sfProp (sfGlobal s)
  | ltSFPropVar (n : nat) : lt_ sfProp (sfVar n)
  | ltSFSPropGlobal (s : string) : lt_ sfSProp (sfGlobal s)
  | ltSFSPropVar (n : nat) : lt_ sfSProp (sfVar n)
  | ltSFGlobalGlobal (s1 s2 : string) : string_lt s1 s2 -> lt_ (sfGlobal s1) (sfGlobal s2)
  | ltSFGlobalVar (s: string) (n : nat) : lt_ (sfGlobal s) (sfVar n)
  | ltSFVarVar (n1 n2 : nat) : Nat.lt n1 n2 -> lt_ (sfVar n1) (sfVar n2).

  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; intro X; inversion X.
      1: eapply string_lt_irreflexive; tea.
      eapply Nat.lt_irrefl; tea.
    - intros ? ? ? X Y; invs X; invs Y; constructor.
      1: eapply transitive_string_lt; tea.
      etransitivity; tea.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. move=> ? ? -> ? ? -> //. Qed.

  Definition compare (sf1 sf2 : t) : comparison :=
    match sf1, sf2 with
    | sfType, sfType => Eq
    | sfType, _ => Lt
    | _, sfType => Gt
    | sfProp, sfProp => Eq
    | sfProp, _ => Lt
    | _, sfProp => Gt
    | sfSProp, sfSProp => Eq
    | sfSProp, _ => Lt
    | _, sfSProp => Gt
    | sfGlobal s1, sfGlobal s2 => string_compare s1 s2
    | sfGlobal _, _ => Lt
    | _, sfGlobal _ => Gt
    | sfVar n1, sfVar n2 => Nat.compare n1 n2
    end.


  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    move=> [| | |s|n] [| | |s'|n']; repeat constructor; cbn.
    - eapply CompareSpec_Proper.
      5: eapply CompareSpec_string. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
    - eapply CompareSpec_Proper.
      5: eapply Nat.compare_spec. 4: reflexivity.
      all: split; [now inversion 1|]. now intros ->.
      all: intro; now constructor.
  Qed.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.

  Definition eqb (sf1 sf2 : t) : bool
    := match compare sf1 sf2 with Eq => true | _ => false end.

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

  Definition is_impredicative (sf : t) : bool :=
    match sf with
    | sfProp | sfSProp => true
    | _ => false
    end.

  Definition from_univ u : t :=
    match u with
    | UType => sfType
    | UProp => sfProp
    | USProp => sfSProp
    | UGlobal s => sfGlobal s
    end.

  Definition sort_val v (x : t) : universe_family :=
    match x with
    | sfProp => UProp
    | sfSProp => USProp
    | sfType => UType
    | sfGlobal s => UGlobal s
    | sfVar k => valuation_sort v k
    end.

  Definition is_prop t := if t is sfProp then true else false.
  Definition is_sprop t := if t is sfSProp then true else false.
  Definition is_type t := if t is sfType then true else false.
  Definition is_var t := if t is (sfVar _) then true else false.

  Lemma is_prop_prop : is_prop sfProp.
  Proof. trivial. Qed.

  Lemma is_sprop_sprop : is_sprop sfSProp.
  Proof. trivial. Qed.

  Lemma is_type_type : is_type sfType.
  Proof. trivial. Qed.

  Lemma is_var_var {n} : is_var (sfVar n).
  Proof. trivial. Qed.

  Local Unset Program Cases.
  Program Definition to_univ t : is_var t = false -> universe_family :=
    match t with
    | sfType => fun _ => UType
    | sfProp => fun _ => UProp
    | sfSProp => fun _ => USProp
    | sfGlobal s => fun _ => UGlobal s
    | sfVar n => fun _ => _
    end.

End SortFamily.


(** * Level expressions *)

(** Level expressions are generated by the grammar
    lvl :=  lSet            the lowest universe level
            Level s         global universe levels
            Var n           local universe level variables
            suc lvl         successor of a level
            max lvl1 lvl2   maximum of two levels
  
    subject to the expected equations on max and successors

  Level expressions are represented through canonical forms:
  Level.t       atomic expressions (lSet, Level s, Var n)
  UnivExpr.t    addition of a constant number to an atomic expression
  UnivLevel.t   max of a non-empty set of UnivExpr.t
*)


(** Levels are Set or Level or Var *)
Module Level.
  Inductive t_ : Set :=
  | lSet
  | Level (_ : string)
  | Var (_ : nat) (* these are debruijn indices *).
  Derive NoConfusion EqDec for t_.

  Definition t := t_.

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

Lemma LevelSet_union_empty s : LevelSet.union LevelSet.empty s = s.
Proof.
  apply LevelSet.eq_leibniz.
  change LevelSet.eq with LevelSet.Equal.
  intros x; rewrite LevelSet.union_spec. lsets.
Qed.

(* Badly named : should be LevelExpr *)
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
Instance univexprset_eq_dec : Classes.EqDec UnivExprSet.t.
Proof.
  intros p p'.
  destruct (UnivExprSet.eq_dec p p').
  - now left; eapply UnivExprSet.eq_leibniz in e.
  - right. intros ->. apply n. reflexivity.
Qed.

Module UnivLevel.
  (** A universe level is a list of universe expressions which is:
        - sorted
        - without duplicate
        - non empty *)
  Record t_ := { t_set : UnivExprSet.t ;
                 t_ne  : UnivExprSet.is_empty t_set = false }.

  Derive NoConfusion for t_.
  
  (** This needs a propositional UIP proof to show that [is_empty = false] is a set *)
  Set Equations With UIP.
  Instance t_eqdec : EqDec t_.
  Proof. eqdec_proof. Qed.
  

  Definition t := t_.

  Coercion t_set : t_ >-> UnivExprSet.t.

  Definition eqb (x y : t) := UnivExprSet.equal x.(t_set) y.(t_set).

  Definition make' (e : UnivExpr.t) : t
    := {| t_set := UnivExprSet.singleton e;
          t_ne := eq_refl |}.

  Definition make (l : Level.t) := make' (UnivExpr.make l).

  Definition set := make' UnivExpr.set.

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

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    UnivExprSet.for_all UnivExpr.is_level u.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    (UnivExprSet.cardinal u =? 1)%nat && is_levels u.


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

  Definition super (l : t) : t := map UnivExpr.succ l.

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


  Lemma elements_not_empty (u : t) : UnivExprSet.elements u <> [].
  Proof.
    destruct u as [u1 u2]; cbn; intro e.
    unfold UnivExprSet.is_empty, UnivExprSet.elements,
    UnivExprSet.Raw.elements in *.
    rewrite e in u2; discriminate.
  Qed.

  Global Instance Evaluable' : Evaluable t
    := fun v u => let '(e, u) := exprs u in
               List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  Lemma val_make' v e
    : val v (make' e) = val v e.
  Proof.
    reflexivity.
  Qed.

  Lemma val_make v l
    : val v (make l) = val v l.
  Proof.
    reflexivity.
  Qed.

  Lemma val_set v : val v set = 0.
  Proof. 
    reflexivity. 
  Qed.


  Lemma eq_univ (u v : UnivLevel.t) :
    u = v :> UnivExprSet.t -> u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; cbn. intros X; destruct X.
    now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma eq_univ' (u v : UnivLevel.t) :
    UnivExprSet.Equal u v -> u = v.
  Proof.
    intro H. now apply eq_univ, UnivExprSet.eq_leibniz.
  Qed.

  Lemma eq_univ'' (u v : UnivLevel.t) :
    UnivExprSet.elements u = UnivExprSet.elements v -> u = v.
  Proof.
    intro H. apply eq_univ.
    destruct u as [u1 u2], v as [v1 v2]; cbn in *; clear u2 v2.
    destruct u1 as [u1 u2], v1 as [v1 v2]; cbn in *.
    destruct H. now rewrite (uip_bool _ _ u2 v2).
  Qed.

  Lemma univ_expr_eqb_true_iff (u v : UnivLevel.t) :
    UnivExprSet.equal u v <-> u = v.
  Proof.
    split.
    - intros.
      apply eq_univ'. now apply UnivExprSet.equal_spec.
    - intros ->. now apply UnivExprSet.equal_spec.
  Qed.

  Lemma eqb_spec l l' : reflect (eq l l') (eqb l l').
  Proof.
    apply iff_reflect; symmetry; apply: univ_expr_eqb_true_iff.
  Qed.

End UnivLevel.

(** This coercion allows to see the universes as a [UnivExprSet.t] *)
Coercion UnivLevel.t_set : UnivLevel.t_ >-> UnivExprSet.t.

Declare Scope univ_scope.
Delimit Scope univ_scope with u.

Notation "⟦ l ⟧_ v" := (val v l) (at level 0, format "⟦ l ⟧_ v", v ident) : univ_scope.

Lemma val_fold_right (u : UnivLevel.t) v :
  val v u = fold_right (fun e x => Nat.max (val v e) x) (val v (UnivLevel.exprs u).1)
                       (List.rev (UnivLevel.exprs u).2).
  Proof.
  unfold val at 1, UnivLevel.Evaluable'.
  destruct (UnivLevel.exprs u).
  now rewrite fold_left_rev_right.
  Qed.

Ltac u :=
 change LevelSet.elt with Level.t in *;
 change UnivExprSet.elt with UnivExpr.t in *.
 (* change LevelConstraintSet.elt with UnivConstraint.t in *. *)

Lemma val_In_le (u : UnivLevel.t) v e :
  UnivExprSet.In e u -> val v e <= val v u.
Proof.
  intro H. rewrite val_fold_right.
  apply UnivLevel.In_exprs_rev in H. destruct (UnivLevel.exprs u); cbn in *.
  clear -H. destruct H as [H|H].
  - subst. induction (List.rev l); cbnr; lia.
  - induction (List.rev l); cbn; invs H.
    + u; lia.
    + specialize (IHl0 H0). lia.
Qed.

Lemma val_In_max (u : UnivLevel.t) v :
  exists e, UnivExprSet.In e u /\ val v e = val v u.
Proof.
  eapply iff_ex. {
    intro. eapply and_iff_compat_r. apply UnivLevel.In_exprs_rev. }
  rewrite val_fold_right. destruct (UnivLevel.exprs u) as [e l]; cbn in *.
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

Lemma val_ge_caract (u : UnivLevel.t) v k :
  (forall e, UnivExprSet.In e u -> val v e <= k) <-> val v u <= k.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_forall; intro. eapply imp_iff_compat_r.
      apply UnivLevel.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (UnivLevel.exprs u) as [e l]; cbn; clear.
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

Lemma val_le_caract (u : UnivLevel.t) v k :
  (exists e, UnivExprSet.In e u /\ k <= val v e) <-> k <= val v u.
Proof.
  split.
  - eapply imp_iff_compat_r. {
      eapply iff_ex; intro. eapply and_iff_compat_r. apply UnivLevel.In_exprs_rev. }
    rewrite val_fold_right.
    destruct (UnivLevel.exprs u) as [e l]; cbn; clear.
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



Lemma val_caract (u : UnivLevel.t) v k :
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
  : val v (UnivLevel.add e s) = Nat.max (val v e) (val v s).
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
  val v (UnivLevel.sup s1 s2) = Nat.max (val v s1) (val v s2).
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

Lemma UnivExprSet_For_all_exprs (P : UnivExpr.t -> Prop) (u : UnivLevel.t)
  : UnivExprSet.For_all P u
    <-> P (UnivLevel.exprs u).1 /\ Forall P (UnivLevel.exprs u).2.
Proof.
  etransitivity.
  - eapply iff_forall; intro e. eapply imp_iff_compat_r.
    apply UnivLevel.In_exprs.
  - cbn; split.
    + intro H. split. apply H. now left.
      apply Forall_forall. intros x H0.  apply H; now right.
    + intros [H1 H2] e [He|He]. subst e; tas.
      eapply Forall_forall in H2; tea.
Qed.

Lemma sup_comm x1 x2 :
  UnivLevel.sup x1 x2 = UnivLevel.sup x2 x1.
Proof.
  apply UnivLevel.eq_univ'; simpl. unfold UnivExprSet.Equal.
  intros H. rewrite !UnivExprSet.union_spec. intuition.
Qed.


(** * Constraints on levels *)


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



Module LevelConstraint.
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
End LevelConstraint.

Module LevelConstraintSet := MSetList.MakeWithLeibniz LevelConstraint.
Module LevelConstraintSetFact := WFactsOn LevelConstraint LevelConstraintSet.
Module LevelConstraintSetProp := WPropertiesOn LevelConstraint LevelConstraintSet.
Module CS := LevelConstraintSet.

Lemma CS_union_empty s : LevelConstraintSet.union LevelConstraintSet.empty s = s.
Proof.
  apply LevelConstraintSet.eq_leibniz.
  change LevelConstraintSet.eq with LevelConstraintSet.Equal.
  intros x; rewrite LevelConstraintSet.union_spec. lsets.
Qed.

Lemma CS_For_all_union f cst cst' : LevelConstraintSet.For_all f (LevelConstraintSet.union cst cst') ->
  LevelConstraintSet.For_all f cst.
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
Instance CS_For_all_proper P : Morphisms.Proper (CS.Equal ==> iff)%signature (LevelConstraintSet.For_all P).
Proof.
  intros s s' eqs.
  unfold CS.For_all. split; intros IH x inxs; apply (IH x);
  now apply eqs.
Qed.

(* Being built up from sorted lists without duplicates, constraint sets have 
  decidable equality. This is however not used in the development. *)
Set Equations With UIP.
Remark LevelConstraintSet_EqDec : EqDec LevelConstraintSet.t.
Proof.
  intros p p'.
  destruct (LevelConstraintSet.eq_dec p p').
  - now left; eapply LevelConstraintSet.eq_leibniz in e.
  - right. intros ->. apply n. reflexivity.
Qed.

(* Indexed inequalities between levels *)

Definition lvl_le_n n x y := (Z.of_nat x <= Z.of_nat  y - n)%Z.

Notation "x <ˡ_ n y" := (lvl_le_n n x y) (at level 10, n ident) : univ_scope.
Notation "x <ˡ y" := (lvl_le_n 1 x y) (at level 70) : univ_scope.
Notation "x <=ˡ y" := (lvl_le_n 0 x y) (at level 69) : univ_scope.


Section LevelInequalities.
  Context {cf:checker_flags}.

  Global Instance lle_refl : Reflexive (lvl_le_n 0).
  Proof. unfold lvl_le_n=> x; lia. Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof. split; lia. Qed.


  Global Instance le_n_trans n : Transitive (lvl_le_n (Z.of_nat n)).
  Proof. unfold lvl_le_n=> ???; lia. Qed.

  Global Instance lle_trans : Transitive (lvl_le_n 0).
  Proof. apply (le_n_trans 0). Qed.

  Global Instance llt_trans : Transitive (lvl_le_n 1).
  Proof. apply (le_n_trans 1). Qed.

  Inductive satisfies0 (v : valuation) : LevelConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : LevelConstraintSet.t -> Prop :=
    LevelConstraintSet.For_all (satisfies0 v).

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition eq_level0 (φ : LevelConstraintSet.t) l l' :=
    forall v, satisfies v φ -> (⟦l⟧_v  = ⟦l'⟧_v)%u.

  Definition leq_level_n n (φ : LevelConstraintSet.t) l l' :=
    forall v, satisfies v φ -> ( ⟦l⟧_v <ˡ_n ⟦l'⟧_v)%u.

  Definition leq_level0 (φ : LevelConstraintSet.t) l l' :=
    forall v, satisfies v φ -> (⟦l⟧_v <=ˡ ⟦l'⟧_v)%u.

  Lemma leq_level0_leq_level_n (φ : LevelConstraintSet.t) l l' :
    leq_level0 φ l l' <-> leq_level_n 0 φ l l'.
  Proof. intros. reflexivity. Qed.

  Definition lt_lvl := leq_level_n 1.

  Definition eq_level φ u u'
    := if check_univs then eq_level0 φ u u' else True.

  Definition leq_level φ u u'
    := if check_univs then leq_level0 φ u u' else True.

  (* ctrs are "enforced" by φ *)

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Lemma valid_subset φ φ' ctrs
    : LevelConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof.
    unfold valid_constraints.
    destruct check_univs; [|trivial].
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.


  (** **** Lemmas about eq and leq **** *)

  Global Instance eq_level0_refl φ : Reflexive (eq_level0 φ).
  Proof.
    intros vH s; reflexivity.
  Qed.

  Global Instance eq_level_refl φ : Reflexive (eq_level φ).
  Proof.
    intro s.
    unfold eq_level; destruct check_univs;
      [apply eq_level0_refl|constructor].
  Qed.

  Global Instance leq_level0_refl φ : Reflexive (leq_level0 φ).
  Proof.
    intros s vH;cbn;reflexivity.
  Qed.

  Global Instance leq_level_refl φ : Reflexive (leq_level φ).
  Proof.
    intro s.
    unfold leq_level; destruct check_univs;
      [apply leq_level0_refl|constructor].
  Qed.

  Global Instance eq_level0_sym φ : Symmetric (eq_level0 φ).
  Proof.
    intros s s' e vH. symmetry ; eauto.
  Qed.

  Global Instance eq_level_sym φ : Symmetric (eq_level φ).
  Proof.
    unfold eq_level. destruct check_univs ; eauto.
    eapply eq_level0_sym.
  Qed.

  Global Instance eq_level0_trans φ : Transitive (eq_level0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h.
    etransitivity ; try eapply h1 ; eauto.
  Qed.

  Global Instance eq_level_trans φ : Transitive (eq_level φ).
  Proof.
    intros s1 s2 s3.
    unfold eq_level. destruct check_univs ; auto.
    intros h1 h2.
    eapply eq_level0_trans ; eauto.
  Qed.

  Global Instance leq_level0_trans φ : Transitive (leq_level0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h. etransitivity.
    - eapply h1. assumption.
    - eapply h2. assumption.
  Qed.

  Global Instance leq_level_trans φ : Transitive (leq_level φ).
  Proof.
    intros s1 s2 s3.
    unfold leq_level. destruct check_univs ; auto.
    intros h1 h2.
    eapply leq_level0_trans ; eauto.
  Qed.


  Lemma eq_leq_level φ u u' :
    eq_level0 φ u u' <-> leq_level0 φ u u' /\ leq_level0 φ u' u.
  Proof.
    split.
    intro H; split; intros v Hv; specialize (H v Hv); now rewrite H.
    intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
    unfold lvl_le_n in H1, H2; lia.
  Qed.

  Lemma leq_level0_sup_l φ s1 s2 :
    leq_level0 φ s1 (UnivLevel.sup s1 s2).
  Proof.
    move=> ??; rewrite val_sup /lvl_le_n; lia.
  Qed.

  Lemma leq_level0_sup_r φ s1 s2 :
    leq_level0 φ s2 (UnivLevel.sup s1 s2).
  Proof.
    move=> ??; rewrite val_sup /lvl_le_n; lia.
  Qed.

  Lemma leq_level_product_l φ (s1 s2 : UnivLevel.t)
    : leq_level φ s1 (UnivLevel.sup s1 s2).
  Proof.
    unfold leq_level; destruct check_univs; [cbn|constructor].
    apply leq_level0_sup_l.
  Qed.

  Lemma leq_level_product_r φ (s1 s2 : UnivLevel.t)
    : leq_level φ s2 (UnivLevel.sup s1 s2).
  Proof.
    unfold leq_level; destruct check_univs; [cbn|constructor].
    apply leq_level0_sup_r.
  Qed.

  Global Instance eq_level_leq_level φ : subrelation (eq_level φ) (leq_level φ).
  Proof.
    unfold eq_level, leq_level; destruct check_univs; [|intuition].
    intros u u' HH v Hv. rewrite (HH v Hv). reflexivity.
  Qed.

  Global Instance eq_level0_equivalence φ : Equivalence (eq_level0 φ) :=
     {| Equivalence_Reflexive := _ ;
        Equivalence_Symmetric := _;
        Equivalence_Transitive := _ |}.

  Global Instance eq_level_equivalence φ : Equivalence (eq_level φ) :=
     {| Equivalence_Reflexive := eq_level_refl _ ;
        Equivalence_Symmetric := eq_level_sym _;
        Equivalence_Transitive := eq_level_trans _ |}.

  Global Instance leq_level_preorder φ : PreOrder (leq_level φ) :=
     {| PreOrder_Reflexive := leq_level_refl _ ;
        PreOrder_Transitive := leq_level_trans _ |}.

  Global Instance llt_str_order : StrictOrder (lvl_le_n 1).
  Proof.
    split.
    - intros x ; unfold lvl_le_n; red; lia.
    - exact _.
  Qed.

  
  Global Instance lle_antisym : Antisymmetric _ eq (lvl_le_n 0).
  Proof.
    intros ??; cbn; try reflexivity; auto.
    unfold lvl_le_n; lia.
  Qed.
 

  Global Instance leq_level0_antisym φ
    : Antisymmetric _ (eq_level0 φ) (leq_level0 φ).
  Proof.
    intros t u tu ut. unfold leq_level0, eq_level0 in *.
    red in tu, ut.
    intros v sat.
    specialize (tu _ sat).
    specialize (ut _ sat).
    simpl in tu, ut.
    apply lle_antisym; tea.
  Qed.
  
  Global Instance leq_level_antisym φ
    : Antisymmetric _ (eq_level φ) (leq_level φ).
  Proof.
    intros t u tu ut. unfold leq_level, eq_level in *.
    destruct check_univs; [|trivial]. eapply leq_level0_antisym; auto.
  Qed.

  Global Instance leq_level_partial_order φ
    : PartialOrder (eq_level φ) (leq_level φ).
  Proof.
    intros x y; split. intros eqxy; split. now eapply eq_level_leq_level. red.
    now eapply eq_level_leq_level, symmetry.
    intros [l r]. now eapply leq_level_antisym.
  Defined.


  Definition eq_level_leq_level' {cf} φ u u'
    := @eq_level_leq_level cf φ u u'.
  Definition leq_level_refl' φ u
    := @leq_level_refl φ u.

  Hint Resolve eq_level_leq_level' leq_level_refl' : core.

End LevelInequalities.


(** * Universes *)

Module Universe.

  (* Putting the invariant in bool for decidability of equality *)
  Notation impredicative_inv s l :=
    (SortFamily.is_prop s || SortFamily.is_sprop s ==> UnivLevel.eqb l UnivLevel.set).

  (** A universe combines a sort family with a universe level *)
  Record t_ := {
    t_sort : SortFamily.t ;
    t_level : UnivLevel.t ;
    t_impredicative_inv : impredicative_inv t_sort t_level }.
  Derive NoConfusion for t_.


  Instance t_eqdec : EqDec t_.
  Proof. eqdec_proof. Qed.

  Definition t := t_.

  (* Project and build universes *)
  Notation sort := t_sort.
  Notation lvl := t_level.

  Definition normalize_lvl sf l :=
   if sf is (SortFamily.sfProp | SortFamily.sfSProp) then UnivLevel.set else l.

  Lemma impredicative_inv_normalize sf l : impredicative_inv sf (normalize_lvl sf l).
  Proof. case: sf=> //=. Qed.

  Lemma normalize_impredicative_inv sf l :
    impredicative_inv sf l -> normalize_lvl sf l = l.
  Proof. case: sf=> //= /UnivLevel.eqb_spec //. Qed.

  Lemma normalize_leq sf l v : (⟦normalize_lvl sf l⟧_v <=ˡ ⟦l⟧_v)%u.
  Proof. case: sf=> *; cbn; unfold lvl_le_n; lia. Qed.

  Definition pair sf l :=
    Build_t_ sf (normalize_lvl sf l) (impredicative_inv_normalize sf l).

  (* comparing universe levels even if the sorts might be impredicative
     otherwise [eqb_true_iff] won't hold *)
  Definition eqb (u1 u2 : t) : bool :=
    SortFamily.eqb (sort u1) (sort u2)
    && UnivLevel.eqb (lvl u1) (lvl u2).

  Definition set0 := UnivLevel.make' (UnivExpr.make Level.lSet).

  Definition lType := pair SortFamily.sfType.
  Definition lProp := Build_t_ SortFamily.sfProp UnivLevel.set eq_refl.
  Definition lSProp := Build_t_ SortFamily.sfSProp UnivLevel.set eq_refl.


  (** Create a universe representing Type at the given level. *)
  Definition make (l : Level.t) : t :=
     lType (UnivLevel.make' (UnivExpr.make l)).

  Definition of_expr e :=
    (lType (UnivLevel.make' e)).

  Definition add_to_exprs (e : UnivExpr.t) (u : t) : t :=
    pair (sort u) (UnivLevel.add e (lvl u)).

  Definition add_list_to_exprs (es : list UnivExpr.t) (u : t) : t :=
    pair (sort u) (UnivLevel.add_list es (lvl u)).

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    UnivLevel.is_levels (lvl u).

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    UnivLevel.is_level (lvl u).

  (* Beware that a sort variable can be instanciated afterwards...*)
  Definition is_sprop (u : t) : bool := SortFamily.is_sprop (sort u).

  Definition is_prop (u : t) : bool := SortFamily.is_prop (sort u).

  Definition is_sort_var (u : t) : bool :=
    if sort u is SortFamily.sfVar _ then true else false.

  Definition is_type (u : t) : bool := SortFamily.is_type (sort u).

  Definition type0 : t := make Level.lSet.
  Definition type1 : t := lType (UnivLevel.make' UnivExpr.type1).


  (* Used for quoting. *)
  Definition from_kernel_repr (e : Level.t * bool) (es : list (Level.t * bool)) : t
    := lType (UnivLevel.add_list (map UnivExpr.from_kernel_repr es)
                (UnivLevel.make' (UnivExpr.from_kernel_repr e))).

  (** The universe strictly above FOR TYPING (not cumulativity) *)

  (* TODO: is that supposed to be universe in which the sort is living ? *)
  Definition super (l : t) : t :=
    lType (UnivLevel.map UnivExpr.succ (lvl l)).


  Definition get_univ_exprs (u : t) : UnivLevel.t := lvl u.

  (** Type of a product *)
  Definition sort_of_product (domsort rangsort : t) :=
    pair (sort rangsort) (UnivLevel.sup (lvl domsort) (lvl rangsort)).

  Lemma eqb_refl u : eqb u u.
  Proof.
    apply/andP;split; first apply SortFamily.eqb_refl.
    now apply UnivExprSet.equal_spec.
  Qed.

  Definition univ_val : valuation -> t -> universes :=
    fun v u => (SortFamily.sort_val v (sort u), val v (lvl u)).

  Definition uType n : universes := (UType, n).

  Definition uProp : universes := (UProp, 0).
  Definition uSProp : universes := (USProp, 0).

  Lemma val_make v l
    : univ_val v (make l) = uType (val v l).
  Proof.
    destruct l; cbnr.
  Qed.

  Lemma make_inj x y :
    make x = make y -> x = y.
  Proof. move=> [=] //. Qed.

  Lemma eqb_true_iff u v :
    eqb u v <-> u = v.
  Proof.
    split. 2: intros ->; apply Universe.eqb_refl.
    destruct u,v=> /=. move=>/andP/=[/SortFamily.eqb_spec Hs /UnivLevel.eqb_spec Hl].
    depelim Hs. depelim Hl. f_equal. apply: uip_bool.
  Qed.

  Lemma eqb_spec u v : reflect (u = v) (eqb u v).
  Proof. apply: iff_reflect; symmetry; apply: eqb_true_iff. Qed.

  Lemma universe_eq u v : 
    Universe.sort u = Universe.sort v ->
    Universe.lvl u = Universe.lvl v ->
    u = v.
  Proof.
    move=> /SortFamily.eqb_spec hs /UnivLevel.eqb_spec hl.
    by apply/eqb_spec; rewrite /Universe.eqb hs hl.
  Qed.  

End Universe.

(* To revisit once we add local sorts (will need to infer if a sort variable is propositional from the constraints) *)
Definition is_propositional u :=
  (* is_eliminable ϕ SortFamily.sfProp (Universe.sort u). *)
  Universe.is_prop u || Universe.is_sprop u.


Notation "⟨ u ⟩_ v" := (Universe.univ_val v u) (at level 0, format "⟨ u ⟩_ v", v ident) : univ_scope.


(* Not sure whether the following lemmas are still useful *)

Lemma is_prop_val u :
  Universe.is_prop u -> forall v, (Universe.univ_val v u).1 = UProp.
Proof.
  move: u => [[]] //=.
Qed.

Lemma is_sprop_val u :
  Universe.is_sprop u -> forall v, (Universe.univ_val v u).1 = USProp.
Proof.
  move: u=> [[]] //.
Qed.


Lemma val_is_prop u v :
  (Universe.univ_val v u).1 = UProp -> Universe.is_prop u \/ Universe.is_sort_var u.
Proof.
  move: u=> [[]] //=; dintuition.
Qed.

Lemma val_is_sprop u v :
  (Universe.univ_val v u).1 = USProp -> Universe.is_sprop u \/ Universe.is_sort_var u.
Proof.
  move: u=> [[]] //=; dintuition.
Qed.

(* Lemma is_prop_and_is_sprop_val_false u : *)
(*   Universe.is_prop u = false -> Universe.is_sprop u = false -> *)
(*   forall v, ∑ n, Universe.univ_val v u = UType n. *)
(* Proof. *)
(*   intros Hp Hsp v. *)
(*   destruct u; try discriminate. simpl. eexists; eauto. *)
(* Qed. *)

Lemma val_is_prop_false u v n :
  Universe.univ_val v u = Universe.uType n -> Universe.is_prop u = false.
Proof.
  pose proof (is_prop_val u) as H. destruct (Universe.is_prop u); cbnr.
  move=>[=]+_;move: (H eq_refl v)=> /= -> //.
Qed.


Lemma is_prop_sort_prod x2 x3 :
  Universe.is_prop (Universe.sort_of_product x2 x3)
  -> Universe.is_prop x3.
Proof.
  unfold Universe.sort_of_product.
  destruct x3;cbn;auto.
Qed.

Lemma is_sprop_sort_prod x2 x3 :
  Universe.is_sprop (Universe.sort_of_product x2 x3)
  -> Universe.is_sprop x3.
Proof.
  unfold Universe.sort_of_product.
  destruct x3;cbn;auto.
Qed.


(** * Constraints on sort families *)



Module SortConstraint.
  Include PairOrderedType SortFamily SortFamily.
  Definition eq_leibniz x y : eq x y -> x = y.
    destruct x, y. cbn. intros [[=->][=->]]. reflexivity.
  Qed.
End SortConstraint.
Module SortConstraintSet := MSetList.MakeWithLeibniz SortConstraint.
Module SortConstraintSetFact := WFactsOn SortConstraint SortConstraintSet.
Module SortConstraintSetProp := WPropertiesOn SortConstraint SortConstraintSet.


(** {6 Universe instances} *)

Module LevelInstance.

  (** A universe level instance represents a vector of argument universe levels
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
End LevelInstance.

Module SortInstance.
  Definition t : Set := list SortFamily.t.

  Definition empty : t := [].
  Definition is_empty (i : t) : bool :=
    match i with
    | [] => true
    | _ => false
    end.

  Definition eqb (i j : t) :=
    forallb2 SortFamily.eqb i j.

  Definition equal_upto (f : SortFamily.t -> SortFamily.t -> bool) (i j : t) :=
    forallb2 f i j.

End SortInstance.

Module UContext.
  Record t := make {
    sort_instance : SortInstance.t ;
    sort_constraints : SortConstraintSet.t ;
    level_instance : LevelInstance.t ;
    level_constraints : LevelConstraintSet.t 
  }.

  Definition empty : t := make SortInstance.empty SortConstraintSet.empty LevelInstance.empty LevelConstraintSet.empty.

  Definition dest : t -> LevelInstance.t * LevelConstraintSet.t := 
    fun x => (level_instance x, level_constraints x).
End UContext.

Module AUContext.
  Record t := make { 
    sort_context : list name ; 
    sort_constraints : SortConstraintSet.t ;
    level_context : list name ;
    level_constraints : LevelConstraintSet.t
  }.

  Definition repr (x : t) : UContext.t :=
    let sinst := mapi (fun i _ => SortFamily.sfVar i) x.(sort_context) in
    let linst := mapi (fun i _ => Level.Var i) x.(level_context) in
    UContext.make sinst x.(sort_constraints) linst x.(level_constraints).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (UContext.level_instance (repr uctx)).
End AUContext.

Module ContextSet.
  (* For monomorphic definitions => no sort polymorphism *)
  Definition t := LevelSet.t × LevelConstraintSet.t.

  Definition empty : t := (LevelSet.empty, LevelConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && LevelConstraintSet.is_empty (snd uctx).
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
  | Polymorphic_ctx ctx => AUContext.level_constraints ctx
  end.

  
(* Preorder on universes *)

Definition level_le_n s n u u' :=
  if is_impredicative s 
  then (n = 0)%Z
  else (u <ˡ_n u')%u.

Definition univ_le_n {cf:checker_flags} n u u' :=
  match u.1 , u'.1 with
  | UProp, UType => prop_sub_type : Prop
  | s, s' => s = s' /\ level_le_n s n u.2 u'.2
  end.


Notation "x <_ n y" := (univ_le_n n x y) (at level 10, n ident) : univ_scope.
Notation "x < y" := (univ_le_n 1 x y) : univ_scope.
Notation "x <= y" := (univ_le_n 0 x y) : univ_scope.

Inductive univ_le_n_view {cf:checker_flags} (n : Z) : 
  universe_family -> nat -> universe_family -> nat -> Prop :=
  | UleVPropType m p : prop_sub_type -> univ_le_n_view n UProp m UType p
  | UleVEq s m p : level_le_n s n m p -> univ_le_n_view n s m s p.

Derive Signature for univ_le_n_view.
(* Doesn't work... *)
(* Derive NoConfusion for univ_le_n_view. *)

Lemma univ_le_n_equiv {cf:checker_flags} n u u' :
  (u <_n u')%u <-> univ_le_n_view n u.1 u.2 u'.1 u'.2.
Proof.
  split; last move: u u'=> [??] [??] /= [|] [] * //.
  move: u u'=> [[|||?]?][[|||?]?] ; unfold univ_le_n=> //=.
  3: move=> h; by constructor.
  all:move=> [h ?]; rewrite ?h ; constructor=> //.
Qed.
  
Ltac lle := unfold univ_le_n, lvl_le_n in *.
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

(* TODO : Revisit once uGraph is updated for levels and we need to tod the same for sorts *)
Section Univ.
  Context {cf:checker_flags}.

  Global Instance ule_refl : Reflexive (univ_le_n 0).
  Proof.
    move=> [[|||?]??]; cbn; last (split=> //); try split=>//;
    unfold lvl_le_n ; lia.
  Qed.

  Global Instance ule_n_trans n : Transitive (univ_le_n (Z.of_nat n)).
  Proof.
    move=> [??][??][??] /univ_le_n_equiv/= [???|????] /univ_le_n_equiv/=.
    all: move=> h; depelim h=> //.
    apply univ_le_n_equiv; constructor=> /=.
    unfold level_le_n in *; destruct (is_impredicative s)=> //.
    etransitivity; eassumption.
  Qed.

  Global Instance ule_trans : Transitive (univ_le_n 0).
  Proof. apply (ule_n_trans 0). Qed.

  Global Instance ult_trans : Transitive (univ_le_n 1).
  Proof. apply (ule_n_trans 1). Qed.

  Definition sort_satisfies0 (v : valuation) (sc : SortConstraint.t) : bool :=
    globally_eliminable (SortFamily.sort_val v sc.1) (SortFamily.sort_val v sc.2).

  Definition sort_satisfies v : SortConstraintSet.t -> Prop :=
    SortConstraintSet.For_all (sort_satisfies0 v).

  Definition sort_consistent ctrs := exists v, sort_satisfies v ctrs.

  Definition eq_sort0 (φ : SortConstraintSet.t) s s' :=
    forall v, sort_satisfies v φ -> SortFamily.sort_val v s = SortFamily.sort_val v s'.

  Definition leq_sort0 (φ : SortConstraintSet.t) s s' :=
    forall v, sort_satisfies v φ -> global_sort_elimination (SortFamily.sort_val v s) (SortFamily.sort_val v s').
  
  Definition eq_universe0 φ u u' :=
    eq_sort0 φ.1 (Universe.sort u) (Universe.sort u')
    /\ (leq_sort0 φ.1 SortFamily.sfProp (Universe.sort u)
     \/ eq_level0 φ.2 (Universe.lvl u) (Universe.lvl u')).

  Definition leq_universe_n n (φ : LevelConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (univ_le_n n (Universe.univ_val v u) (Universe.univ_val v u'))%u.

  Definition leq_universe0 (φ : LevelConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Universe.univ_val v u <= Universe.univ_val v u')%u.

  Lemma leq_universe0_leq_universe_n (φ : LevelConstraintSet.t) u u' :
    leq_universe0 φ u u' <-> leq_universe_n 0 φ u u'.
  Proof. intros. reflexivity. Qed.

  Definition lt_universe := leq_universe_n 1.

  Definition eq_universe φ u u'
    := if check_univs then eq_universe0 φ u u' else True.

  Definition leq_universe φ u u'
    := if check_univs then leq_universe0 φ u u' else True.

  (* ctrs are "enforced" by φ *)

  (* Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Lemma valid_subset φ φ' ctrs
    : LevelConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof.
    unfold valid_constraints.
    destruct check_univs; [|trivial].
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.


  (** **** Lemmas about eq and leq **** *)

  Global LevelInstance eq_universe0_refl φ : Reflexive (eq_universe0 φ).
  Proof.
    intros vH s; reflexivity.
  Qed.

  Global LevelInstance eq_universe_refl φ : Reflexive (eq_universe φ).
  Proof.
    intro s.
    unfold eq_universe; destruct check_univs;
      [apply eq_universe0_refl|constructor].
  Qed.

  Global LevelInstance leq_universe0_refl φ : Reflexive (leq_universe0 φ).
  Proof.
    intros s vH;cbn;reflexivity.
  Qed.

  Global LevelInstance leq_universe_refl φ : Reflexive (leq_universe φ).
  Proof.
    intro s.
    unfold leq_universe; destruct check_univs;
      [apply leq_universe0_refl|constructor].
  Qed.

  Global LevelInstance eq_universe0_sym φ : Symmetric (eq_universe0 φ).
  Proof.
    intros s s' e vH. symmetry ; eauto.
  Qed.

  Global LevelInstance eq_universe_sym φ : Symmetric (eq_universe φ).
  Proof.
    unfold eq_universe. destruct check_univs ; eauto.
    eapply eq_universe0_sym.
  Qed.

  Global LevelInstance eq_universe0_trans φ : Transitive (eq_universe0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h.
    etransitivity ; try eapply h1 ; eauto.
  Qed.

  Global LevelInstance eq_universe_trans φ : Transitive (eq_universe φ).
  Proof.
    intros s1 s2 s3.
    unfold eq_universe. destruct check_univs ; auto.
    intros h1 h2.
    eapply eq_universe0_trans ; eauto.
  Qed.

  Global LevelInstance leq_universe0_trans φ : Transitive (leq_universe0 φ).
  Proof.
    intros s1 s2 s3 h1 h2 v h. etransitivity.
    - eapply h1. assumption.
    - eapply h2. assumption.
  Qed.

  Global LevelInstance leq_universe_trans φ : Transitive (leq_universe φ).
  Proof.
    intros s1 s2 s3.
    unfold leq_universe. destruct check_univs ; auto.
    intros h1 h2.
    eapply leq_universe0_trans ; eauto.
  Qed.


  (* Lemma eq_leq_universe φ u u' :
    eq_universe0 φ u u' <-> leq_universe0 φ u u' /\ leq_universe0 φ u' u.
  Proof.
    split.
    intro H; split; intros v Hv; specialize (H v Hv); now rewrite H.
    intros [H1 H2] v Hv; specialize (H1 v Hv); specialize (H2 v Hv).
    unfold univ_le_n in *.
    move: (Universe.univ_val v u) (Universe.univ_val v u') H1 H2=> [[| | |?]?] [[| | |?]?]; cbn; try now auto.  
    
    1,2: todo "Fix equality between levels of impredicative sorts".
    move=> [??] [??]; f_equal; first f_equal=>//; lia.
  Qed. *)

  (* Lemma leq_universe0_sup_l φ s1 s2 : *)
  (*   Universe.is_prop s1 = false -> Universe.is_sprop s1 = false ->  *)
  (*   leq_universe0 φ s1 (Universe.sup s1 s2). *)
  (* Proof. *)
  (*   intros H1 H2 v Hv. *)
  (*   specialize (is_prop_and_is_sprop_val_false _ H1 H2 v) as [n Hzero]. *)
  (*   rewrite val_universe_sup Hzero. destruct (Universe.univ_val v s2); simpl; lia. *)
  (* Qed. *)

  (* Lemma leq_universe0_sup_r φ s1 s2 : *)
  (*   Universe.is_prop s2 = false -> Universe.is_sprop s2 = false ->  *)
  (*   leq_universe0 φ s2 (Universe.sup s1 s2). *)
  (* Proof. *)
  (*   intros H1 H2 v Hv. *)
  (*   specialize (is_prop_and_is_sprop_val_false _ H1 H2 v) as [n Hzero]. *)
  (*   rewrite val_universe_sup Hzero. *)
  (*   destruct (Universe.univ_val v s1); simpl; lia. *)
  (* Qed. *)

  (* FixMe: do the same as the proof below *)
  Lemma leq_universe0_sup_l' φ (s1 s2 : UnivLevel.t) :
    leq_universe0 φ (Universe.lType s1) (Universe.lType (UnivLevel.sup s1 s2)).
  Proof.
    intros v Hv. cbn. rewrite val_sup;split=> //; lia.
  Qed.

  Lemma leq_universe0_sup_r' φ sf (s1 s2 : UnivLevel.t) :
    leq_universe0 φ (Universe.pair sf s2) (Universe.pair sf (UnivLevel.sup s1 s2)).
  Proof.
    intros v Hv. move: sf=> [|||?|?]; cbn;
    last (unfold univ_le_n; cbn; set z := valuation_sort _ _; case: z).
    all: split=> //; rewrite val_sup; lia.
  Qed.

  Lemma leq_universe_product φ (s1 s2 : Universe.t)
    : leq_universe φ s2 (Universe.sort_of_product s1 s2).
  Proof.
    unfold leq_universe; destruct check_univs; [cbn|constructor].
    apply leq_universe0_sup_r'.
  Qed.
  (* Rk: [leq_universe φ s1 (sort_of_product s1 s2)] does not hold due to
     impredicativity. *)

  Global LevelInstance eq_universe_leq_universe φ : subrelation (eq_universe φ) (leq_universe φ).
  Proof.
    unfold eq_universe, leq_universe; destruct check_univs; [|intuition].
    intros u u' HH v Hv. rewrite (HH v Hv). reflexivity.
  Qed.

  Global LevelInstance eq_universe0_equivalence φ : Equivalence (eq_universe0 φ) :=
     {| Equivalence_Reflexive := _ ;
        Equivalence_Symmetric := _;
        Equivalence_Transitive := _ |}.

  Global LevelInstance eq_universe_equivalence φ : Equivalence (eq_universe φ) :=
     {| Equivalence_Reflexive := eq_universe_refl _ ;
        Equivalence_Symmetric := eq_universe_sym _;
        Equivalence_Transitive := eq_universe_trans _ |}.

  Global LevelInstance leq_universe_preorder φ : PreOrder (leq_universe φ) :=
     {| PreOrder_Reflexive := leq_universe_refl _ ;
        PreOrder_Transitive := leq_universe_trans _ |}.

  Global LevelInstance llt_str_order : StrictOrder (univ_le_n 1).
  Proof.
    split.
    - intros x H. destruct x as [[] n]; cbn in *; lia.
    - exact _.
  Qed.

  (*
  Global LevelInstance lle_antisym : Antisymmetric _ eq (univ_le_n 0).
  Proof.
    intros [[] ?] [[] ?]; cbn; try reflexivity; auto.
    intros. f_equal; lia.
  Qed.
  *)

  (*
  Global LevelInstance leq_universe0_antisym φ
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
  *)  
  
  (* Global LevelInstance leq_universe_antisym φ
    : Antisymmetric _ (eq_universe φ) (leq_universe φ).
  Proof.
    intros t u tu ut. unfold leq_universe, eq_universe in *.
    destruct check_univs; [|trivial]. eapply leq_universe0_antisym; auto.
  Qed. *)
(* 
  Global LevelInstance leq_universe_partial_order φ
    : PartialOrder (eq_universe φ) (leq_universe φ).
  Proof.
    intros x y; split. intros eqxy; split. now eapply eq_universe_leq_universe. red.
    now eapply eq_universe_leq_universe, symmetry.
    intros [l r]. now eapply leq_universe_antisym.
  Defined. *)


  Definition eq_universe_leq_universe' {cf} φ u u'
    := @eq_universe_leq_universe cf φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_universe_leq_universe' leq_universe_refl' : core.

  (** Elimination restriction *)

  (* Revisit *)
  Definition is_allowed_elimination0
             φ (into : Universe.t) (allowed : allowed_eliminations) : Prop :=
    forall v,
      satisfies v φ ->
      match allowed, ⟨into⟩_v%u.1 with
      | IntoSProp, USProp
      | IntoPropSProp, (UProp | USProp)
      | IntoSetPropSProp, (UProp | USProp | UType)
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
*)
End Univ.

(* This universe is a hack used in plugings to generate fresh universes *)
Definition fresh_universe : Universe.t. exact Universe.type0. Qed.
(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t. exact Level.lSet. Qed.


(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : LevelInstance.t -> A -> A.


Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
            Level.lSet | Level.Level _ => l
          | Level.Var n => List.nth n u Level.lSet
          end.

Instance subst_instance_cstr : UnivSubst LevelConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

Instance subst_instance_cstrs : UnivSubst LevelConstraintSet.t :=
  fun u ctrs => LevelConstraintSet.fold (fun c => LevelConstraintSet.add (subst_instance_cstr u c))
                                ctrs LevelConstraintSet.empty.

Instance subst_instance_level_expr : UnivSubst UnivExpr.t :=
  fun u e => match e with
          | (Level.lSet, _)
          | (Level.Level _, _) => e
          | (Level.Var n, b) =>
            match nth_error u n with
            | Some l => (l,b)
            | None => (Level.lSet, b)
            end
          end.

Instance subst_instance_univ_level : UnivSubst UnivLevel.t :=
  fun u => UnivLevel.map (subst_instance_level_expr u).

Instance subst_instance_univ : UnivSubst Universe.t :=
  fun u e => Universe.pair (Universe.sort e) (subst_instance u (Universe.t_level e)).

Instance subst_instance_instance : UnivSubst LevelInstance.t :=
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

  Definition closedu_universe_levels (u : UnivLevel.t) :=
    UnivExprSet.for_all closedu_level_expr u.

  Definition closedu_universe (u : Universe.t) :=
    closedu_universe_levels (Universe.lvl u).

  Definition closedu_instance (u : LevelInstance.t) :=
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


  Lemma closedu_subst_instance_univ_level u l
    : closedu_universe_levels 0 l -> subst_instance_univ_level u l = l.
  Proof.
    intro H. unfold subst_instance_univ_level.
    apply UnivLevel.eq_univ'.
    destruct l as [ts H1].
    unfold closedu_universe_levels in *;cbn in *.
    intro e; split; intro He.
    - apply UnivLevel.map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      apply UnivExprSet.for_all_spec in H; proper.
      exact (H _ He').
      now subst. 
    - apply UnivLevel.map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply UnivExprSet.for_all_spec in H; proper. now apply H.
  Qed.

  Lemma closedu_subst_instance_univ u s
    : closedu_universe 0 s -> subst_instance_univ u s = s.
  Proof.
    destruct s. unfold closedu_universe, subst_instance_univ.
    cbn=> /closedu_subst_instance_univ_level H.
    apply:Universe.universe_eq=> //=.
    rewrite /subst_instance (H u) Universe.normalize_impredicative_inv //.
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

Hint Resolve closedu_subst_instance_level closedu_subst_instance_level_expr
     closedu_subst_instance_univ closedu_subst_instance : substu.

(** Substitution of a universe-closed instance of the right size
    produces a universe-closed term. *)
Section SubstLevelInstanceClosed.
  Context (u : LevelInstance.t) (Hcl : closedu_instance 0 u).

  Lemma subst_instance_level_closedu l
    : closedu_level #|u| l -> closedu_level 0 (subst_instance_level u l).
  Proof.
    destruct l; cbnr.
    unfold closedu_instance in Hcl.
    destruct (nth_in_or_default n u Level.lSet).
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

  Lemma subst_instance_univ_level_closedu l
    : closedu_universe_levels #|u| l -> closedu_universe_levels 0 (subst_instance_univ_level u l).
  Proof.
    intro H.
    destruct l as [t ?];cbnr.
    destruct t as [l Hl].
    apply UnivExprSet.for_all_spec; proper.
    intros e He. eapply UnivLevel.map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply UnivExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.
  
  Lemma subst_instance_impredicative_inv s l :
    Universe.impredicative_inv s l -> Universe.impredicative_inv s (subst_instance u l).
  Proof.
    move=> /implyP h; apply/implyP=>/h/UnivLevel.eqb_spec -> //.
  Qed.

  Lemma subst_instance_univ_closedu s
    : closedu_universe #|u| s -> closedu_universe 0 (subst_instance_univ u s).
  Proof.
    unfold subst_instance_univ, closedu_universe.
    destruct s as [s l inv]; cbn.
    rewrite Universe.normalize_impredicative_inv; last apply: subst_instance_univ_level_closedu.
    by apply: subst_instance_impredicative_inv.
  Qed.

  Lemma subst_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance u t).
  Proof.
    intro H. etransitivity. eapply forallb_map.
    eapply forallb_impl; tea.
    intros l Hl; cbn. apply subst_instance_level_closedu.
  Qed.
End SubstLevelInstanceClosed.

Hint Resolve subst_instance_level_closedu subst_instance_level_expr_closedu
     subst_instance_univ_closedu subst_instance_closedu : substu.


Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ^ string_of_nat n
  end.

Definition string_of_level_expr (e : UnivExpr.t) : string :=
  let '(l, n) := e in string_of_level l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition string_of_univ_level (l : UnivLevel.t) :=
  string_of_list string_of_level_expr (UnivExprSet.elements l).

Definition string_of_sort (u : Universe.t) :=
  match Universe.sort u with
  | SortFamily.sfSProp => "SProp"
  | SortFamily.sfProp => "Prop"
  | SortFamily.sfType => "Type(" ^ string_of_univ_level (Universe.lvl u) ^ ")"
  | SortFamily.sfGlobal s => s ^ "(" ^ string_of_univ_level (Universe.lvl u) ^ ")" 
  | SortFamily.sfVar n => "SRel<" ^ string_of_nat n ^ ">(" ^ string_of_univ_level (Universe.lvl u) ^ ")"
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (sort_names : list name) (level_names : list name) (ctx : UContext.t).
Derive NoConfusion for universes_entry.

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry (AUContext.sort_context ctx)  (AUContext.level_context ctx) (Universes.AUContext.repr ctx)
  | Monomorphic_ctx ctx => Monomorphic_entry ctx
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx c => LevelInstance.empty
  | Polymorphic_ctx c => UContext.level_instance (AUContext.repr c)
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
             " /\ " (LevelConstraintSet.elements t).


Ltac cong := intuition congruence.


(* Revisit once uGraph is updated for levels and we do the same for sorts *)
(*

(* Useful ? *)
(* Lemma val_universe_sup_not_prop vv v u :
  Universe.is_prop v = false -> Universe.is_sprop v = false ->
  ∑ n, Universe.univ_val vv (UnivLevel.sup u v) = UType n.
Proof.
  intros Hp Hsp.
  destruct u,v;cbn;try discriminate;try lia; try apply val_zero_exprs;
  eexists; eauto.
Qed. *)


(* Does not hold *)
(* Lemma univ_le_prop_inv {cf:checker_flags} u : (u <= UProp)%u -> u = UProp.
Proof. destruct u; simpl; try congruence; auto. Qed. *)

(* Lemma univ_le_sprop_inv {cf:checker_flags} u : (u <= USProp)%u -> u = USProp.
Proof. destruct u; simpl; try congruence; auto. Qed. *)

Lemma univ_prop_le_inv {cf:checker_flags} u : (Universe.uProp <= u)%u -> 
  (u.1 = UProp \/ (prop_sub_type /\ exists n, u = Universe.uType n)).
Proof.
  move: u => [??] /univ_le_n_equiv /= h; depelim h; last by left.
  right; split=> //; eexists; reflexivity.
Qed.



(* Lemma univ_val_max_mon {cf:checker_flags} u u' v v' : (u <= u')%u -> (UType v <= UType v')%u -> 
  (univ_val_max u (UType v) <= univ_val_max u' (UType v'))%u.
Proof.
  intros.
  destruct u, u'; simpl in *; auto. lia. lia.
Qed. *)


Definition normalize (u : Universe.t) :=
  let l := 
    match Universe.sort u with
    | SortFamily.sfSProp | SortFamily.sfProp => UnivLevel.set
    | SortFamily.sfVar _ => UnivLevel.set
      (* Universe.lvl u FixMe wrt to a set of constraints ϕ *)
    | _ => Universe.lvl u
    end
  in
  Universe.pair (Universe.sort u) l.

Lemma normalize_leq_universe {cf: checker_flags} ϕ u :
  leq_universe ϕ (normalize u) u.
Proof.
  unfold leq_universe in *; destruct check_univs=> //.
  move=> vv Hv; case: u=> [[] ?] //; cbnr. 1,2:split=> //; lia.
  unfold univ_le_n. unfold Universe.univ_val. cbn.
  set z := valuation_sort _ _; case: z=> []; split=> //; lia.
Qed.
  

Lemma leq_universe_product_down_mon {cf: checker_flags} ϕ u u' v v' :
  leq_universe ϕ u u' ->
  leq_universe ϕ v v' ->
  leq_universe ϕ (Universe.sort_of_product (normalize u) v) (Universe.sort_of_product u' v').
Proof.
  unfold leq_universe in *; destruct check_univs=>//.
  intros H1 H2 vv Hv.
  move: {H1 H2} (H1 _ Hv) (H2 _ Hv) => /univ_le_n_equiv H1 /univ_le_n_equiv H2.
  apply univ_le_n_equiv.
  unfold Universe.sort_of_product, univ_le_n; cbn.
  depelim H2; first (rewrite H0 H2 ; by constructor).
  rewrite H0; constructor.
  move: H ; unfold lvl_le_n.
  set z := is_impredicative _ ; case: z => //.
  depelim H1.
  all: revert dependent u=> -[[]?] // ?; cbn in *.
  all: rewrite !val_sup ?UnivLevel.val_set; try lia.
Qed.  
  

(* Lemma leq_universe_product_mon {cf: checker_flags} ϕ u u' v v' :
  leq_universe ϕ u u' ->
  leq_universe ϕ v v' ->
  leq_universe ϕ (Universe.sort_of_product u v) (Universe.sort_of_product u' v').
Proof.
  unfold leq_universe in *; destruct check_univs; [|trivial].
  intros H1 H2 vv Hv. specialize (H1 _ Hv). specialize (H2 _ Hv).
  cbn in *. unfold Universe.sort_of_product.
  Unset Printing Notations. unfold Universe.univ_val.
  destruct v as [[] lv], v' as [[] lv']; cbn in *; auto.
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
Qed. *)

Lemma impredicative_product {cf:checker_flags} {ϕ l u} :
  Universe.is_prop u ->
  leq_universe ϕ (Universe.sort_of_product l u) u.
Proof.
  unfold Universe.sort_of_product.
  case: u=> [[]?] //; cbn=> ?.
  unfold leq_universe; case: check_univs=> //.
Qed.

Section UniverseLemmas.
  Context {cf:checker_flags}.

  Ltac unfold_eq_universe
    := unfold eq_universe in *; destruct check_univs; [intros v Hv|trivial].

  Lemma sup_idem s : UnivLevel.sup s s = s.
  Proof.
    apply eq_univ'; cbn.
    intro; rewrite !UnivExprSet.union_spec. intuition.
  Qed.

  (* Lemma sup_idem s : Universe.sup s s = s.
  Proof.
    destruct s;cbn;auto.
    apply f_equal.
    apply eq_univ'; cbn.
    intro; rewrite !UnivExprSet.union_spec. intuition.
  Qed. *)

  Lemma sort_of_product_idem s
    : Universe.sort_of_product s s = s.
  Proof.
    unfold Universe.sort_of_product.
    destruct (Universe.is_prop s), (Universe.is_sprop s); trea;cbn.
    all: case: s=> [??] /=; f_equal; apply sup_idem.
  Qed.

  Lemma sup_assoc s1 s2 s3 :
    UnivLevel.sup s1 (UnivLevel.sup s2 s3) = UnivLevel.sup (UnivLevel.sup s1 s2) s3.
  Proof.
    apply eq_univ'; cbn. symmetry; apply UnivExprSetProp.union_assoc.
  Qed.

  (* LevelInstance universe_sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) UnivLevel.sup.
  Proof.
    intros s1 s1' H1 s2 s2' H2.
    unfold_eq_universe. specialize (H1 v Hv). specialize (H2 v Hv).
    rewrite !val_universe_sup.
    now rewrite H1 H2.
  Qed. *)

  Lemma sort_of_product_twice u s :
    Universe.sort_of_product u (Universe.sort_of_product u s)
    = Universe.sort_of_product u s.
  Proof.
    destruct u,s;auto.
    unfold Universe.sort_of_product;cbn.
    now rewrite sup_assoc sup_idem.
  Qed.
End UniverseLemmas.


Section no_prop_leq_type.
  Context {cf:checker_flags}.
  Context (ϕ : LevelConstraintSet.t).

  Lemma succ_inj x y : UnivExpr.succ x = UnivExpr.succ y -> x = y.
  Proof.
    unfold UnivExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x : 
    UnivExprSet.In x (UnivLevel.map UnivExpr.succ l) <-> 
    exists x', UnivExprSet.In x' l /\ x = UnivExpr.succ x'.
  Proof.
    rewrite UnivLevel.map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (UnivExpr.succ l) = val v l + 1.
  Proof.
    destruct l as []; simpl. cbn. lia. 
  Qed.

  Lemma val_map_succ v l : val v (UnivLevel.map UnivExpr.succ l) = val v l + 1.
  Proof.
    remember (UnivLevel.map UnivExpr.succ l) eqn:eq.
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
    leq_universe ϕ (Universe.super (normalize u)) (Universe.super u').
  Proof.
    unfold leq_universe. destruct check_univs; [|trivial].
    intros H v Hv; move:u u' {H} (H v Hv)=> [[|||?|?]?] [??]. 
    all: cbn; try move=>[??] ; split=> //; rewrite !val_map_succ; lia.
  Qed.

  (* Lemma leq_universe_props u1 u2 :
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
       : univ_lemmas. *)
  
  Lemma leq_prop_prop {l l'} :
    Universe.is_prop l -> Universe.is_prop l' ->
    leq_universe ϕ l l'.
  Proof.
    red. destruct check_univs; [|trivial].
    intros H1 H2 v Hv. eapply is_prop_val in H1; eapply is_prop_val in H2.
    apply univ_le_n_equiv.
    rewrite -> H1, H2. constructor=> //=.
  Qed.

  Lemma leq_sprop_sprop {l l'} :
    Universe.is_sprop l -> Universe.is_sprop l' ->
    leq_universe ϕ l l'.
  Proof.
    red. destruct check_univs; [|trivial].
    intros H1 H2 v Hv. eapply is_sprop_val in H1; eapply is_sprop_val in H2.
    apply univ_le_n_equiv.
    rewrite -> H1, H2. by constructor.
  Qed.
  
  (* Lemma leq_prop_is_prop_sprop {x s} :
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
  Qed. *)

End no_prop_leq_type.
*)