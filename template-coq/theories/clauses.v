From Coq Require Import ssreflect ssrbool.
From Coq Require Import Program RelationClasses Morphisms.
From Coq Require Import OrderedTypeAlt OrderedTypeEx MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils Universes.
From Equations Require Import Equations.
Set Equations Transparent.

Definition clause : Type := nonEmptyLevelExprSet × LevelExpr.t.
Module Clause.
  Definition t := clause.

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : RelationClasses.Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | lt_clause1 l e e' : LevelExpr.lt e e' -> lt_ (l, e) (l, e')
  | lt_clause2 l l' b b' : LevelExprSet.lt l.(t_set) l'.(t_set) -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : RelationClasses.StrictOrder lt.
  Proof.
    constructor.
    - intros x X; inversion X; subst. now eapply LevelExpr.lt_strorder in H1.
      eapply LevelExprSet.lt_strorder; eassumption.
    - intros x y z X1 X2; invs X1; invs X2; constructor; tea.
      etransitivity; tea.
      etransitivity; tea.
  Qed.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
    intros x x' H1 y y' H2. unfold lt. subst. reflexivity.
  Qed.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match LevelExprSet.compare l1.(t_set) l2.(t_set) with
      | Eq => LevelExpr.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros [? ?] [? ?]; cbn; repeat constructor.
    destruct (LevelExprSet.compare_spec n n0); repeat constructor; tas.
    eapply LevelExprSet.eq_leibniz in H. apply NonEmptySetFacts.eq_univ in H.
    subst. cbn in *.
    destruct (LevelExpr.compare_spec t0 t1); repeat constructor; tas. now subst.
  Qed.

  Global Instance reflect_t : ReflectEq t := reflect_prod _ _ .

  Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2} := Classes.eq_dec.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End Clause.

Module Clauses := MSetList.MakeWithLeibniz Clause.
Module ClausesFact := WFactsOn Clause Clauses.
Module ClausesProp := WPropertiesOn Clause Clauses.
Module ClausesDecide := WDecide (Clauses).
Ltac clsets := ClausesDecide.fsetdec.

Definition clauses := Clauses.t.

Lemma filter_add {p x s} : Clauses.Equal (Clauses.filter p (Clauses.add x s)) (if p x then Clauses.add x (Clauses.filter p s) else Clauses.filter p s).
Proof.
  intros i.
  rewrite Clauses.filter_spec.
  destruct (eqb_spec i x); subst;
  destruct (p x) eqn:px; rewrite !Clauses.add_spec !Clauses.filter_spec; intuition auto || congruence.
Qed.

Instance proper_fold_transpose {A} (f : Clauses.elt -> A -> A) :
  transpose eq f ->
  Proper (Clauses.Equal ==> eq ==> eq) (Clauses.fold f).
Proof.
  intros hf s s' Hss' x ? <-.
  eapply ClausesProp.fold_equal; tc; tea.
Qed.
Existing Class transpose.

Lemma clauses_fold_filter {A} (f : Clauses.elt -> A -> A) (p : Clauses.elt -> bool) cls acc : 
  transpose Logic.eq f ->
  Clauses.fold f (Clauses.filter p cls) acc = 
  Clauses.fold (fun elt acc => if p elt then f elt acc else acc) cls acc.
Proof.
  intros hf.
  symmetry. eapply ClausesProp.fold_rec_bis.
  - intros s s' a eq. intros ->. 
    eapply ClausesProp.fold_equal; tc. auto.
    intros x.
    rewrite !Clauses.filter_spec.
    now rewrite eq.
  - now cbn.
  - intros.
    rewrite H1.
    rewrite filter_add.
    destruct (p x) eqn:px => //.
    rewrite ClausesProp.fold_add //.
    rewrite Clauses.filter_spec. intuition auto.
Qed.

Module MoreLevel.

  Include Level.

  Lemma compare_sym : forall x y : t, (compare y x) = CompOpp (compare x y).
  Proof.
    induction x; destruct y; simpl; auto.
    apply StringOT.compare_sym.
    apply PeanoNat.Nat.compare_antisym.
  Qed.
  
  Lemma eq_refl x : eq x x.
  Proof. red. reflexivity. Qed.

  Lemma eq_sym x y : eq x y -> eq y x.
  Proof. unfold eq. apply symmetry. Qed.
 
  Lemma eq_trans x y z : eq x y -> eq y z -> eq x z.
  Proof. unfold eq. apply transitivity. Qed.

  Infix "?=" := compare.

  Lemma compare_trans :
    forall c (x y z : t), (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z.
    destruct (compare_spec x y) => <-; subst.
    destruct (compare_spec y z); auto.
    destruct (compare_spec y z); auto; try congruence.
    destruct (compare_spec x z); auto; try congruence.
    subst. elimtype False. eapply (irreflexivity (A:=t)). etransitivity; [exact H|exact H0].
    elimtype False. eapply (irreflexivity (A:=t)). etransitivity; [exact H|]. 
    eapply transitivity; [exact H0|exact H1].
    destruct (compare_spec y z); auto; try congruence.
    destruct (compare_spec x z); auto; try congruence.
    subst. elimtype False. eapply (irreflexivity (A:=t)). etransitivity; [exact H|exact H0].
    elimtype False. eapply (irreflexivity (A:=t)). etransitivity; [exact H|]. 
    eapply transitivity; [exact H1|exact H0].
  Qed.

  Lemma compare_eq {x y} : compare x y = Eq -> x = y.
  Proof.
    destruct (compare_spec x y) => //.
  Qed.
End MoreLevel.

Module LevelOT := OrderedType_from_Alt MoreLevel.
Module LevelMap := FMapAVL.Make LevelOT.
Module LevelMapFact := FMapFacts.WProperties LevelMap.

Definition strict_subset (s s' : LevelSet.t) :=
  LevelSet.Subset s s' /\ ~ LevelSet.Equal s s'.

Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
Proof.
  intros hs []. split => //. lsets.
  intros heq. apply H0. lsets.
Qed.

Lemma strict_subset_cardinal s s' : strict_subset s s' -> LevelSet.cardinal s < LevelSet.cardinal s'.
Proof.
  intros [].
  assert (LevelSet.cardinal s <> LevelSet.cardinal s').
  { intros heq. apply H0. 
    intros x. split; intros. now apply H.
    destruct (LevelSet.mem x s) eqn:hin.
    eapply LevelSet.mem_spec in hin.
    auto. eapply LevelSetProp.FM.not_mem_iff in hin.
    exfalso.
    eapply LevelSetProp.subset_cardinal_lt in hin; tea.
    lia. }
  enough (LevelSet.cardinal s <= LevelSet.cardinal s') by lia.
  now eapply LevelSetProp.subset_cardinal.
Qed.

Record model := {
  model_values :> LevelMap.t nat
}.

(* Print maps to nat nicely *)
Fixpoint to_bytes (s : string) : list Byte.byte :=
  match s with
  | String.EmptyString => []
  | String.String b s => b :: to_bytes s
  end.

Declare Scope levelnat_scope.
Delimit Scope levelnat_scope with levelnat.
Module LevelNatMapNotation.
  Import LevelMap.Raw.
  Notation levelmap := (tree nat) (only parsing).
  Definition parse_levelnat_map (l : list Byte.byte) : option levelmap :=
    None.
  Definition print_levelnat_map (m : levelmap) :=
    let list := LevelMap.Raw.elements m in
    print_list (fun '(l, w) => string_of_level l ^ " -> " ^ string_of_nat w) nl list.
   
  Definition print_levelmap (l : levelmap) : list Byte.byte :=
    to_bytes (print_levelnat_map l).
   
  String Notation levelmap parse_levelnat_map print_levelmap
      : levelnat_scope.
End LevelNatMapNotation.
Import LevelNatMapNotation.
Arguments LevelMap.Bst {elt} this%levelnat {is_bst}.

Definition premise (cl : clause) := fst cl.

Definition concl (cl : clause) := snd cl.

Definition level_value (m : model) (level : Level.t) : nat :=
  match LevelMap.find level m with
  | Some val => val
  | None => 0
  end.

#[program] 
Definition choose (l : nonEmptyLevelExprSet) : LevelExpr.t :=
  match LevelExprSet.choose l with
  | Some l => l
  | None => !%prg
  end.

Next Obligation.
  symmetry in Heq_anonymous.
  eapply LevelExprSet.choose_spec2, LevelExprSetFact.is_empty_1 in Heq_anonymous.
  destruct l. cbn in *. congruence.    
Qed.


Definition min_atom_value (m : model) (atom : LevelExpr.t) :=
  let '(l, k) := atom in
  (Z.of_nat (level_value m l) - Z.of_nat k)%Z.

Definition min_premise (m : model) (l : nonEmptyLevelExprSet) : Z :=
  LevelExprSet.fold (fun atom min => Z.min (min_atom_value m atom) min) l 
   (min_atom_value m (choose l)).

Definition satisfiable_atom (m : model) (atom : Level.t * nat) : bool :=
  let '(l, k) := atom in
  match LevelMap.find l m with
  | Some val => k <=? val
  | None => false
  end.
  
Definition satisfiable_premise (m : model) (l : nonEmptyLevelExprSet) :=
  LevelExprSet.for_all (satisfiable_atom m) l.

(* Definition valid_clause (m : model) (cl : clause) := *)
  (* implb (satisfiable_premise m (premise cl)) (satisfiable_atom m (concl cl)). *)

Definition valid_clause (m : model) (cl : clause) :=
  let k0 := min_premise m (premise cl) in
  if (k0 <? 0)%Z then true
  else let (l, k) := concl cl in 
    k + Z.to_nat k0 <=? level_value m l.
  
Definition is_model (cls : clauses) (m : model) : bool :=
  Clauses.for_all (valid_clause m) cls.

Inductive update_result := 
  | VacuouslyTrue
  | Holds
  | DoesntHold (wm : LevelSet.t × model).

Definition update_model m l v :=
  {| model_values := LevelMap.add l v m.(model_values) |}.

Definition update_value (wm : LevelSet.t × model) (cl : clause) : update_result :=
  let (w, m) := wm in
  let k0 := min_premise m (premise cl) in
  (* cl holds vacuously as the premise doesn't hold *)
  if (k0 <? 0)%Z then VacuouslyTrue
  else 
    (* The premise does hold *)
    let (l, k) := concl cl in
    (* Does the conclusion also hold?
       We optimize a bit here, rather than adding k0 in a second stage, 
       we do it already while checking the clause. In the paper, a second
       pass computes this.
      *)
    if k + Z.to_nat k0 <=? level_value m l then Holds
    else 
      (* The conclusion doesn't hold, we need to set it higher *)
      DoesntHold (LevelSet.add l w, update_model m l (k + Z.to_nat k0)).

Definition check_clause_model cl '(modified, wm) := 
  match update_value wm cl with 
  | VacuouslyTrue => (modified, wm)
  | DoesntHold wm' => (true, wm')
  | Holds => (modified, wm)
  end.

Definition check_model_aux (cls : clauses) (wm : LevelSet.t × model) : bool × (LevelSet.t × model) :=
  Clauses.fold check_clause_model cls (false, wm).

(* If check_model = None then we have a model of all clauses, 
  othewise, we return Some (W', m') where W ⊂ W' and the model has
  been updated for at least one atom l ∈ W'. *)
Definition check_model (cls : clauses) (wm : LevelSet.t × model) := 
  let '(modified, wm) := check_model_aux cls wm in
  if modified then Some wm else None.

Lemma check_model_aux_subset {cls w v} : 
  forall b w' v', check_model_aux cls (w, v) = (b, (w', v')) -> LevelSet.Subset w w'.
Proof.
  intros w' v'.
  unfold check_model, check_model_aux, check_clause_model. revert w' v'.
  eapply ClausesProp.fold_rec => //.
  { intros. noconf H0. reflexivity. }
  intros x a s' s'' hin nin hadd IH.
  intros b w' v'. destruct a.
  destruct p as []. 
  unfold update_value.
  destruct Z.ltb. intros [= -> -> ->] => //.
  now eapply IH.
  destruct x as [prem [l k]]; cbn.
  destruct Nat.leb. intros [= -> -> ->] => //. now eapply IH.
  intros [= <- <- <-]. intros x inx.
  eapply LevelSet.add_spec.
  specialize (IH _ _ _ eq_refl).
  now right.
Qed.

Lemma check_model_subset {cls w v} : 
  forall w' v', check_model cls (w, v) = Some (w', v') -> LevelSet.Subset w w'.
Proof.
  intros w' v'. unfold check_model.
  destruct check_model_aux eqn:cm.
  destruct p as [W m].
  eapply check_model_aux_subset in cm.
  destruct b => //. now intros [= <- <-].
Qed.

Definition restrict_clauses (cls : clauses) (W : LevelSet.t) :=
  Clauses.filter (fun '(prem, concla) =>
    LevelSet.subset (LevelExprSet.levels prem) W &&
    LevelSet.mem (LevelExpr.get_level concla) W) cls.

Lemma in_restrict_clauses (cls : clauses) (concls : LevelSet.t) cl :
  Clauses.In cl (restrict_clauses cls concls) -> 
  LevelSet.In (LevelExpr.get_level (concl cl)) concls /\ Clauses.In cl cls.
Proof.
  unfold restrict_clauses.
  rewrite Clauses.filter_spec.
  destruct cl. cbn. firstorder eauto.
  move/andP: H0 => [] /LevelSet.subset_spec hsub /LevelSet.mem_spec hmem //.
Qed.

Definition clauses_with_concl (cls : clauses) (concl : LevelSet.t) :=
  Clauses.filter (fun '(prem, concla) => LevelSet.mem (LevelExpr.get_level concla) concl) cls.

Lemma in_clauses_with_concl (cls : clauses) (concls : LevelSet.t) cl :
  Clauses.In cl (clauses_with_concl cls concls) <-> 
  LevelSet.In (LevelExpr.get_level (concl cl)) concls /\ Clauses.In cl cls.
Proof.
  unfold clauses_with_concl.
  rewrite Clauses.filter_spec.
  destruct cl. rewrite LevelSet.mem_spec. cbn. firstorder eauto.
Qed.

Definition clauses_conclusions (cls : clauses) : LevelSet.t :=
  Clauses.fold (fun cl acc => LevelSet.add (LevelExpr.get_level (concl cl)) acc) cls LevelSet.empty.
  
Lemma clauses_conclusions_spec a cls : 
  LevelSet.In a (clauses_conclusions cls) <-> 
  exists cl, Clauses.In cl cls /\ LevelExpr.get_level (concl cl) = a.
Proof.
  unfold clauses_conclusions.
  eapply ClausesProp.fold_rec; clear.
  - move=> s' he /=. rewrite LevelSetFact.empty_iff.
    firstorder auto.
  - move=> cl ls cls' cls'' hin hnin hadd ih.
    rewrite LevelSet.add_spec. firstorder eauto.
    specialize (H0 x). cbn in H0.
    apply hadd in H1. firstorder eauto.
    subst. left. now destruct x.
Qed.

Lemma clauses_conclusions_clauses_with_concl cls concl : 
  LevelSet.Subset (clauses_conclusions (clauses_with_concl cls concl)) concl.
Proof.
  intros x [cl []] % clauses_conclusions_spec.
  eapply in_clauses_with_concl in H as [].
  now rewrite H0 in H.
Qed.

Lemma clauses_conclusions_restrict_clauses cls W : 
  LevelSet.Subset (clauses_conclusions (restrict_clauses cls W)) W.
Proof.
  intros x [cl []] % clauses_conclusions_spec.
  eapply in_restrict_clauses in H as [].
  now rewrite H0 in H.
Qed.

Definition in_clauses_conclusions (cls : clauses) (x : Level.t): Prop :=
  exists cl, Clauses.In cl cls /\ (LevelExpr.get_level cl.2) = x.

Infix "⊂_lset" := LevelSet.Subset (at level 70).


Lemma check_model_subset_clauses cls w m : 
  forall w' m', check_model cls (w, m) = Some (w', m') -> 
  w ⊂_lset w' /\ w' ⊂_lset (LevelSet.union w (clauses_conclusions cls)).
Proof.
  intros w' v' cm. split; [now eapply check_model_subset|].
  move: cm.
  unfold check_model. revert w' v'.
  unfold clauses_conclusions.
Admitted.
Definition levelexpr_value : LevelExprSet.elt -> nat := snd.

Coercion levelexpr_value : LevelExprSet.elt >-> nat.

Definition v_minus_w_bound (V W : LevelSet.t) (m : model) := 
  LevelMap.fold (fun w v acc => Nat.max v acc) 
    (LevelMapFact.filter (fun l _ => LevelSet.mem l (LevelSet.diff V W)) m) 0.
  
Definition premise_min (l : nonEmptyLevelExprSet) : nat :=
  LevelExprSet.fold (fun atom min => Nat.min atom min) l 0.

Definition gain (cl : clause) : Z :=
  Z.of_nat (levelexpr_value (concl cl)) - Z.of_nat (premise_min (premise cl)).

Definition max_gain (cls : clauses) := 
  Clauses.fold (fun cl acc => Nat.max (Z.to_nat (gain cl)) acc) cls 0.


(*  
  eapply (ClausesProp.fold_rel (R := fun x y => forall (w' : LevelSet.t) (m : model), x = Some (w', m) -> LevelSet.Subset w' (LevelSet.union w y))) => //.
  intros x a s' hin IH w' m'.
  destruct a.
  - destruct p as []. specialize (IH _ _ eq_refl).
    unfold update_value.
    destruct Z.ltb. intros [= -> ->] => //; lsets.
    destruct x as [prem [l k]]; cbn.
    destruct Nat.leb.
    intros [= -> ->] => //. lsets.
    intros [= <- <-]. lsets.
  - unfold update_value.
    destruct Z.ltb. intros => //.
    destruct x as [prem [l k]]; cbn.
    destruct Nat.leb => //.
    intros [= <- <-]. lsets.
Qed. *)

Definition model_same_domain (m m' : model) := 
  forall l, LevelMap.In l m <-> LevelMap.In l m'.

#[local] Instance model_same_domain_refl : Reflexive model_same_domain.
Proof. intros m l. reflexivity. Qed.

#[local] Instance model_same_domain_trans : Transitive model_same_domain.
Proof. intros m m' m'' h h' l. rewrite (h l). apply h'. Qed.

Definition model_le (m m' : model) := 
  forall l k, LevelMap.MapsTo l k m -> 
  exists k', LevelMap.MapsTo l k' m' /\ k <= k'.
    
Infix "⩽" := model_le (at level 70). (* \leqslant *)

Definition model_map_outside V (m m' : model) :=
  forall l, ~ LevelSet.In l V -> 
    forall k, LevelMap.MapsTo l k m <-> LevelMap.MapsTo l k m'.

#[local] Instance model_map_outside_refl V : Reflexive (model_map_outside V).
Proof. intros m l. reflexivity. Qed.

#[local] Instance model_map_outside_trans V : Transitive (model_map_outside V).
Proof.
  intros m m' m'' h h' l hnin k.
  rewrite (h l hnin k). now apply h'.
Qed.

(** The termination proof relies on the correctness of check_model: 
  it does strictly increase a value but not above [max_gain cls].
*)

Lemma check_model_spec cls w m : 
  forall w' m', check_model cls (w, m) = Some (w', m') -> 
  [/\ w ⊂_lset w',
      w' ⊂_lset (LevelSet.union w (clauses_conclusions cls)),
      exists l, LevelSet.In l w' /\ level_value m l < level_value m' l <= max_gain cls,
      model_same_domain m m' &
      model_map_outside w' m m'].
Proof. Admitted.

Record valid_model (V : LevelSet.t) (m : model) (cls : clauses) :=
  { model_model : model;
    model_clauses_conclusions : clauses_conclusions cls ⊂_lset V;
    model_ok : check_model cls (LevelSet.empty, model_model) = None;
    model_above : m ⩽ model_model;
    model_domains : model_same_domain m model_model;
    model_outside : model_map_outside V m model_model
 }.
Arguments model_model {V m cls}.
Arguments model_clauses_conclusions {V m cls}.
Arguments model_ok {V m cls}.
Arguments model_above {V m cls}.
Arguments model_domains {V m cls}.
Arguments model_outside {V m cls}.

Inductive result (V : LevelSet.t) (cls : clauses) (m : model) :=
  | Loop
  | Model (w : LevelSet.t) (m : valid_model V m cls) (prf : LevelSet.subset w V).
Arguments Loop {V cls m}.
Arguments Model {V cls m}.
Arguments exist {A P}.  
Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.
Arguments lexprod {A B}.

Definition option_of_result {V m cls} (r : result V m cls) : option model :=
  match r with
  | Loop => None
  | Model w m sub => Some m.(model_model)
  end. 

(* Definition lexprod_rel := lexprod lt lt.

#[local] Instance lexprod_rel_wf : WellFounded lexprod_rel.
Proof.
  eapply (Acc_intro_generator 1000). unfold lexprod_rel. eapply wf_lexprod, lt_wf. eapply lt_wf.
Defined.

Opaque lexprod_rel_wf. *)
 
#[tactic="idtac"]
Equations? result_inclusion {V m cls V'} (r : result V cls m) (prf : LevelSet.Subset V V') : result V' cls m :=
  result_inclusion Loop _ := Loop;
  result_inclusion (Model w m' sub) sub' := 
    Model w {| model_model := m'.(model_model) |} _.
Proof.
  - transitivity V => //. now eapply m'.(model_clauses_conclusions).
  - apply m'.
  - apply m'.
  - apply m'.
  - intros x hin. apply m'. intros hv. apply LevelSet.subset_spec in sub.
    apply sub' in hv. now apply hin.
  - eapply LevelSet.subset_spec. eapply LevelSet.subset_spec in sub.
    now transitivity V.
Qed.


(* Lemma clauses_conclusions_diff cls cls' :
  clauses_conclusions cls ⊂_lset clauses_conclusions cls' ->
  clauses_conclusions (Clauses.diff cls cls') =_lset 
  LevelSet.diff (clauses_conclusions cls) (clauses_conclusions cls').
Proof.
  intros hs x.
  rewrite LevelSet.diff_spec !clauses_conclusions_spec.
  firstorder eauto.
  exists x0. split; try (lsets || clsets).
  intros [cl []].
  eapply Clauses.diff_spec in H as []. 
  red in hs. specialize (hs x).
  rewrite clauses_conclusions_spec in hs.
  forward hs. exists x0 => //.
  rewrite clauses_conclusions_spec in hs.
  destruct hs as [cl' []].
  


  apply H1.
  rewrite in_clauses_with_concl. split => //.
  now rewrite H0.
Qed. *)


Lemma clauses_conclusions_diff cls s : 
  clauses_conclusions (Clauses.diff cls (clauses_with_concl cls s)) ⊂_lset
  LevelSet.diff (clauses_conclusions cls) s.
Proof.
  intros a. rewrite LevelSet.diff_spec !clauses_conclusions_spec.
  firstorder eauto.
  exists x; split => //.
  now rewrite Clauses.diff_spec in H.
  intros ha.
  rewrite Clauses.diff_spec in H; destruct H as [].
  apply H1.
  rewrite in_clauses_with_concl. split => //.
  now rewrite H0.
Qed.

Lemma diff_eq U V : LevelSet.diff V U =_lset V <-> LevelSet.inter V U =_lset LevelSet.empty.
Proof. split. lsets. lsets. Qed.

Lemma nequal_spec U V : strict_subset U V -> 
  exists x, LevelSet.In x V /\ ~ LevelSet.In x U.
Proof.
  intros [].
Admitted.

Lemma strict_subset_diff (U V : LevelSet.t) : strict_subset U V -> strict_subset (LevelSet.diff V U) V.
Proof.
  intros []; split; try lsets.
  intros eq.
  eapply diff_eq in eq. red in eq.
  apply H0. intros x.
Admitted.
 
Lemma levelset_neq U V : LevelSet.equal U V = false -> ~ LevelSet.Equal U V.
Proof. intros eq heq % LevelSet.equal_spec. congruence. Qed.

Lemma levelset_union_same U : LevelSet.union U U =_lset U.
Proof. lsets. Qed.

Lemma fold_rel_ne [A : Type] [R : LevelSet.t -> A -> A -> Type] [f : LevelSet.elt -> A -> A]
  [g : LevelSet.elt -> A -> A] [i : A] [s : LevelSet.t] :
  transpose eq g ->
  (forall i, R LevelSet.empty i i) ->
  (forall (x : LevelSet.elt) (a : A) (b : A) s',
  LevelSet.In x s -> R s' a b -> R (LevelSet.add x s') (f x a) (g x b)) ->
  R s (LevelSet.fold f s i) (LevelSet.fold g s i).
Proof.
  intros htr hr hr'.
  eapply LevelSetProp.fold_rec_bis.
  - intros. admit.
  - intros. cbn. apply hr.
  - intros. 
    epose proof (LevelSetProp.fold_add (eqA:=eq) _ (f:=g)).
    forward H1. tc. forward H1. auto. rewrite H1 //.
    eapply hr'. auto. apply X.
Admitted.

Lemma fold_left_ne_lt (f g : nat -> LevelSet.elt -> nat) l acc : 
  l <> [] ->
  (forall acc acc' x, In x l -> acc <= acc' -> f acc x <= g acc' x) ->
  (exists x, In x l /\ forall acc acc', acc <= acc' -> f acc x < g acc' x) ->
  fold_left f l acc < fold_left g l acc.
Proof.
  generalize (le_refl acc).
  generalize acc at 2 4.
  induction l in acc |- * => //.
  intros.
  destruct l; cbn.
  { destruct H2 as [x []]. cbn in H2. destruct H2; subst => //.
    now eapply (H3 acc acc0). }
  cbn in IHl. eapply IHl.
  - apply H1 => //. now left.
  - congruence.
  - intros.
    destruct H3. subst. eapply H1 => //. now right; left.
    eapply H1 => //. now right; right.
  - destruct H2 as [x [hin IH]].
Admitted.

Lemma clauses_conclusions_diff_left cls W cls' : 
  clauses_conclusions (Clauses.diff (clauses_with_concl cls W) cls') ⊂_lset W.
Proof.
  intros l. 
  rewrite clauses_conclusions_spec.
  move=> [] cl. rewrite Clauses.diff_spec => [] [] [].
  move/in_clauses_with_concl => [] hin ? ? eq.
  now rewrite eq in hin.
Qed.

Lemma LevelSet_In_elements l s : 
  In l (LevelSet.elements s) <-> LevelSet.In l s.
Proof.
  rewrite LevelSetFact.elements_iff.
  now rewrite InA_In_eq.
Qed.

Lemma clauses_empty_eq {s} : Clauses.Empty s -> Clauses.Equal s Clauses.empty.
Proof. clsets. Qed.

Lemma update_value_valid {W m cl} : 
  match update_value (W, m) cl with
  | VacuouslyTrue | Holds => valid_clause m cl
  | DoesntHold _ => ~~ valid_clause m cl
  end.
Proof.
  unfold update_value, valid_clause.
  destruct Z.ltb => //.
  destruct cl as [prem [l k]]; cbn.
  destruct Nat.leb => //.
Qed.

Lemma valid_update_value {W m cl} : 
  valid_clause m cl -> 
  match update_value (W, m) cl with
  | VacuouslyTrue | Holds => true
  | DoesntHold _ => false
  end.
Proof.
  unfold update_value, valid_clause.
  destruct Z.ltb => //.
  destruct cl as [prem [l k]]; cbn.
  destruct Nat.leb => //.
Qed.

Lemma check_model_aux_false {cls acc acc'} : check_model_aux cls acc = (false, acc') -> acc = acc'.
Proof.
  unfold check_model_aux, check_clause_model.
  eapply ClausesProp.fold_rec.
  - intros s emp [=] => //.
  - intros cl [modified [w' m']] cls' cls'' incl nincls' incls''.
    intros IH.
    destruct update_value eqn:upd => //.
Qed.

(* Lemma check_model_aux_true {cls acc acc'} : check_model_aux cls acc = (true, acc') -> acc = acc'.
Proof.
  unfold check_model_aux.
  eapply ClausesProp.fold_rec.
  - intros s emp [=] => //.
  - intros cl [modified [w' m']] cls' cls'' incl nincls' incls''.
    intros IH.
    destruct update_value eqn:upd => //.
Qed. *)

Lemma check_model_aux_model {cls acc} : 
  check_model_aux cls acc = (false, acc) <-> is_model cls acc.2.
Proof.
  unfold check_model_aux, check_clause_model.
  unfold is_model.
  unfold is_true; rewrite -ClausesFact.for_all_iff.
  eapply ClausesProp.fold_rec.
  - intros s emp.
    split => //.
    intros [=] x hx. clsets.
  - intros cl [modified [w' m']] cls' cls'' incl nincls' incls''.
    intros IH.
    split.
    * move: (@update_value_valid w' m' cl).
      destruct update_value eqn:upd => //; intros vcl [= -> <-] ;
        destruct IH as [IH _]; specialize (IH eq_refl).
      intros x hx; apply incls'' in hx as []; subst. exact vcl. now apply IH.
      intros x hx; apply incls'' in hx as []; subst. exact vcl. now apply IH.
    * intros hf.
      assert (valid_clause acc.2 cl).
      { apply hf. apply incls''. intuition auto. }
      destruct IH as [_ IH]. forward IH.
      { intros x hx. apply hf. apply incls''. now right. }
      noconf IH.
      move: (@valid_update_value w' m' cl H).
      destruct update_value eqn:upd => //.
Qed.

Lemma clauses_for_all_neg {p s}: 
  ~~ Clauses.for_all p s <-> ~ Clauses.For_all p s.
Proof.
  intuition auto.
  rewrite ClausesFact.for_all_iff in H0. red in H. now rewrite H0 in H.
  revert H. apply contra_notN.
  rewrite ClausesFact.for_all_iff //.
Qed.

Lemma clauses_for_all_exists {p s}: 
  ~~ Clauses.for_all p s <-> Clauses.exists_ (fun x => ~~ p x) s.
Proof.
  rewrite ClausesFact.for_all_b ClausesFact.exists_b.
  induction (Clauses.elements s).
  - cbn; auto. reflexivity.
  - cbn. rewrite negb_and. intuition auto.
    move/orP: H1 => [->|] //. move/H. intros ->. now rewrite orb_true_r.
    move/orP: H1 => [->|] //. move/H0. intros ->. now rewrite orb_true_r.
Qed.
#[local] Instance model_le_refl : Reflexive model_le.
Proof. intros x l k map. exists k; split => //. Qed.

#[local] Instance model_le_trans : Transitive model_le.
Proof. intros m m' m'' mm' m'm'' l k map.
  apply mm' in map as [k' [map ?]].
  apply m'm'' in map as [k'' [map ?]]. exists k''. split => //. lia.
Qed.

Lemma update_model_monotone m l k : level_value m l <= k -> m ⩽ update_model m l k.
Proof.
  intros hl.
  intros l' k' maps. 
  unfold update_model. cbn.
  destruct (eqb_spec l l').
  - exists k. move: hl. subst l'.
    unfold level_value.
    rewrite (LevelMap.find_1 maps).
    intros hle. 
    split => //. eapply LevelMap.add_1. eapply LevelMap.E.eq_refl.
  - exists k'. split => //. apply LevelMap.add_2 => //.
    intros he. destruct (MoreLevel.compare_spec l l'); congruence.
Qed.

Lemma check_clause_model_inv {cl modified w m b wm'} : 
  check_clause_model cl (modified, (w, m)) = (b, wm') ->
  m ⩽ wm'.2.
Proof.
  unfold check_clause_model.
  destruct (update_value (w, m) cl) eqn:upd.
  * now intros [= <- <-].
  * now intros [= <- <-].
  * intros [= <- <-].
    move: upd.
    unfold update_value.
    case: Z.ltb_spec => //.
    destruct cl as [prem [l k]] => /=.
    intros hprem.
    case: Nat.leb_spec => // hlt.
    intros [= <-]. cbn.
    eapply update_model_monotone. lia.  
Qed.
  
Lemma check_clause_model_intact {cl modified w m wm'} : 
  check_clause_model cl (modified, (w, m)) = (false, wm') -> valid_clause m cl /\ wm' = (w, m).
Proof.
  unfold check_clause_model.
  move: (@update_value_valid w m cl).
  destruct (update_value (w, m) cl) eqn:upd.
  * intros valid [= -> <-]. split => //.
  * intros valid [= -> <-]. split => //.
  * intros _ [=].
Qed.

Lemma check_clause_model_modify {cl w m wm'} : 
  check_clause_model cl (false, (w, m)) = (true, wm') -> ~~ valid_clause m cl.
Proof.
  unfold check_clause_model.
  destruct (update_value (w, m) cl) eqn:upd.
  * now intros [= <- <-].
  * now intros [= <- <-].
  * intros [= <-].
    move: upd.
    unfold update_value, valid_clause.
    case: Z.ltb_spec => //.
    destruct cl as [prem [l k]] => /=.
    intros hprem.
    case: Nat.leb_spec => // hlt.
Qed.

Lemma check_model_aux_model_le {cls acc acc' b} : 
  check_model_aux cls acc = (b, acc') -> acc.2 ⩽ acc'.2.
Proof.
  unfold check_model_aux.
  revert b acc'.
  eapply ClausesProp.fold_rec.
  - intros s emp b acc'. intros [=]. subst. reflexivity. 
  - intros cl [modified [w' m']] cls' cls'' incl nincls' incls''.
    intros IH b acc'.
    move/check_clause_model_inv.
    specialize (IH _ _ eq_refl). cbn in IH. now intros; transitivity m'.
Qed.

Lemma check_model_aux_not_model {cls acc acc'} : 
  check_model_aux cls acc = (true, acc') -> ~~ is_model cls acc.2.
Proof.
  unfold check_model_aux.
  unfold is_model. 
  rewrite clauses_for_all_exists /is_true ClausesFact.exists_b.
  rewrite Clauses.fold_spec.
  revert acc acc'. induction (Clauses.elements cls); intros acc acc'.
  - cbn. intros [=].
  - cbn -[check_clause_model].
    destruct (check_clause_model a) eqn:cl.
    destruct acc as [w m].
    pose proof (check_clause_model_inv cl) as accle.
    destruct b.
    * intros _. apply/orP. left. cbn.
      now eapply check_clause_model_modify.
    * intros hl. specialize (IHl _ _ hl).
      cbn. apply/orP. right.
      apply check_clause_model_intact in cl as []. subst p. exact IHl.
Qed.

Lemma check_model_is_model {W cls m} : check_model cls (W, m) = None <-> is_model cls m.
Proof.
  unfold check_model, is_model.
  destruct check_model_aux eqn:caux.
  destruct b => //. intuition auto. congruence.
  { eapply check_model_aux_not_model in caux.
    rewrite /is_model /= // in caux. now rewrite H in caux. }
  intuition auto.
  pose proof (check_model_aux_false caux). subst p.
  now rewrite check_model_aux_model in caux.
Qed.

Lemma check_model_update {W cls m wm'} : check_model cls (W, m) = Some wm' -> ~~ is_model cls m /\ m ⩽ wm'.2.
Proof.
  unfold check_model, is_model.
  destruct check_model_aux eqn:caux.
  destruct b => //. intros [= <-]. intuition auto. 
  now eapply check_model_aux_not_model in caux.
  now eapply check_model_aux_model_le in caux.
Qed.

Infix "↓" := clauses_with_concl (at level 70). (* \downarrow *)
Infix "⇂" := restrict_clauses (at level 70). (* \downharpoonright *)

Lemma is_model_union {cls cls' m} : 
  is_model cls m -> is_model cls' m -> is_model (Clauses.union cls cls') m.
Proof.
  rewrite /is_model. rewrite /is_true -!ClausesFact.for_all_iff.
  now move=> ism ism' x /Clauses.union_spec [].
Qed.

#[local] Instance Clauses_For_All_proper : Proper (eq ==> Clauses.Equal ==> iff) Clauses.For_all.
Proof.
  intros x y -> cl cl' eqcl.
  unfold Clauses.For_all. now setoid_rewrite eqcl.
Qed.

#[local] Instance Clauses_for_all_proper : Proper (eq ==> Clauses.Equal ==> eq) Clauses.for_all.
Proof.
  intros x y -> cl cl' eqcl.
  apply iff_is_true_eq_bool.
  rewrite /is_true -!ClausesFact.for_all_iff. now rewrite eqcl.
Qed.

#[local] Instance is_model_proper : Proper (Clauses.Equal ==> eq ==> eq) is_model.
Proof.
  intros cl cl' eqcl x y ->. unfold is_model. now rewrite eqcl.
Qed.

Definition extends_model {W cls m m'} : 
  m' ⩽ m ->
  model_same_domain m' m ->
  model_map_outside W m' m ->
  result W cls m -> result W cls m'.
Proof.
  intros leq ldom lout []. exact Loop.
  econstructor 2; tea.
  destruct m0. econstructor; tea.
  - now transitivity m.
  - now transitivity m.
  - now transitivity m.
Qed.

Lemma model_le_values (m m' : model) x : m ⩽ m' -> level_value m x <= level_value m' x.
Proof.
  intros lem. specialize (lem x).
  unfold level_value.
  destruct LevelMap.find eqn:hl => //. 2:lia.
  apply LevelMap.find_2 in hl. specialize (lem _ hl) as [k' [mapsto leq]].
  now rewrite (LevelMap.find_1 mapsto).
Qed.

Lemma level_value_MapsTo {k e} {m : model} : 
  LevelMap.MapsTo k e m -> level_value m k = e.
Proof.
  unfold level_value.
  move=> mapto; rewrite (LevelMap.find_1 mapto) //.
Qed.

Lemma model_map_outside_weaken {W W'} {m m' : model} : 
  model_map_outside W m m' ->
  W ⊂_lset W' ->
  model_map_outside W' m m'.
Proof.
  intros hm sub x hin k.
  apply hm. intros hin'. apply sub in hin'. now apply hin.
Qed.

Infix "⊂_clset" := Clauses.Subset (at level 70).

Lemma max_gain_in cl cls : 
  Clauses.In cl cls ->
  Z.to_nat (gain cl) <= max_gain cls.
Proof.
  intros hin.
  unfold max_gain. revert cl hin.
  eapply ClausesProp.fold_rec.
  - intros s' ise hin. firstorder eauto.
  - intros x a s' s'' xs nxs' hadd IH cl' hin'.
    eapply hadd in hin' as [].
    * subst x. lia.
    * specialize (IH _ H). lia.
Qed.

Definition max_gain_subset (cls cls' : Clauses.t) : 
  cls ⊂_clset cls' ->
  max_gain cls <= max_gain cls'.
Proof.
  unfold max_gain at 1.
  revert cls'.
  eapply ClausesProp.fold_rec.
  - intros s' ise sub. lia.
  - intros x a s' s'' xs nxs' hadd IH cls'' hs.
    specialize (IH cls''). forward IH. transitivity s'' => //. 
    intros ??. now apply hadd.
    assert (incls'' : Clauses.In x cls'').
    { now apply hs, hadd. }
    apply max_gain_in in incls''. lia.
Qed.

Section InnerLoop.
  Context (V : LevelSet.t) 
    (loop : forall (V' : LevelSet.t) (cls : clauses) (m : model) (p : clauses_conclusions cls ⊂_lset V'),
    LevelSet.cardinal V' < LevelSet.cardinal V -> result V' cls m). 
  
  Definition measure (W : LevelSet.t) (cls : clauses) (m : model) : nat := 
    let bound := v_minus_w_bound V W m in
    let cls := (Clauses.diff (cls ↓ W) (cls ⇂ W)) in
    let maxgain := max_gain cls in 
    LevelSet.fold (fun w acc => 
        Nat.add acc (bound + maxgain - level_value m w)) W 0.
  Notation cls_diff cls W := (Clauses.diff (cls ↓ W) (cls ⇂ W)) (only parsing).
  
(*
  Equations? extend_model {W cls} (m : valid_model W (cls ⇂ W))
    (r : result W (Clauses.diff (cls ↓ W) (cls ⇂ W)))
    : result W (cls ↓ W) :=
    extend_model _ Loop := Loop;
    extend_model m (Model w m' sub) := 
      Model w {| model_model := m'.(model_model) |} _.
  Proof.
    - apply LevelSet.subset_spec in sub. now apply clauses_conclusions_clauses_with_concl in H. 
    - eapply sub. now eapply m.(model_clauses_conclusions).
    - apply m.
    - eapply LevelSet.subset_spec. eapply LevelSet.subset_spec in sub.
      now transitivity V.
  Qed.
  *)

  Lemma v_minus_w_bound_irrel {W} m m' : 
    model_map_outside W m m' ->
    v_minus_w_bound V W m = v_minus_w_bound V W m'.
  Proof.
    unfold v_minus_w_bound.
    intros out. eapply LevelMapFact.fold_Equal. tc. cbn.
    { intros x y eq. cbn. solve_proper. }
    { intros x y. cbn. intros e e' a neq. lia. }
    apply LevelMapFact.F.Equal_mapsto_iff.
    intros k e. rewrite -> LevelMapFact.filter_iff.
    2:{ intros x y eq. eapply MoreLevel.compare_eq in eq. subst y. solve_proper. }
    rewrite -> LevelMapFact.filter_iff.
    2:{ move=> x y /MoreLevel.compare_eq ->. solve_proper. }
    rewrite LevelSet.mem_spec LevelSet.diff_spec.
    intuition auto.
    - now apply out.
    - now apply out.
  Qed.
  
  Definition min_value (m : model) (atom : LevelExpr.t) :=
    let '(l, k) := atom in
    (Z.of_nat (level_value m l))%Z.
  
  Definition min_premise_value (m : model) (l : nonEmptyLevelExprSet) : Z :=
    LevelExprSet.fold (fun atom min => Z.min (min_value m atom) min) l 
     (min_value m (choose l)).

  Definition non_W_atoms W (l : nonEmptyLevelExprSet) := 
    LevelExprSet.filter (fun '(l, k) => ~~ LevelSet.mem l W) l.

  Lemma measure_model W cls m :
    clauses_conclusions cls ⊂_lset W ->
    let clsdiff := cls_diff cls W in
    measure W cls m = 0 -> is_model clsdiff m.
  Proof using.
    clear loop. 
    unfold measure, is_model.
    set (clsdiff := Clauses.diff _ _).
    intros clw hm.
    assert (LevelSet.For_all (fun w => v_minus_w_bound V W m + max_gain clsdiff <= level_value m w) W).
    { move: hm.
      generalize (v_minus_w_bound V W m) => vbound.
      eapply LevelSetProp.fold_rec.
      intros. intros x hin. firstorder eauto.
      intros x a s' s'' inw nins' hadd ih heq.
      forward ih by lia.
      intros l hin.
      apply hadd in hin as [].
      * subst x. lia.
      * now apply ih. }
    clear hm.
    eapply ClausesFact.for_all_iff. tc.
    intros cl hl.
    unfold valid_clause.
    case: Z.ltb_spec => // hk0.
    destruct cl as [prem [l k]] => /=.
    eapply Nat.leb_le. cbn in hk0.
    specialize (clw l).
    rewrite /clsdiff in hl. eapply Clauses.diff_spec in hl as [hl hl'].
    eapply in_clauses_with_concl in hl as [lW incls].
    specialize (H _ lW). cbn -[clsdiff] in H. cbn in lW.
    etransitivity; tea.
    set (prem' := non_W_atoms W prem).
    assert (ne : LevelExprSet.is_empty prem' = false). todo "invariant".
    set (preml := {| t_set := prem'; t_ne := ne |}).

    assert (Z.to_nat (min_premise m prem) <= 
      Z.to_nat (min_premise_value m preml) - premise_min prem).
    { unfold min_premise. unfold premise_min. todo "monotone". }
    transitivity (k + (Z.to_nat (min_premise_value m preml) - premise_min prem)). lia.
    assert (Z.to_nat (gain (prem, (l, k))) <= max_gain clsdiff). todo "easy".
    transitivity (v_minus_w_bound V W m + Z.to_nat (gain (prem, (l, k)))).
    2:lia.
    unfold gain. cbn -[min_premise_value].
    assert (premise_min prem <= (Z.to_nat (min_premise_value m preml))).
    { todo "unclear". }
    assert (k + (Z.to_nat (min_premise_value m preml) - premise_min prem) =
      (Z.to_nat (min_premise_value m preml) + k - premise_min prem)) as ->. lia.
    rewrite Z2Nat.inj_sub. lia.
    rewrite !Nat2Z.id.
    assert (Z.to_nat (min_premise_value m preml) <= v_minus_w_bound V W m).
    { todo "clearly a subset". }
    lia.
  Qed.

  Lemma is_model_equal {cls cls' m} : Clauses.Equal cls cls' -> is_model cls m -> is_model cls' m.
  Proof. now intros ->. Qed.

  Lemma union_diff_eq {cls cls'} : Clauses.Equal (Clauses.union cls (Clauses.diff cls' cls)) 
    (Clauses.union cls cls').
  Proof. clsets. Qed.

  Lemma valid_clause_le {cl m m'} : m ⩽ m' -> valid_clause m cl -> valid_clause m' cl.
  Proof.
    intros hle.
    unfold valid_clause.
    case: Z.ltb_spec => //.
    case: Z.ltb_spec => //.
    - intros premge premlt.
      intros _.
      destruct cl as [prem [l k]]. cbn in *.
  Abort.
    
  Lemma is_model_closed {cls m m'} : m ⩽ m' -> is_model cls m -> is_model cls m'.
  Proof.
    intros lem.
    unfold is_model.
    rewrite /is_true -!ClausesFact.for_all_iff.
    intros ha x hin. specialize (ha x hin).
    cbn in ha.
  Abort.

  #[tactic="idtac"]
  Equations? inner_loop (W : LevelSet.t) (cls : clauses) (init : model) 
    (m : valid_model W init (cls ⇂ W))
    (prf : [/\ strict_subset W V, ~ LevelSet.Empty W & clauses_conclusions cls ⊂_lset W]) : 
    result W (cls ↓ W) m.(model_model)
    by wf (measure W cls m.(model_model)) lt :=
    inner_loop W cls init m subWV with inspect (measure W cls m.(model_model)) := {
    | exist 0 eq => Model W {| model_model := m.(model_model) |} _
    | exist (S n) neq with loop W (cls ⇂ W) m.(model_model) _ _ := {
      | Loop => Loop
      (* We check if the model [mr] for (cls ⇂ W) extends to a model of (cls ↓ W). *)
      | Model Wr mr hsub with inspect (check_model (Clauses.diff (cls ↓ W) (cls ⇂ W)) (Wr, mr.(model_model))) := { 
        | exist None eqm => Model W {| model_model := mr.(model_model) |} _
        | exist (Some (Wconcl, mconcl)) eqm := 
          (* If it doesn't extend, then we're entitled to recursively compute a 
              better model starting with mconcl, as we have made the measure decrease:
              some atom in Wr has been strictly updated in Wconcl. *)
          extends_model _ _ _ (inner_loop W cls init (* (Clauses.diff (cls ↓ W) (cls ⇂ W))  *) {| model_model := mconcl |} _) } } }.
  Proof.
    all:cbn [model_model]; clear loop inner_loop.
    all:try solve [try apply LevelSet.subset_spec; try reflexivity].
    all:try apply LevelSet.subset_spec in hsub.
    all:destruct subWV as [WV neW clsW].
    all:try solve [intuition auto].
    - apply clauses_conclusions_clauses_with_concl.
    - rewrite check_model_is_model.
      eapply is_model_equal. 2:eapply is_model_union.
      2:{ pose proof (model_ok m). eapply check_model_is_model in H. exact H. }
      2:{ eapply measure_model. exact clsW. exact eq. }
      rewrite union_diff_eq.
      enough (cls ⇂ W ⊂_clset (cls ↓ W)) by clsets.
      { intros cl.
        move/in_restrict_clauses => [hin hcl].
        now rewrite in_clauses_with_concl. }
    - apply clauses_conclusions_restrict_clauses.
    - now eapply strict_subset_cardinal.
    - apply check_model_update in eqm as []. cbn in H0.
       transitivity (model_model mr) => //. apply mr.
    - intuition auto.
      eapply check_model_spec in eqm as [wrsub subwr hm dom out].
      transitivity mr.(model_model) => //. apply mr.
    - eapply check_model_spec in eqm as [wrsub subwr hm dom out].
      transitivity mr.(model_model) => //. apply mr.
      eapply model_map_outside_weaken; tea.
      etransitivity; tea.
      intros x.
      rewrite LevelSet.union_spec; move => []; try lsets.
      now move/clauses_conclusions_diff_left.
    - eapply clauses_conclusions_restrict_clauses.
    - rewrite check_model_is_model.
      have okm := model_ok mr.
      rewrite check_model_is_model in okm.
      pose proof (check_model_update eqm) as [nmodel lem]. cbn in lem.
      
    
    - unfold measure.
      destruct subWV as [subWV ne].
      pose proof (check_model_update eqm) as [nmodel lem].
      eapply check_model_spec in eqm as [wrsub subwr hm hout].
      destruct hm as [l [hinw hl]].
      assert (v_minus_w_bound V W mconcl = v_minus_w_bound V W m) as ->. 
      { (* Because we don't touch V - W levels *)
        cbn in lem. pose proof (model_above mr).
        symmetry.
        apply v_minus_w_bound_irrel.
        transitivity mr.(model_model). apply mr.
        eapply model_map_outside_weaken; tea.
        etransitivity; tea.
        intros l'.
        rewrite LevelSet.union_spec; move => []; try lsets.
        now move/clauses_conclusions_diff_left. }
      assert (hmaxgain : max_gain (Clauses.diff (cls ↓ W) (cls ⇂ W)) <= max_gain cls).
      { apply max_gain_subset. intros cl. rewrite Clauses.diff_spec; move=> [].
        now move/in_clauses_with_concl. }
      rewrite !LevelSet.fold_spec.
      eapply fold_left_ne_lt.
      { destruct ne. intros he. apply H0. now rewrite LevelSetProp.elements_Empty. }
      + intros.
        assert (level_value m x <= level_value mconcl x).
        { cbn in lem. have mmr := (model_above mr). 
          eapply model_le_values. now transitivity mr.(model_model). }
        lia.
      + exists l. split.
        { epose proof (clauses_conclusions_diff_left cls W (restrict_clauses cls W)).
          eapply LevelSet_In_elements. lsets. }
        intros acc acc' hacc.
        assert (level_value mconcl l <= v_minus_w_bound V W m + max_gain cls).
        { destruct hl. lia. }
        assert (level_value m l <= level_value (model_model mr) l).
        { eapply model_le_values. apply mr. }
        destruct hl. lia.
    - apply check_model_is_model. apply check_model_is_model in eqm. 
      pose proof (ism' := model_ok mr). apply check_model_is_model in ism'.
      have mu := is_model_union eqm ism'.
      rewrite /is_true -mu. apply is_model_proper => //.
      intros x.
      rewrite Clauses.union_spec Clauses.diff_spec.
      intuition auto.
      * assert (Clauses.In x (cls ↓ W)). eapply in_clauses_with_concl. split => //. apply H2.
        eapply clauses_conclusions_spec. exists x; split => //. clsets.
      * now eapply in_clauses_with_concl in H0 as [].
      * now eapply in_restrict_clauses in H3 as [].
    - apply mr.
    - apply mr.
    - apply mr.
  Qed.
End InnerLoop.

Equations? loop (V : LevelSet.t) (cls : clauses) (m : model) (prf : clauses_conclusions cls ⊂_lset V) : 
    result V
  by wf (LevelSet.cardinal V) lt :=
  loop V cls m prf with inspect (check_model cls (LevelSet.empty, m)) :=
    | exist None eqm => Model LevelSet.empty {| model_clauses := cls; model_model := m |} _
    | exist (Some (W, m')) eqm with inspect (LevelSet.equal W V) := {
      | exist true eq := Loop
      (* Loop on cls|W, with |W| < |V| *)
      | exist false neq with loop W (cls ⇂ W) m' _ := {
        | Loop := Loop
        | Model Wr mwr hsub
          (* We have a model for (cls ⇂ W), we try to extend it to a model of (csl ↓ W). *)
          with inner_loop V loop W (cls ↓ W) mwr.(model_model) _ := 
          { | Loop := Loop
            | Model Wc mwc hsub'
            (* We get a model for (cls ↓ W), we check if it extends to all clauses.
               By invariant |Wc| cannot be larger than |W|.
            *)
            with inspect (check_model cls (Wc, mwc.(model_model))) :=
            { | exist None eqm' => Model Wc {| model_clauses := cls; model_model := mwc.(model_model) |} _
              | exist (Some (Wcls, mcls)) eqm' with inspect (LevelSet.equal Wcls V) := {
                | exist true _ := Loop
                | exist false neq' := 
                (* Here Wcls < V, we've found a model for all of the clauses with conclusion
                  in W, which can now be fixed. We concentrate on the clauses whose
                  conclusion is different. Clearly |W| < |V|, but |Wcls| is not 
                  necessarily < |V| *)
                result_inclusion (loop (LevelSet.diff V W) (Clauses.diff cls (cls ↓ W)) mcls _) _ } 
            }
          }
      }
    }.
Proof.
  all:clear loop.
  all:intuition auto.
  all:eapply levelset_neq in neq.
  - now eapply clauses_conclusions_restrict_clauses.
  - eapply check_model_subset_clauses in eqm as []. cbn. 
    eapply strict_subset_cardinal. split => //. lsets.
  - eapply check_model_subset_clauses in eqm as [ww' w'wcl].
    rewrite LevelSet_union_empty in w'wcl. 
    eapply LevelSet.subset_spec in hsub.
    split => //. lsets. 
  - eapply check_model_spec in eqm as [? []].
    destruct H2 as [l [hin _]]. specialize (H l) => //.
  - apply clauses_conclusions_clauses_with_concl.
  - eapply clauses_conclusions_diff in H.
    rewrite LevelSet.diff_spec. intuition lsets.
  - eapply check_model_subset_clauses in eqm as []; tea.
    rewrite LevelSet_union_empty in H0.
    assert (strict_subset W V).
    { split => //. lsets. }
    eapply strict_subset_cardinal.
    now eapply strict_subset_diff.
  - now rewrite LevelSet.diff_spec in H.
  - eapply check_model_subset_clauses in eqm as [].
    rewrite LevelSet_union_empty in H0.
    eapply LevelSet.subset_spec. 
    eapply LevelSet.subset_spec in hsub, hsub'. 
    lsets.
Defined.
  
Definition zero_model levels := 
  LevelSet.fold (fun l acc => LevelMap.add l 0 acc) levels (LevelMap.empty _).

Definition add_max l k m := 
  match LevelMap.find l m with
  | Some k' => 
    if k' <? k then LevelMap.add l k m
    else m
  | None => LevelMap.add l k m
  end.

(* To handle the constraint checking decision problem,
  we must start with a model where all atoms [l + k]
  appearing in premises are true. Otherwise the 
  [l := 0] model is minimal for [l+1-> l+2]. 
  Starting with [l := 1], we see that the minimal model above it 
  has [l := ∞] *)

Definition min_model_map (m : LevelMap.t nat) cls : LevelMap.t nat :=
  Clauses.fold (fun '(cl, concl) acc => 
    LevelExprSet.fold (fun '(l, k) acc => 
      add_max l k acc) cl acc) cls m.

Definition min_model m cls := 
  {| model_values := min_model_map m cls |}.
      
Definition init_model cls := min_model (LevelMap.empty _) cls.

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.

Definition add_predecessors (V : LevelSet.t) cls :=
  LevelSet.fold (fun l acc => 
    Clauses.add (NonEmptySetFacts.singleton (l, 1), (l, 0)) acc) V cls.

Lemma in_add_predecessors (V : LevelSet.t) cls : 
  forall cl, 
    Clauses.In cl (add_predecessors V cls) -> 
    Clauses.In cl cls \/ LevelSet.In (LevelExpr.get_level (concl cl)) V.
Admitted.
    
Equations infer (V : LevelSet.t) (cls : clauses) (prf : LevelSet.Subset (clauses_conclusions cls) V) : result V  := 
  infer V cls prf := loop V cls (init_model cls) prf.

  (* Proof.
  eapply clauses_conclusions_spec in H as [cl []].
  eapply in_add_predecessors in H as [].
  eapply prf. rewrite clauses_conclusions_spec. now exists cl.
  now rewrite H0 in H.
Qed. *)

Definition clauses_levels (cls : clauses) : LevelSet.t := 
  Clauses.fold (fun '(cl, concl) acc => 
  LevelSet.union (LevelExprSet.levels cl)
    (LevelSet.add concl.1 acc)) cls LevelSet.empty.

Lemma in_conclusions_levels {cls} : clauses_conclusions cls ⊂_lset clauses_levels cls.
Proof.
  intros a.
  unfold clauses_levels. unfold clauses_conclusions.
  eapply (ClausesProp.fold_rel (R := fun x y => forall a, LevelSet.In a x -> LevelSet.In a y)) => //.
  intros x l l' hin hsub x' hix'.
  destruct x as [prem [l'' k]]. cbn in *. 
  eapply LevelSet.union_spec. right.
  eapply LevelSet.add_spec. 
  specialize (hsub x'). lsets.
Qed.

Equations infer_model (clauses : clauses) : result (clauses_levels clauses) :=
  infer_model clauses := infer (clauses_levels clauses) clauses in_conclusions_levels.

Definition mk_level x := LevelExpr.make (Level.Level x).
Definition levela := mk_level "a".
Definition levelb := mk_level "b".
Definition levelc := mk_level "c".
Definition leveld := mk_level "d".
Definition levele := mk_level "e".

Definition ex_levels : LevelSet.t := 
  LevelSetProp.of_list (List.map (LevelExpr.get_level) [levela; levelb; levelc; leveld; levele]).

Definition mk_clause (hd : LevelExpr.t) (premise : list LevelExpr.t) (e : LevelExpr.t) : clause := 
  (NonEmptySetFacts.add_list premise (NonEmptySetFacts.singleton hd), e).

Definition levelexpr_add (x : LevelExpr.t) (n : nat) : LevelExpr.t :=
  let (l, k) := x in (l, k + n).

(* Example from the paper *)  
Definition clause1 : clause := mk_clause levela [levelb] (LevelExpr.succ levelb).  
Definition clause2 : clause := mk_clause levelb [] (levelexpr_add levelc 3).
Definition clause3 := mk_clause (levelexpr_add levelc 1) [] leveld.
Definition clause4 := mk_clause levelb [levelexpr_add leveld 2] levele.
Definition clause5 := mk_clause levele [] levela.

Definition ex_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4].

Definition ex_loop_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4; clause5].


Example test := infer_model ex_clauses.
Example test_loop := infer_model ex_loop_clauses.

Definition print_level_nat_map (m : LevelMap.t nat) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => string_of_level l ^ " -> " ^ string_of_nat w) nl list.

Definition print_wset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list string_of_level " " list.

Definition valuation_of_model (m : model) : LevelMap.t nat :=
  let max := LevelMap.fold (fun l k acc => Nat.max k acc) m 0 in
  LevelMap.fold (fun l k acc => LevelMap.add l (max - k) acc) m (LevelMap.empty _).
  
Definition print_result {V} (m : result V) :=
  match m with
  | Loop => "looping"
  | Model w m _ => "satisfiable with model: " ^ print_level_nat_map m.(model_model) ^ nl ^ " W = " ^
    print_wset w 
    ^ nl ^ "valuation: " ^ print_level_nat_map (valuation_of_model m.(model_model))
  end.
  
Definition valuation_of_result {V} (m : result V) :=
  match m with
  | Loop => "looping"
  | Model w m _ => print_level_nat_map (valuation_of_model m.(model_model))
  end.

Eval compute in print_result test.
Eval compute in print_result test_loop.

(* Testing the unfolding of the loop function "by hand" *)
Definition hasFiniteModel {V} (m : result V) :=
  match m with
  | Loop => false
  | Model _ _ _ => true
  end.

Ltac hnf_eq_left := 
  match goal with
  | |- ?x = ?y => let x' := eval hnf in x in change (x' = y)
  end.

(* Goal hasFiniteModel test.
  hnf. hnf_eq_left. exact eq_refl.
  unfold test.
  unfold infer_model.
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
  hnf in f. simpl in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _).
  hnf in eq. unfold eq, inspect.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. unfold f', inspect.
  simp loop.
  set (f'' := check_model _ _).
  hnf in f''. simpl in f''.
  unfold inspect, f''. simp loop.
  set (eq' := LevelSet.equal _ _).
  hnf in eq'. unfold eq', inspect.
  simp loop.
  set (cm := check_model _ _).
  hnf in cm. simpl in cm.
  unfold inspect, cm. simp loop.
  exact eq_refl.
Qed. *)

Eval lazy in print_result test.
Eval compute in print_result test_loop.

Definition clauses_of_constraint (cstr : UnivConstraint.t) : clauses :=
  let '(l, d, r) := cstr in
  match d with
  | ConstraintType.Le k => 
    (* Represent r >= lk + k <-> lk + k <= r *)
    if (k <? 0)%Z then
      let n := Z.to_nat (- k) in 
      let r' := NonEmptySetFacts.map (fun l => levelexpr_add l n) r in
        LevelExprSet.fold (fun lk acc => Clauses.add (r', lk) acc) l Clauses.empty
    else
      LevelExprSet.fold (fun lk acc => 
        Clauses.add (r, levelexpr_add lk (Z.to_nat k)) acc) l Clauses.empty
  | ConstraintType.Eq => 
    let cls :=
      LevelExprSet.fold (fun lk acc => Clauses.add (r, lk) acc) l Clauses.empty
    in
    let cls' :=
      LevelExprSet.fold (fun rk acc => Clauses.add (l, rk) acc) r cls
    in cls'
  end.

Definition clauses_of_constraints (cstrs : ConstraintSet.t) : clauses :=
  ConstraintSet.fold (fun cstr acc => Clauses.union (clauses_of_constraint cstr) acc) cstrs Clauses.empty.

Definition print_premise (l : LevelAlgExpr.t) : string :=
  let (e, exprs) := LevelAlgExpr.exprs l in
  string_of_level_expr e ^
  match exprs with
  | [] => "" 
  | l => ", " ^ print_list string_of_level_expr ", " exprs 
  end.

Definition print_clauses (cls : clauses) :=
  let list := Clauses.elements cls in
  print_list (fun '(l, r) => 
    print_premise l ^ " → " ^ string_of_level_expr r) nl list.

Definition add_cstr (x : LevelAlgExpr.t) d (y : LevelAlgExpr.t) cstrs :=
  ConstraintSet.add (x, d, y) cstrs.

Coercion LevelAlgExpr.make : LevelExpr.t >-> LevelAlgExpr.t.
Import ConstraintType.
Definition test_cstrs :=
  (add_cstr levela Eq (levelexpr_add levelb 1)
  (add_cstr (LevelAlgExpr.sup levela levelc) Eq (levelexpr_add levelb 1)
  (add_cstr levelb (ConstraintType.Le 0) levela
  (add_cstr levelc (ConstraintType.Le 0) levelb
    ConstraintSet.empty)))).

Definition test_clauses := clauses_of_constraints test_cstrs.

Definition test_levels : LevelSet.t := 
  LevelSetProp.of_list (List.map (LevelExpr.get_level) [levela; levelb; levelc]).

Eval compute in print_clauses test_clauses.

Definition test' := infer_model test_clauses.
Eval compute in print_result test'.
Import LevelAlgExpr (sup).

Definition test_levels' : LevelSet.t := 
  LevelSetProp.of_list (List.map (LevelExpr.get_level) 
    [levela; levelb;
      levelc; leveld]).

Notation " x + n " := (levelexpr_add x n).

Coercion LevelExpr.make : Level.t >-> LevelExpr.t.

Fixpoint chain (l : list LevelExpr.t) :=
  match l with
  | [] => ConstraintSet.empty
  | hd :: [] => ConstraintSet.empty
  | hd :: (hd' :: _) as tl => 
    add_cstr hd (Le 10) hd' (chain tl)
  end.

Definition levels_to_n n := 
  unfold n (fun i => (Level.Level (string_of_nat i), 0)).

Definition test_chain := chain (levels_to_n 50).

Eval compute in print_clauses  (clauses_of_constraints test_chain).

(** These constraints do have a finite model that makes all implications true (not vacuously) *)
Time Eval vm_compute in print_result (infer_model (clauses_of_constraints test_chain)).

(* Eval compute in print_result test''. *) 
Definition chainres :=  (infer_model (clauses_of_constraints test_chain)).



(*Goal hasFiniteModel chainres.
  hnf.
  unfold chainres.
  unfold infer_model.
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
  compute in f.
  hnf in f. simpl in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _). simpl in eq.
  hnf in eq. unfold eq, inspect.
  rewrite loop_clause_1_clause_2_equation_2.
  set (l := loop _ _ _ _ _ _). hnf in l. simpl in l.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. unfold f', inspect.
  simp loop.
  set (f'' := check_model _ _).
  hnf in f''. simpl in f''.
  unfold inspect, f''. simp loop.
  set (eq' := LevelSet.equal _ _).
  hnf in eq'. unfold eq', inspect.
  simp loop.
  set (cm := check_model _ _).
  hnf in cm. simpl in cm.
  unfold inspect, cm. simp loop.
  exact eq_refl.
Qed. *)

(*Goal chainres = Loop.
  unfold chainres.
  unfold infer_model.
  set (levels := Clauses.fold _ _ _).
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
  hnf in f. cbn in f.
  unfold f. unfold inspect.
  simp loop.
  set (eq := LevelSet.equal _ _).
  hnf in eq. unfold eq, inspect.
  simp loop.
  set (f' := check_model _ _).
  hnf in f'. cbn in f'. unfold flip in f'. cbn in f'.

set (f := check_model _ _).
hnf in f. cbn in f.
unfold f. cbn -[forward]. unfold flip.
unfold init_w.
rewrite unfold_forward.
set (f' := check_model _ _).
cbn in f'. unfold flip in f'.
hnf in f'. cbn in f'.
cbn.

unfold check_model. cbn -[forward]. unfold flip.
set (f := update_value _ _). cbn in f.
unfold Nat.leb in f. hnf in f.

Eval compute in print_result (infer_model ex_levels test_clauses).

*)

Definition test_above0 := 
  (add_cstr (levelc + 1) (ConstraintType.Le 0) levelc ConstraintSet.empty).
  
Eval compute in print_clauses (clauses_of_constraints test_above0).
Definition testabove0 := infer_model (clauses_of_constraints test_above0).

Eval vm_compute in print_result testabove0.

(** Verify that no clause holds vacuously for the model *)

Definition premise_holds (m : model) (cl : clause) :=
  satisfiable_premise m (premise cl).

Definition premises_hold (cls : clauses) (m : model) : bool :=
  Clauses.for_all (premise_holds m) cls.

Definition print_model_premises_hold cls (m : model) :=
  if premises_hold cls m then "all premises hold"
  else "some premise doesn't hold".

Definition print_premises_hold {V} (r : result V) :=
  match r with
  | Loop => "looping"
  | Model w m _ => print_model_premises_hold m.(model_clauses) m.(model_model)
  end.

(* Is clause [c] non-vacuous and satisfied by the model? *)
Definition check_clause (m : model) (cl : clause) : bool :=
  satisfiable_premise m (premise cl) && satisfiable_atom m (concl cl).

Definition check_clauses (m : model) cls : bool :=
  Clauses.for_all (check_clause m) cls.

Definition check_cstr (m : model) (c : UnivConstraint.t) :=
  let cls := clauses_of_constraint c in
  check_clauses m cls.

Definition check_cstrs (m : model) (c : ConstraintSet.t) :=
  let cls := clauses_of_constraints c in
  check_clauses m cls.
  
Equations? infer_extension (V : LevelSet.t) (m : valid_model V) (cls : clauses) 
  (prf : LevelSet.Subset (clauses_conclusions cls) V) : result V := 
  | V, m, cls', prf := loop V (Clauses.union m.(model_clauses) cls') m.(model_model) _.
Proof.
  eapply clauses_conclusions_spec in H as [cl []].
  eapply Clauses.union_spec in H as [].
  apply m.(model_clauses_conclusions). 
  rewrite clauses_conclusions_spec. now exists cl.
  eapply prf. rewrite clauses_conclusions_spec.
  now exists cl. 
Qed.

(* We weaken a valid model for V to a model for [W ∪ clauses_levels cls] by 
   setting a minimal value for the new atoms in [clauses_levels cls \ W]
   such that the new clauses [cls] do not hold vacuously.
*)
Equations? weaken_model {V : LevelSet.t} (m : valid_model V) (cls : clauses) : valid_model (LevelSet.union (clauses_levels cls) V) :=
  weaken_model m cls := 
    {| model_clauses := m.(model_clauses); 
       model_model := min_model m.(model_model) cls |}.
Proof.
  rewrite LevelSet.union_spec. right. now apply m.
Qed.

Equations? infer_model_extension {V : LevelSet.t} (m : valid_model V) (cls : clauses) : result (LevelSet.union (clauses_levels cls) V) :=
  infer_model_extension m cls := 
    infer_extension (LevelSet.union (clauses_levels cls) V) (weaken_model m cls) cls _.
Proof.
  eapply LevelSet.union_spec. left.
  now eapply in_conclusions_levels.
Qed.

Definition model_variables (m : model) : LevelSet.t :=
  LevelMap.fold (fun l _ acc => LevelSet.add l acc) m LevelSet.empty.

Variant enforce_result :=
  | Looping
  | ModelExt (m : model).

Definition testp := Eval vm_compute in {| model_values := (LevelMap.empty _) |}.

Definition enforce_clauses {V} (m : valid_model V) cls : option model :=
  match infer_model_extension m cls with
  | Loop => None
  | Model w m _ => Some m.(model_model)
  end.

Definition enforce_clause {V} (m : valid_model V) cl : option model :=
  enforce_clauses m (Clauses.singleton cl).

Definition enforce_cstr {V} (m : valid_model V) (c : UnivConstraint.t) :=
  let cls := clauses_of_constraint c in
  enforce_clauses m cls.

Definition enforce_cstrs {V} (m : valid_model V) (c : ConstraintSet.t) :=
  let cls := clauses_of_constraints c in
  enforce_clauses m cls.

Definition initial_cstrs :=
  (add_cstr (sup levela levelb) Eq (levelc + 1)
  (add_cstr levelc (Le 0) (sup levela levelb)
  (add_cstr levelc (Le 0) levelb
    ConstraintSet.empty))).

Definition enforced_cstrs :=
  (* (add_cstr (sup levela levelb) Eq (sup (levelc + 1) leveld) *)
  (add_cstr (levelb + 10) (Le 0) levele
  (* (add_cstr levelc (Le 0) levelb *)
  ConstraintSet.empty).
  
Definition initial_cls := clauses_of_constraints initial_cstrs.
Definition enforced_cls := clauses_of_constraints enforced_cstrs.
  
Eval vm_compute in init_model initial_cls.

Definition abeqcS :=
  clauses_of_constraints 
    (add_cstr (sup levela levelb) Eq (levelc + 1) ConstraintSet.empty).
  
Eval compute in print_clauses initial_cls.
Eval compute in print_clauses abeqcS.

Definition test'' := infer_model initial_cls.
Definition testabeqS := infer_model abeqcS.

Eval vm_compute in print_result test''.
Eval vm_compute in print_result testabeqS.

Eval vm_compute in print_model_premises_hold initial_cls (init_model initial_cls).

Ltac get_result c :=
  let c' := eval vm_compute in c in 
  match c' with
  | Loop => fail "looping"
  | Model ?w ?m _ => exact m
  end.

Definition model_cstrs' := ltac:(get_result test'').

Eval vm_compute in check_cstrs model_cstrs'.(model_model) initial_cstrs.
(* Here c <= b, in the model b = 0 is minimal, and b's valuation gives 1 *)
Eval vm_compute in print_result (infer_model initial_cls).

(* Here it is still the case, we started with b = 0 but move it to 10 
  due to the b + 10 -> e clause, and reconsider the b -> c clause to move 
  c up *)
Eval vm_compute in 
  option_map valuation_of_model
  (enforce_cstrs model_cstrs' enforced_cstrs).

(* The whole set of constraints has a finite model with c <= b *)

Definition all_clauses := Clauses.union initial_cls enforced_cls.

Eval vm_compute in valuation_of_result (infer_model all_clauses).
Eval vm_compute in
  option_map (is_model all_clauses) (option_of_result (infer_model all_clauses)).
  
(* This is a model? *)
Eval vm_compute in (enforce_cstrs model_cstrs' enforced_cstrs).
Eval vm_compute in print_clauses initial_cls.

Notation "x ≡ y" := (eq_refl : x = y) (at level 70).

(** This is also a model of (the closure of) the initial clauses *)
Check (option_map (is_model initial_cls) (enforce_cstrs model_cstrs' enforced_cstrs)
  ≡ Some true).

(* And a model of the new constraints *)
Check (option_map (is_model enforced_cls) (enforce_cstrs model_cstrs' enforced_cstrs)
   ≡ Some true).

(* All premises hold *)    
Eval vm_compute in 
  option_map (print_model_premises_hold enforced_cls) 
    (enforce_cstrs model_cstrs' enforced_cstrs).
