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

End MoreLevel.

Module LevelOT := OrderedType_from_Alt MoreLevel.
Module LevelMap := FMapAVL.Make LevelOT.
Module LevelMapFact := FMapFacts.WProperties LevelMap.

Definition model := LevelMap.t nat.

Definition premise (cl : clause) := fst cl.

Definition concl (cl : clause) := snd cl.

Definition matches_clause (cl : clause) (m : model) :=
  LevelExprSet.exists_ (fun '(l, k) => LevelMap.find l m == Some k) (premise cl).

Definition update_model (m : model) (w : LevelSet.t) (e : LevelExpr.t) : 
  option (LevelSet.t * model) :=
  let (l, k) := e in
  match LevelMap.find l m with
  | Some k' => if k' <? k then Some (LevelSet.add l w, LevelMap.add l k m) else None
  | None => None
  end.

Definition new_atoms (cls : clauses) (m : model) (w : LevelSet.t) : option (LevelSet.t * model) :=
  Clauses.fold
    (fun cl acc => 
      if matches_clause cl m then 
        match update_model m w (concl cl) with
        | Some v' => Some v'
        | None => acc
        end
      else acc)
    cls None.

(* Variant model_check :=
  | Satisfiable
  | Unsatisfiable (cls : clauses). *)
  
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

Definition valid_clause (m : model) (cl : clause) :=
  implb (satisfiable_premise m (premise cl)) (satisfiable_atom m (concl cl)).

Definition is_model (cls : clauses) (m : model) : bool :=
  Clauses.for_all (valid_clause m) cls.

Inductive update_result := 
  | VacuouslyTrue
  | Holds
  | DoesntHold (wm : LevelSet.t × model).

Definition update_value (wv : LevelSet.t × model) (cl : clause) : update_result :=
  let (w, v) := wv in
  let k0 := min_premise v (premise cl) in
  (* cl holds vacuously as the premise doesn't hold *)
  if (k0 <? 0)%Z then VacuouslyTrue
  else 
    (* The premise does hold *)
    let (l, k) := concl cl in
    (* Does the conclusion also hold ? *)
    if k + Z.to_nat k0 <=? level_value v l then Holds
    else 
      (* The conclusion doesn't hold, we need to set it higher *)
      DoesntHold (LevelSet.add l w, LevelMap.add l (k + Z.to_nat k0) v).

Definition check_model (cls : clauses) (wv : LevelSet.t × model) : 
    option (LevelSet.t × model) :=
  Clauses.fold
    (fun cl acc => 
      let cur := match acc with None => wv | Some acc => acc end in
      match update_value cur cl with 
      | VacuouslyTrue => acc
      | DoesntHold acc => Some acc
      | Holds => acc
      end)
    cls None.

Definition strict_subset (s s' : LevelSet.t) :=
  LevelSet.Subset s s' /\ ~ LevelSet.Equal s s'.

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

Lemma check_model_subset {cls w v} : 
  forall w' v', check_model cls (w, v) = Some (w', v') -> LevelSet.Subset w w'.
Proof.
  intros w' v'.
  unfold check_model. revert w' v'.
  eapply ClausesProp.fold_rec => //.
  intros x a s' s'' hin nin hadd IH.
  intros w' v'. destruct a.
  - destruct p as []. specialize (IH _ _ eq_refl).
    unfold update_value.
    destruct Z.ltb. intros [= -> ->] => //.
    destruct x as [prem [l k]]; cbn.
    destruct Nat.leb.
    intros [= -> ->] => //.
    intros [= <- <-]. intros x inx.
    eapply LevelSet.add_spec. now right.
  - unfold update_value.
    destruct Z.ltb. intros => //.
    destruct x as [prem [l k]]; cbn.
    destruct Nat.leb => //.
    intros [= <- <-].
    intros x inx. eapply LevelSet.add_spec. now right.
Qed.

Definition restrict_clauses (cls : clauses) (W : LevelSet.t) :=
  Clauses.filter (fun '(prem, concla) =>
    LevelSet.subset (LevelExprSet.levels prem) W &&
    LevelSet.mem (LevelExpr.get_level concla) W) cls.

Definition clauses_with_concl (cls : clauses) (concl : LevelSet.t) :=
  Clauses.filter (fun '(prem, concla) => LevelSet.mem (LevelExpr.get_level concla) concl) cls.

Lemma in_clauses_with_concl (cls : clauses) (concl : LevelSet.t) cl :
  Clauses.In cl (clauses_with_concl cls concl) -> LevelSet.In (LevelExpr.get_level cl.2) concl.
Proof.
  unfold clauses_with_concl.
  move/Clauses.filter_spec => [].
  destruct cl. intros hin. move/LevelSet.mem_spec.
  now cbn.
Qed.

Definition clauses_conclusions (cls : clauses) : LevelSet.t :=
  Clauses.fold (fun cl acc => LevelSet.add (LevelExpr.get_level cl.2) acc) cls LevelSet.empty.
  
Lemma clauses_conclusions_clauses_with_concl cls concl : 
  LevelSet.Subset (clauses_conclusions (clauses_with_concl cls concl)) concl.
Proof.
  unfold clauses_conclusions, clauses_with_concl. 
  intros x.
  eapply ClausesProp.fold_rec; clear.
  - move=> s' he /LevelSet.empty_spec //.
  - move=> cl ls cls' cls'' hin hnin hadd ih.
    move/LevelSet.add_spec. intros [->|].
    eapply Clauses.filter_spec in hin. 2:tc.
    destruct hin. destruct cl as [prem [l k]]; cbn in *.
    now eapply LevelSet.mem_spec in H0.
    eauto.
Qed.

Lemma clauses_conclusions_restrict_clauses cls W : 
  LevelSet.Subset (clauses_conclusions (restrict_clauses cls W)) W.
Proof.
  unfold clauses_conclusions, restrict_clauses.
  intros x.
  eapply ClausesProp.fold_rec; clear.
  - move=> s' he /LevelSet.empty_spec //.
  - move=> cl ls cls' cls'' hin hnin hadd ih.
    move/LevelSet.add_spec. intros [->|].
    eapply Clauses.filter_spec in hin. 2:tc.
    destruct hin. destruct cl as [prem [l k]]; cbn in *.
    now move/andP: H0 => [] /LevelSet.subset_spec Hs /LevelSet.mem_spec hi.
    eauto.
Qed.

Definition in_clauses_conclusions (cls : clauses) (x : Level.t): Prop :=
  exists cl, Clauses.In cl cls /\ (LevelExpr.get_level cl.2) = x.
  
Lemma check_model_subset_clauses cls w m : 
  forall w' m', check_model cls (w, m) = Some (w', m') -> 
  LevelSet.Subset w w' /\ LevelSet.Subset w' (LevelSet.union w (clauses_conclusions cls)).
Proof.
  intros w' v' cm. split; [now eapply check_model_subset|].
  move: cm.
  unfold check_model. revert w' v'.
  unfold clauses_conclusions.
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
Qed.

Inductive result (cls : clauses) (V : LevelSet.t) :=
  | Loop
  | Model (w : LevelSet.t) (m : model) (prf : LevelSet.subset w V) (ism : check_model cls (w, m) = None).
Arguments Loop {cls} {V}.
Arguments Model {cls} {V}.
Arguments exist {A P}.  
Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.
Arguments lexprod {A B}.

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

(* Lemma check_model_none {cls w m} : check_model (restrict_clauses cls w) m = None ->
  Clauses.For_all (fun cl => update_value m cl = None) (restrict_clauses cls m)  *)
(* check_model cls (w', m) = Some (w'', m') -> strict_subset w w''. *)

(** Some correctness lemma like this will be needed: 
  If (w', m) is a model for (restrict_clauses cls w) but not for cls, 
  then the "w''" set must be strictly larger than "w'" as there must be a clause
  in `cls / restrict_clauses cls w` that triggered a DoesntHold and an update of 
  its conclusion atom, which by definition cannot be in `w`.
*)
Lemma check_model_extend_strict_subset {cls m w w' w'' m'} : check_model (restrict_clauses cls w) (w', m) = None -> check_model cls (w', m) = Some (w'', m') -> strict_subset w w''.
Proof.
  unfold check_model, restrict_clauses.
  set (f := fun cl acc => _).
  assert (transpose eq f).
  { intros x y acc. unfold f.
    set (acc' := match acc with | Some acc0 => acc0 | None => (w', m) end).
    destruct (update_value acc' y) eqn:updy.
    destruct (update_value acc' x) eqn:updx.
    fold acc'. rewrite updy updx //.
    fold acc'. rewrite updy updx //.
    fold acc'. rewrite updx.
    admit. }
    
  rewrite clauses_fold_filter.
  revert w'' m'.
  eapply (ClausesProp.fold_rel (R:= fun x y => forall w'' m', x = None -> y = Some (w'', m') -> strict_subset w w'')) => //.
  intros.
  destruct x as [prem concla].
  cbn in *. subst f. cbn in H3.
  destruct (_ && _) eqn:cond.
  destruct a. destruct b. destruct (update_value p _) => //.
  destruct (update_value p _) => //.
  destruct (update_value (w', m) _) eqn:upd => //.
  destruct b as [[]|].
  destruct (update_value (t, m0) _) eqn:upd' => //. noconf H3.
  eapply H1; trea. noconf H3.
  eapply H1; trea. noconf H3.
  
Admitted.

Lemma check_model_extend_strict_subset' {cls m w w' w'' m'} : check_model (clauses_with_concl cls w) (w', m) = None -> check_model cls (w', m) = Some (w'', m') -> strict_subset w w''.
Proof. Admitted.

Lemma strict_subset_incl (x y z : LevelSet.t) : LevelSet.Subset x y -> strict_subset y z -> strict_subset x z.
Proof.
  intros hs []. split => //. lsets.
  intros heq. apply H0. lsets.
Qed.

Definition lexprod_rel := lexprod lt lt.

#[local] Instance lexprod_rel_wf : WellFounded lexprod_rel.
Proof.
  eapply (Acc_intro_generator 1000). unfold lexprod_rel. eapply wf_lexprod, lt_wf. eapply lt_wf.
Defined.

Opaque lexprod_rel_wf.

Equations? loop (V : LevelSet.t) (W : LevelSet.t) (cls : clauses) (m : model) (w : LevelSet.t) 
  (prf : LevelSet.Subset w W /\ LevelSet.Subset W V /\ LevelSet.Subset (clauses_conclusions cls) W) : result cls V
  by wf (LevelSet.cardinal V, LevelSet.cardinal V - LevelSet.cardinal w) (lexprod lt lt) :=
  loop V W cls m w prf with inspect (check_model cls (w,m)) :=
    | exist None eqm => Model w m _ eqm
    | exist (Some (w', m')) eqm with inspect (LevelSet.equal w' W) := {
      | exist true eq := Loop
      | exist false neq with loop w' w' (restrict_clauses cls w') m' w' _ := { (* Here w' < V *)
        | Loop := Loop
        | Model w'' m'' hsub ism with inspect (check_model cls (w'', m'')) :=
          { | exist None eqm' => Model w'' m'' _ eqm'
            | exist (Some (w''', m''')) eqm' with inspect (LevelSet.equal w''' w'') := {
              | exist true _ := Loop
              | exist false neq' := loop V V cls m''' w''' _ } (* Here V - w''' < V *)
          }
      }
    }.
Proof.
  all:clear loop.
  all:intuition auto.
  - reflexivity.
  - eapply check_model_subset_clauses in eqm as [sww' sw'wcl]; lsets.
  - 
  (* exact (clauses_conclusions_clauses_with_concl cls w'). *)
    exact (clauses_conclusions_restrict_clauses cls w').
  - assert (~ LevelSet.Equal w' W).
    { intros heq % LevelSet.equal_spec. congruence. } clear neq.
    eapply check_model_subset_clauses in eqm as []. cbn. 
    constructor. 
    eapply strict_subset_cardinal. split => //. lsets.
    intros heq. apply H2. intros l. split. intros. lsets. lsets.
  - eapply check_model_subset_clauses in eqm as [ww' w'wcl].
    eapply check_model_subset_clauses in eqm' as [w''w''' w'''w'cl].
    eapply LevelSet.subset_spec in hsub. lsets.
  - reflexivity.
  - lsets.
  - eapply LevelSet.subset_spec in hsub.
    assert (strict_subset w' w''').
    { exact (check_model_extend_strict_subset ism eqm'). }
    eapply check_model_subset_clauses in eqm as [ww' w'wcl].
    eapply check_model_subset_clauses in eqm' as [w''w''' w'''w'cl].
    constructor 2.
    enough (LevelSet.cardinal w < LevelSet.cardinal w'''). 
    { assert (LevelSet.cardinal w <= LevelSet.cardinal V).
      { eapply LevelSetProp.subset_cardinal. lsets. }
      assert (LevelSet.cardinal w''' <= LevelSet.cardinal V).
      { eapply LevelSetProp.subset_cardinal. lsets. }
      lia. }
    eapply strict_subset_cardinal. eapply strict_subset_incl; tea.
  - eapply LevelSet.subset_spec in hsub. eapply LevelSet.subset_spec.
    eapply check_model_subset_clauses in eqm as [ww' w'wcl].
    lsets.
  - eapply LevelSet.subset_spec. lsets.
Qed.
Transparent lexprod_rel_wf.

Definition init_model (levels : LevelSet.t) : model :=
  LevelSet.fold (fun l acc => LevelMap.add l 0 acc) levels (LevelMap.empty _).

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.

Equations? check (V : LevelSet.t) (cls : clauses)  (prf : LevelSet.Subset (clauses_conclusions cls) V) : result cls V  := 
  check V cls prf := loop V V cls (init_model V) LevelSet.empty _.
Proof.
  repeat split => //.
  intros x hin. now eapply LevelSet.empty_spec in hin.
Qed.
  
Definition clauses_levels (cls : clauses) : LevelSet.t := 
  Clauses.fold (fun '(cl, concl) acc => 
  LevelSet.union (LevelExprSet.levels cl)
    (LevelSet.add concl.1 acc)) cls LevelSet.empty.

Equations? check_clauses (clauses : clauses) : result clauses (clauses_levels clauses) :=
  check_clauses clauses := check (clauses_levels clauses) clauses _.
Proof.
  revert a H.
  unfold clauses_levels. unfold clauses_conclusions.
  eapply (ClausesProp.fold_rel (R := fun x y => forall a, LevelSet.In a x -> LevelSet.In a y)) => //.
  intros x l l' hin hsub x' hix'.
  destruct x as [prem [l'' k]]. cbn in *. 
  eapply LevelSet.union_spec. right.
  eapply LevelSet.add_spec. 
  specialize (hsub x'). lsets.
Qed.

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


Example test := check_clauses ex_clauses.
Example test_loop := check_clauses ex_loop_clauses.

Definition print_model (m : model) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => string_of_level l ^ " -> " ^ string_of_nat w) nl list.

Definition print_wset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list string_of_level " " list.

Definition valuation_of_model (m : model) : model :=
  let max := LevelMap.fold (fun l k acc => Nat.max k acc) m 0 in
  let valuation := LevelMap.fold (fun l k acc => LevelMap.add l (max - k) acc) m (LevelMap.empty _) in
  valuation.
  
Definition print_result {cls V} (m : result cls V) :=
  match m with
  | Loop => "looping"
  | Model w m _ _ => "satisfiable with model: " ^ print_model m ^ nl ^ " W = " ^
    print_wset w 
    ^ nl ^ "valuation: " ^ print_model (valuation_of_model m)
  end.

Eval compute in print_result test.
Eval compute in print_result test_loop.


(* Testing the unfolding of the loop function "by hand" *)
Definition hasFiniteModel {cls V} (m : result cls V) :=
  match m with
  | Loop => false
  | Model _ _ _ _ => true
  end.

Ltac hnf_eq_left := 
  match goal with
  | |- ?x = ?y => let x' := eval hnf in x in change (x' = y)
  end.

(* Goal hasFiniteModel test.
  hnf. hnf_eq_left. exact eq_refl.
  unfold test.
  unfold check_clauses.
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
  | l => " ∨ " ^ print_list string_of_level_expr " ∨ " exprs 
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

Definition test' := check_clauses test_clauses.
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
    add_cstr hd (Le 1) hd' (chain tl)
  end.

Definition levels_to_n n := 
  unfold n (fun i => (Level.Level (string_of_nat i), 0)).

Definition test_chain := chain (levels_to_n 3).

Eval compute in print_clauses  (clauses_of_constraints test_chain).

(** There is a bug in our loop, these constraints do have a finite model *)
Time Eval compute in print_result (check_clauses (clauses_of_constraints test_chain)).

  
(* Eval compute in print_result test''. *) 
Definition chainres :=  (check_clauses (clauses_of_constraints test_chain)).
Goal hasFiniteModel chainres.
  hnf.
  unfold chainres.
  unfold check_clauses.
  rewrite /check.
  simp loop.
  set (f := check_model _ _).
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
  unfold check_clauses.
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

Eval compute in print_result (check_clauses ex_levels test_clauses).

*)

Definition test_cstrs' :=
  (add_cstr (sup levela levelb) Eq (sup (levelc + 1) leveld)
  (add_cstr (sup levela levelb) Eq (levelc + 1)
  (add_cstr levelc (Le 0) (sup levela levelb)
  (* (add_cstr (levelc + 1) (ConstraintType.Le 0) levelc  *)
  (add_cstr levelc (Le 1) leveld
  (add_cstr levelc (Le 0) levelb
    ConstraintSet.empty))))).

Eval compute in print_clauses  (clauses_of_constraints test_cstrs').

Definition test'' := check_clauses (clauses_of_constraints test_cstrs').
