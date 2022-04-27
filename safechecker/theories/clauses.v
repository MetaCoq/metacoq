From Coq Require Import Program RelationClasses Morphisms.
From Coq Require Import OrderedTypeAlt OrderedTypeEx MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils Universes.
From Equations Require Import Equations.

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

Definition satisfiable_atom (m : model) (atom : Level.t * nat) : bool :=
  let '(l, k) := atom in
  match LevelMap.find l m with
  | Some val => k <=? val
  | None => false
  end.
  
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

Definition satisfiable_premise (m : model) (l : nonEmptyLevelExprSet) :=
  LevelExprSet.exists_ (satisfiable_atom m) l.

Definition valid_clause (m : model) (cl : clause) :=
  implb (satisfiable_premise m (premise cl)) (satisfiable_atom m (concl cl)).

Definition is_model (cls : clauses) (m : model) : bool :=
  Clauses.for_all (valid_clause m) cls.

Definition update_map l k v :=
  match LevelMap.find l v with
  | Some k' => LevelMap.add l (Nat.max k k') v
  | None => LevelMap.add l k v
  end. 

Definition update_value (wv : LevelSet.t × model) (cl : clause) : option (LevelSet.t × model) :=
  let (w, v) := wv in
  let k0 := min_premise v (premise cl) in
  (* cl holds vacuously as the premise doesn't hold *)
  if (k0 <? 0)%Z then None
  else 
    (* The premise does hold *)
    let (l, k) := concl cl in
    (* Does the conclusion also hold ? *)
    if k + Z.to_nat k0 <=? level_value v l then None
    else 
      (* The conclusion doesn't hold, we need to set it higher *)
      (* let (w, v) := cur in *)
      Some (LevelSet.add l w, update_map l (k + Z.to_nat k0) v).

Definition check_model (cls : clauses) (wv : LevelSet.t × model) : 
    option (LevelSet.t × model) :=
  Clauses.fold
    (fun cl acc => 
      let cur := match acc with None => wv | Some acc => acc end in
      match update_value cur cl with 
      | Some acc => Some acc
      | None => acc
      end)
    cls None.

Inductive result :=
  | Loop
  | Unsatisfiable (w : LevelSet.t) (m : model)
  | Model (w : LevelSet.t) (m : model).

#[bypass_check(guard)]
Fixpoint forward (V : LevelSet.t) (cls : clauses) (m : model) (w : LevelSet.t) { struct w } : result :=
  match check_model cls (w,m) with
  | None => 
    if is_model cls m then Model w m
    else Unsatisfiable w m
  | Some (w', v') => 
    if LevelSet.equal w' V then Loop
    else forward V cls v' w'
  end.

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

Definition clause1 : clause := 
  mk_clause levela [levelb] (LevelExpr.succ levelb).

Definition levelexpr_add (x : LevelExpr.t) (n : nat) : LevelExpr.t :=
  let (l, k) := x in (l, k + n).

Definition clause2 : clause := mk_clause levelb [] (levelexpr_add levelc 3).
Definition clause3 := mk_clause (levelexpr_add levelc 1) [] leveld.
Definition clause4 := mk_clause levelb [levelexpr_add leveld 2] levele.
Definition clause5 := mk_clause levele [] levela.

Definition ex_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4].

Definition ex_loop_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4; clause5].
  
Definition init_model (levels : LevelSet.t) : model :=
  LevelSet.fold (fun l acc => LevelMap.add l 0 acc) levels (LevelMap.empty _).

Definition init_w (levels : LevelSet.t) : LevelSet.t := LevelSet.empty.

Example test := forward ex_levels ex_clauses (init_model ex_levels) (init_w ex_levels).
Example test_loop := forward ex_levels ex_loop_clauses (init_model ex_levels) (init_w ex_levels).

Eval compute in test.

Definition print_model (m : model) :=
  let list := LevelMap.elements m in
  print_list (fun '(l, w) => string_of_level l ^ " -> " ^ string_of_nat w) nl list.

Definition print_wset (l : LevelSet.t) :=
  let list := LevelSet.elements l in
  print_list string_of_level " " list.

Definition print_result (m : result) :=
  match m with
  | Loop => "looping"
  | Model w m => "satisfiable with model: " ^ print_model m ^ nl ^ " W = " ^
    print_wset w
  | Unsatisfiable w m => "Unsatisfiable with model: " ^ print_model m ^ " W = " ^ print_wset w
  end.
  
Eval compute in print_result test.
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

Definition clauses_of_constraints (cstrs : UnivConstraintSet.t) : clauses :=
  UnivConstraintSet.fold (fun cstr acc => Clauses.union (clauses_of_constraint cstr) acc) cstrs Clauses.empty.

Definition print_premise (l : LevelAlgExpr.t) : string :=
  let (e, exprs) := LevelAlgExpr.exprs l in
  string_of_level_expr e ^
  match exprs with
  | [] => "" 
  | l => " \/ " ^ print_list string_of_level_expr " \/ " exprs 
  end.

Definition print_clauses (cls : clauses) :=
  let list := Clauses.elements cls in
  print_list (fun '(l, r) => 
    print_premise l ^ " -> " ^ string_of_level_expr r) nl list.
