(* Distributed under the terms of the MIT license. *)

From Coq Require Import ssreflect ssrbool.
From Coq Require Import Program RelationClasses Morphisms.
From Coq Require Import Orders OrderedTypeAlt OrderedTypeEx MSetList MSetInterface MSetAVL MSetFacts FMapInterface MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Universes.
From Equations Require Import Equations.
Set Equations Transparent.

Import Universes.

Module MoreLevel.
  Import Universes.
  Include Level.

  Definition reflect_eq : ReflectEq t := reflect_level.
  Definition to_string := string_of_level.

End MoreLevel.

Module LevelMap.
  Module OT := FMapOrderedType_from_UsualOrderedType Level.
  Include FMapAVL.Make OT.
End LevelMap.

Module UnivLoopChecking.
  Include LoopChecking MoreLevel LevelSet LevelMap.
End UnivLoopChecking.

Import UnivLoopChecking.

Definition translate_universe (u : LevelAlgExpr.t) : nonEmptyLevelExprSet :=
  let (hd, tl) := Universes.NonEmptySetFacts.to_nonempty_list u in
  NonEmptySetFacts.add_list tl (NonEmptySetFacts.singleton hd).

Definition to_constraint (x : UnivConstraint.t) : constraint :=
  let '(l, d, r) := x in
  let '(l, d, r) := match d with
  | ConstraintType.Eq => (l, UnivEq, r)
  | ConstraintType.Le k => 
    if (k <? 0)%Z then (l, UnivLe, LevelAlgExpr.add (Z.to_nat (- k)) r)
    else (LevelAlgExpr.add (Z.to_nat k) l, UnivLe, r)
  end
  in 
  let l := translate_universe l in
  let r := translate_universe r in
  (l, d, r).

Definition enforce_constraints (cstrs : ConstraintSet.t) : clauses :=
  ConstraintSet.fold (fun cstr acc => enforce_constraint (to_constraint cstr) acc) cstrs Clauses.empty.
  
Declare Scope levelnat_scope.
Delimit Scope levelnat_scope with levelnat.
Module LevelNatMapNotation.
  Import LevelMap.Raw.
  Notation levelmap := (tree nat) (only parsing).
  Definition parse_levelnat_map (l : list Byte.byte) : option levelmap :=
    None.
  Definition print_levelnat_map (m : levelmap) :=
    let list := LevelMap.Raw.elements m in
    print_list (fun '(l, w) => MoreLevel.to_string l ^ " -> " ^ string_of_nat w) nl list.
   
  Definition print_levelmap (l : levelmap) : list Byte.byte :=
    to_bytes (print_levelnat_map l).
   
  String Notation levelmap parse_levelnat_map print_levelmap
      : levelnat_scope.
End LevelNatMapNotation.
Import LevelNatMapNotation.
Arguments LevelMap.Bst {elt} this%levelnat {is_bst}.

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


(* Example from the paper *)  
Definition clause1 : clause := mk_clause levela [levelb] (LevelExpr.succ levelb).  
Definition clause2 : clause := mk_clause levelb [] (LevelExpr.add levelc 3).
Definition clause3 := mk_clause (LevelExpr.add levelc 1) [] leveld.
Definition clause4 := mk_clause levelb [LevelExpr.add leveld 2] levele.
Definition clause5 := mk_clause levele [] levela.

Definition ex_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4].

Definition ex_loop_clauses :=
  ClausesProp.of_list [clause1; clause2; clause3; clause4; clause5].


Example test := infer ex_clauses.
Example test_loop := infer ex_loop_clauses.


Eval compute in print_result test.
Eval compute in print_result test_loop.

(* Testing the unfolding of the loop function "by hand" *)
Definition hasFiniteModel {V U cls m} (m : result V U cls m) :=
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
  unfold infer.
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

Definition add_cstr (x : LevelAlgExpr.t) d (y : LevelAlgExpr.t) cstrs :=
  ConstraintSet.add (x, d, y) cstrs.

Coercion LevelAlgExpr.make : LevelExpr.t >-> LevelAlgExpr.t.
Import ConstraintType.
Definition test_cstrs :=
  (add_cstr levela Eq (LevelExpr.add levelb 1)
  (add_cstr (LevelAlgExpr.sup levela levelc) Eq (LevelExpr.add levelb 1)
  (add_cstr levelb (ConstraintType.Le 0) levela
  (add_cstr levelc (ConstraintType.Le 0) levelb
    ConstraintSet.empty)))).

Definition test_clauses := clauses_of_constraints test_cstrs.

Definition test_levels : LevelSet.t := 
  LevelSetProp.of_list (List.map (LevelExpr.get_level) [levela; levelb; levelc]).

Eval compute in print_clauses test_clauses.

Definition test' := infer test_clauses.
Eval compute in print_result test'.
Import LevelAlgExpr (sup).

Definition test_levels' : LevelSet.t := 
  LevelSetProp.of_list (List.map (LevelExpr.get_level) 
    [levela; levelb;
      levelc; leveld]).

Notation " x + n " := (LevelExpr.add x n).

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
Time Eval vm_compute in print_result (infer (clauses_of_constraints test_chain)).

(* Eval compute in print_result test''. *) 
Definition chainres :=  (infer (clauses_of_constraints test_chain)).



(*Goal hasFiniteModel chainres.
  hnf.
  unfold chainres.
  unfold infer.
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
  unfold infer.
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

Eval compute in print_result (infer ex_levels test_clauses).

*)

Definition test_above0 := 
  (add_cstr (levelc + 1) (ConstraintType.Le 0) levelc ConstraintSet.empty).
  
Eval compute in print_clauses (clauses_of_constraints test_above0).
Definition testabove0 := infer (clauses_of_constraints test_above0).

Eval vm_compute in print_result testabove0.

(** Verify that no clause holds vacuously for the model *)

Definition premise_holds (m : model) (cl : clause) :=
  satisfiable_premise m (premise cl).

Definition premises_hold (cls : clauses) (m : model) : bool :=
  Clauses.for_all (premise_holds m) cls.

Definition print_model_premises_hold cls (m : model) :=
  if premises_hold cls m then "all premises hold"
  else "some premise doesn't hold".

Definition print_premises_hold {V U cls m} (r : result V U cls m) :=
  match r with
  | Loop => "looping"
  | Model w m _ => print_model_premises_hold cls m.(model_model)
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
  
  (* as [cl []].
  eapply Clauses.union_spec in H as [].
  apply m.(model_clauses_conclusions). 
  rewrite clauses_conclusions_spec. now exists cl.
  eapply prf. rewrite clauses_conclusions_spec.
  now exists cl. 
Qed. *)

(*Equations? weaken_model (m : model) (cls : clauses) : valid_model (LevelSet.union (clauses_levels cls) V m cls) :=
  weaken_model m cls := 
    {| model_clauses := m.(model_clauses); 
       model_model :=  |}.
Proof.
  rewrite LevelSet.union_spec. right. now apply m.
Qed. *)

Definition model_variables (m : model) : LevelSet.t :=
  LevelMap.fold (fun l _ acc => LevelSet.add l acc) m LevelSet.empty.

Variant enforce_result :=
  | Looping
  | ModelExt (m : model).

Definition enforce_cstr {V init cls} (m : valid_model V init cls) (c : UnivConstraint.t) :=
  let cls := clauses_of_constraint c in
  enforce_clauses m cls.

Definition enforce_cstrs {V init cls} (m : valid_model V init cls) (c : ConstraintSet.t) :=
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

Definition test'' := infer initial_cls.
Definition testabeqS := infer abeqcS.

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
Eval vm_compute in print_result (infer initial_cls).

(* Here it is still the case, we started with b = 0 but move it to 10 
  due to the b + 10 -> e clause, and reconsider the b -> c clause to move 
  c up *)
Eval vm_compute in 
  option_map valuation_of_model
  (enforce_cstrs model_cstrs' enforced_cstrs).

(* The whole set of constraints has a finite model with c <= b *)

Definition all_clauses := Clauses.union initial_cls enforced_cls.

Eval vm_compute in valuation_of_result (infer all_clauses).
Eval vm_compute in
  option_map (is_model all_clauses) (option_of_result (infer all_clauses)).
  
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
