Require Import BinInt List. Import ListNotations.
From Template Require Import config univ.



(* Prop < Set <= other levels *)
(* Each time a level l is inserted in the graph, the constraint *)
(* Set <= l is added. *)

(* For the moment we recompute the graph each time *)
(* TODO the first component is useless *)
Definition t : Type := LevelSet.t * ConstraintSet.t.

(* TODO use nat where Z is not useful or BinNat *)
Local Open Scope Z.

Definition edge : Set := Level.t * Z * Level.t.

Definition edges_of_constraint (uc : univ_constraint) : list edge
  := let '((l, ct),l') := uc in
     match ct with
     | ConstraintType.Lt => [(l,-1,l')]
     | ConstraintType.Le => [(l,0,l')]
     | ConstraintType.Eq => [(l,0,l'); (l',0,l)]
     end.

Definition init_graph : t :=
  let levels := LevelSet.add Level.prop (LevelSet.add Level.set LevelSet.empty) in
  let constraints := ConstraintSet.add (Level.prop, ConstraintType.Lt, Level.set) ConstraintSet.empty in
  (levels, constraints).

(* The monomorphic levels are > Set while polymorphic ones are >= Set. *)
Definition add_node (l : Level.t) (G : t) : t
  := let levels := LevelSet.add l (fst G) in
     let constraints :=
         match l with
         | Level.lProp | Level.lSet => snd G (* supposed to be yet here *)
         | Level.Var _ => ConstraintSet.add (Level.set, ConstraintType.Le, l) (snd G)
         | Level.Level _ => ConstraintSet.add (Level.set, ConstraintType.Lt, l) (snd G)
         end in
     (levels, constraints).

Definition add_constraint (uc : univ_constraint) (G : t) : t
  := let '((l, ct),l') := uc in
     (* maybe useless if we always add constraints
        in which the universes are declared *)
     let G := add_node l (add_node l' G) in
     let constraints := ConstraintSet.add uc (snd G) in
     (fst G, constraints).

Definition repr (uctx : universe_context) : UContext.t :=
  match uctx with
  | Monomorphic_ctx c => c
  | Polymorphic_ctx c => c
  end.

Definition add_global_constraints (uctx : universe_context) (G : t) : t
  := match uctx with
     | Monomorphic_ctx (inst, cstrs) =>
       let G := List.fold_left (fun s l => add_node l s) inst G in
       ConstraintSet.fold add_constraint cstrs G
     | Polymorphic_ctx _ => G
     end.

Section UGraph.
  Variable (φ : t).

  (* FIXME duplicates *)
  Definition edges : list edge
    := ConstraintSet.fold (fun uc E => edges_of_constraint uc ++ E) (snd φ) [].

  (* The graph *)
  (* For each node we record its predecessos  *)
  Definition pred_graph := LevelMap.t (Level.t * Z).

  Definition Zinfty := (Z.pow 2 6)%Z.  (* FIXME bigger at least *)

  Definition add_node_pred_graph l := LevelMap.add l (Level.Level "nil", Zinfty).

  Definition init_pred_graph : pred_graph :=
    LevelSet.fold add_node_pred_graph (fst φ) (LevelMap.empty _).

  Definition relax (G : pred_graph) (e : edge) : pred_graph :=
    let '((u, w), v) := e in
    match LevelMap.find u G, LevelMap.find v G with
    | Some (_, ud), Some (_, vd)
      => if vd >=? (ud + w) then
          LevelMap.add v (u, ud + w) G
        else G
    | _, _ => G
    end.

  Definition BellmanFord (G : pred_graph) (s : Level.t) : pred_graph :=
    let G' := LevelMap.add s (Level.Level "nil", Z0) G in
    let G' := LevelMap.fold (fun _ _ => fold_left relax edges) G G' in
    G'.

  (* true if there is a negative cycle *)
  Definition detect_negative_cycle (G : pred_graph) : bool
    := existsb (fun '((u,w),v) =>
                  match LevelMap.find u G, LevelMap.find v G with
                  | Some (_, ud), Some (_, vd)
                    => Z.gtb vd (ud + w)
                  | _, _ => false
                  end) edges.

  (* If enforce l1 l2 = Some n, the graph enforce that l2 is at least l1 + n *)
  (* i.e. l1 + n <= l2 *)
  (* If None nothing is enforced by the graph between those two levels *)
  Definition enforce (u v : Level.t) : option Z :=
    let G := BellmanFord init_pred_graph u in
    match LevelMap.find v G with
    | Some (_, vd) => Some (Z.opp vd)
    | None => None
    end.
  Definition check_le_level (l1 l2 : Level.t) : bool :=
    match enforce l1 l2 with
    | Some k => Z.geb k 0
    | None => false
    end.

  Definition check_lt_level (l1 l2 : Level.t) : bool :=
    match enforce l1 l2 with
    | Some k => Z.geb k 1
    | None => false
    end.

  Definition check_eq_level (l1 l2 : Level.t) : bool :=
    check_le_level l1 l2 && check_le_level l2 l1.


  Definition check_constraint (cstr : univ_constraint) :=
    let '(l, d, r) := cstr in
    match d with
    | ConstraintType.Eq => check_eq_level l r
    | ConstraintType.Lt => check_lt_level l r
    | ConstraintType.Le => check_le_level l r
    end.

  Definition check_constraints (cstrs : ConstraintSet.t) :=
    ConstraintSet.for_all check_constraint cstrs.

  Definition check_le_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match e1, e2 with
    | (l1, false), (l2, false)
    | (l1, true), (l2, true) => check_le_level l1 l2
    | (l1, true), (l2, false) => check_lt_level l1 l2
    | (l1, false), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k (-1)
                               | _ => false
                               end
    end.

  Definition check_lt_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match e1, e2 with
    | (l1, false), (l2, false)
    | (l1, true), (l2, true) => check_lt_level l1 l2
    | (l1, true), (l2, false) => match enforce l1 l2 with
                               | Some k => Z.geb k 1 (* Approximation? *)
                               | _ => false
                               end
    | (l1, false), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k 0 (* Approximation ? *)
                               | _ => false
                               end
    end.

  Definition check_eq_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    check_le_level_expr e1 e2 && check_le_level_expr e2 e1.

  Definition exists_bigger_or_eq (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_le_level_expr e1) u2.

  Definition exists_strictly_bigger (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_lt_level_expr e1) u2.

  Definition check_leq `{cf : checker_flags} (u1 u2 : Universe.t) : bool :=
    (negb check_univs) || Universe.for_all (fun e => exists_bigger_or_eq e u2) u1.

  Definition check_lt (u1 u2 : Universe.t) : bool :=
    Universe.for_all (fun e => exists_strictly_bigger e u2) u1.

  (* true is all is ok *)
  Definition no_universe_inconsistency : bool :=
    let G := BellmanFord init_pred_graph Level.prop in
    negb (detect_negative_cycle G).

End UGraph.


(* Section Test. *)

(*   Compute init_graph. *)

(*   Definition G := init_graph. *)

(*   Compute (check_leq G Universe.type0m Universe.type0). *)
(*   Compute (check_lt G Universe.type0m Universe.type0). *)
(*   Compute (check_lt G Universe.type0m Universe.type0m). *)
(*   Compute (check_lt G Universe.type0 Universe.type0m). *)
(*   Compute (check_lt G Universe.type0 Universe.type0). *)
(*   Compute (no_universe_inconsistency G). *)

(*   Definition G' := add_constraint (Level.Level "Top.0", Lt, Level.Level "Top.1") *)
(*                        (add_constraint (Level.Var 0, Lt, Level.Var 1) G). *)

(*   Compute (check_lt G' (Universe.make (Level.Level "Top.0")) (Universe.make (Level.Var 0))). *)
(*   Compute (check_leq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.lProp))). *)
(*   Compute (check_leq G' (Universe.super (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1"))). *)
(*   Compute (check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.super (Level.Level "Top.1"))). *)
(*   Compute (check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1"))). *)


(*   Compute G'. *)
(*   Compute (no_universe_inconsistency G'). *)
(*   Compute (check_lt G' (Universe.make (Level.Var 1)) (Universe.make (Level.Var 0))). *)
(*   Compute (check_leq G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1))). *)
(*   Compute (check_lt G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1))). *)

(*   Compute (check_leq G' Universe.type1 Universe.type0). *)
(*   Compute (check_lt G' Universe.type1 Universe.type1). *)


(*   Definition G'' := add_constraint (Level.Var 1, Lt, Level.Var 2) *)
(*                                   (add_constraint (Level.Var 2, Lt, Level.lSet) G'). *)

(*   Compute (no_universe_inconsistency G''). *)

(* End Test. *)
