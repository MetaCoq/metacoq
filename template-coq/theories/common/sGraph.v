From Coq Require Import MSetList MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils config wGraph Universes.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Module SortFamilySet := MSetList.MakeWithLeibniz SortFamily.
Module SortFamilySetFact := WFactsOn SortFamily SortFamilySet.
Module SortFamilySetProp := WPropertiesOn SortFamily SortFamilySet.
(*
Module wGraphExt (V : UsualOrderedTypeWithLeibniz) (VSet : MSetList.SWithLeibniz with Module E := V).
  Include WeightedGraph V VSet.
  Section simplify_paths.
    Context (G : t).

    Definition sub_simple_path {s x y z} (q : SimplePaths G s y z)
      (H : VSet.mem x (snodes G q) = true): exists s', ∥ SimplePaths G s' x z ∥.
      induction q.
      - cbn in H. rewrite<- VSetFact.mem_iff, VSetFact.empty_iff in H. inversion H.
      - cbn in H. rewrite<- VSetFact.mem_iff, VSetFact.add_iff in H. destruct H.
        + exists s'. constructor. rewrite<- H. apply (spaths_step G s0 s' x0 y z); try assumption.
        + rewrite<- VSetFact.mem_iff in IHq. apply (IHq H).
    Defined.

    Definition simplify_paths {x y} (q : Paths G x y) : exists s, ∥ SimplePaths G s x y ∥.
      induction q.
      - exists VSet.empty. constructor. unfold nodes. apply spaths_refl.
      - destruct IHq as (s, H); destruct H. set b:= (VSet.mem x (snodes G X)).
        assert (VSet.mem x (snodes G X) = b). reflexivity. clearbody b. destruct b.
        + apply (sub_simple_path X H).
        + exists (VSet.add x (snodes G X)). constructor.
          apply (spaths_step G (snodes G X) _ x y z); try assumption. rewrite<- VSetFact.not_mem_iff in H.
          apply (DisjointAdd_add2 H). exact (reduce G X).
    Defined.
  End simplify_paths.
  
End wGraphExt.
*)
Module Import sGraph := WeightedGraph SortFamily SortFamilySet.

Definition add_sorts : SortConstraint.t -> SortFamilySet.t -> SortFamilySet.t :=
  fun c s => SortFamilySet.add c.2 (SortFamilySet.add c.1 s).

Lemma add_sorts_correct (constraint: SortConstraint.t) (sorts: SortFamilySet.t) :
  forall s, SortFamilySet.In s (add_sorts constraint sorts) <->
    s = constraint.1 \/ s = constraint.2 \/ SortFamilySet.In s sorts.
Proof.
  intro s. split; intro H.
  - unfold add_sorts in H.
    apply SortFamilySet.add_spec in H. destruct H; [right;left;assumption|].
    apply SortFamilySet.add_spec in H. destruct H; [left;assumption| right;right;assumption].
  - apply SortFamilySet.add_spec. destruct H.
    + right. apply SortFamilySet.add_spec. left; assumption.
    + destruct H; [left; assumption|]. right; apply SortFamilySet.add_spec; right; assumption.
Qed.

Lemma add_sorts_compat : (Proper ((eq * eq) ==> SortFamilySet.Equal ==> SortFamilySet.Equal)) add_sorts.
Proof.
  now intros [][] [[=->][=->]] x0 y0 [=->]%SortFamilySet.eq_leibniz.
Defined.

Lemma add_sorts_trans: transpose SortFamilySet.Equal add_sorts.
Proof.
  intros x y z. unfold add_sorts.
  rewrite (SortFamilySetProp.add_add _ x.1 y.2).
  rewrite (SortFamilySetProp.add_add z x.1 y.1).
  rewrite (SortFamilySetProp.add_add _ x.2 y.2).
  rewrite (SortFamilySetProp.add_add _ x.2 y.1).
  reflexivity.
Qed.

Definition fold_add_edges := SortConstraintSetProp.fold_add SortFamilySet.eq_equiv add_sorts_compat add_sorts_trans.

Definition constraints_to_set : SortConstraintSet.t -> SortFamilySet.t :=
  fun constraints => SortConstraintSet.fold add_sorts
    constraints (SortFamilySet.singleton SortFamily.sfType).

Lemma constraints_to_set_correct (constraints: SortConstraintSet.t) (s: SortFamily.t):
  SortFamilySet.In s (constraints_to_set constraints) <->
  s = SortFamily.sfType \/ 
  (exists constraint, SortConstraintSet.In constraint constraints /\ 
    (s = constraint.1 \/ s = constraint.2)).
Proof.
  revert constraints.
  apply SortConstraintSetProp.set_induction.
  - intros s0 [=->]%SortConstraintSetProp.empty_is_empty_1%SortConstraintSet.eq_leibniz.
    split; [intro H|move=> [->|[constraint [H]]]]; unfold constraints_to_set in *.
    + rewrite (SortConstraintSetProp.fold_empty) in H.
      now inversion H.
    + rewrite SortConstraintSetProp.fold_empty. now apply SortFamilySet.singleton_spec.
    + inversion H.
  - intros s1 s2 H x I H0. apply SortConstraintSetProp.Add_Equal in H0.
    rewrite (SortConstraintSet.eq_leibniz H0). unfold constraints_to_set in *.
    split; [intro H1|intros [->|[constraint [H1 H2]]]].
    + apply fold_add_edges in H1; try assumption.
      apply SortFamilySet.add_spec in H1 as [->|H1].
      * right. exists x. now split; [apply SortConstraintSet.add_spec;left|right].
      * apply SortFamilySet.add_spec in H1 as [->|H1].
      -- right. exists x. now split; [apply SortConstraintSet.add_spec;left|left].
      -- apply H in H1 as [->|[constraint [H1 H2]]]; [left; reflexivity|].
        right; exists constraint; (split; [apply SortConstraintSet.add_spec;now right|]). assumption.
    + apply fold_add_edges; try assumption.
      apply add_sorts_correct. right;right. apply H. now left.
    + apply fold_add_edges; try assumption.
      apply add_sorts_correct. apply SortConstraintSet.add_spec in H1 as [[[=<-][=<-]]|H1]; [rewrite<- or_assoc; left; apply H2|].
      right;right. apply<- H. right. exists constraint. now split.
Qed.

Definition to_edge (constraint: SortConstraint.t) := (constraint.1, 1%Z, constraint.2).

Notation "c .to_edge" := (to_edge c) (at level 3, format "c '.to_edge'").

Definition add_edge : SortConstraint.t -> EdgeSet.t -> EdgeSet.t :=
  (fun c s => EdgeSet.add c.to_edge s).

Lemma add_edge_compat : Proper (eq * eq ==> EdgeSet.eq ==> EdgeSet.eq) add_edge.
Proof.
  now intros [] [] [[=->][=->]] x0 y0 [=->]%EdgeSet.eq_leibniz.
Qed.

Lemma add_edge_trans : (SetoidList.transpose EdgeSet.eq add_edge).
Proof.
  now intros x0 y0 z0; unfold add_edge; rewrite EdgeSetProp.add_add.
Qed.

Lemma add_edge_correct c s : forall e, EdgeSet.In e (add_edge c s) <->
  e = c.to_edge \/ EdgeSet.In e s.
Proof.
  unfold add_edge. apply EdgeSet.add_spec.
Qed.

Definition to_edges (constraints: SortConstraintSet.t) :=
  SortConstraintSet.fold add_edge constraints EdgeSet.empty.

Lemma to_edges_correct constraints: forall c, SortConstraintSet.In c constraints <->
  EdgeSet.In c.to_edge (to_edges constraints).
Proof.
  revert constraints.
  induction constraints using SortConstraintSetProp.set_induction.
  - apply SortConstraintSetProp.empty_is_empty_1 in H.
    split; [intros H0%H|intro H0].
    + inversion H0.
    + unfold to_edges in H0. rewrite (SortConstraintSet.eq_leibniz H) in H0.
      rewrite SortConstraintSetProp.fold_empty in H0. inversion H0.
  - apply (SortConstraintSetProp.Add_Equal) in H0.
    rewrite (SortConstraintSet.eq_leibniz H0).
    split; intro H1; unfold to_edges in *.
    + rewrite (SortConstraintSetProp.fold_add EdgeSet.eq_equiv _ _); [|exact add_edge_compat|exact add_edge_trans|assumption].
      apply EdgeSet.add_spec. now apply SortConstraintSet.add_spec in H1 as [[[=H2][=H4]]|H2];
      [left; unfold to_edge; rewrite H2; rewrite H4|right; apply IHconstraints1].
    + apply SortConstraintSet.add_spec.
      apply (SortConstraintSetProp.fold_add EdgeSet.eq_equiv add_edge_compat add_edge_trans) in H1; try assumption.
      apply EdgeSet.add_spec in H1. destruct H1; [left; inversion H1; constructor; assumption|].
      right. apply IHconstraints1. assumption.
Qed.

(*
Definition add_constraint : SortConstraint.t -> sGraph.t -> sGraph.t :=
  fun constraint graph =>
    if SortFamily.eq_dec constraint.1 constraint.2
    then graph else add_edge graph constraint.to_edge.

Lemma add_constraint_correct c G : forall e,
  sGraph.EdgeSet.In e (sGraph.E (add_constraint c G)) <->
  (e = c.to_edge /\ c.1 <> c.2) \/ sGraph.EdgeSet.In e (sGraph.E G).
Proof.
  split; intro.
  - unfold add_constraint in H. destruct (sGraph.VSetDecide.F.eq_dec c.1 c.2); cbn in H; [right;assumption|].
    destruct (EdgeSet.add_spec (sGraph.E G) c.to_edge e). destruct (H0 H); [left; split; assumption| right; assumption].
  - unfold add_constraint. destruct (sGraph.VSetDecide.F.eq_dec c.1 c.2); cbn.
    + destruct H; [destruct H; contradiction| assumption].
    + apply EdgeSet.add_spec. destruct H; [destruct H; left; assumption| right; assumption].
Qed.

Lemma add_constraint_vertices c G: SortFamilySet.In c.1 (sGraph.V G) ->
  SortFamilySet.In c.2 (sGraph.V G) ->
  SortFamilySet.Equal (sGraph.V G) (sGraph.V (add_constraint c G)).
Proof.
  intros.
  unfold add_constraint. set d := (VSetDecide.F.eq_dec c.1 c.2).
  destruct d; cbn; [reflexivity|].
  split; intro.
  - apply SortFamilySet.add_spec. right; apply SortFamilySet.add_spec; right; assumption.
  - do 2 (apply SortFamilySet.add_spec in H1; destruct H1; [rewrite H1; assumption|]).
    assumption.
Qed.

Lemma add_constraint_no_loop (c:SortConstraint.t) (G:sGraph.t) :
  (no_self_loop G) -> no_self_loop (add_constraint c G).
Proof.
  do 4 intro. apply add_constraint_correct in H0. destruct H0.
  - destruct H0. rewrite H0 in H1. cbn in H1. contradiction.
  - apply (H e H0 H1).
Qed.

Definition add_constraints : SortConstraintSet.t -> sGraph.t -> sGraph.t :=
  fun constraints graph => SortConstraintSet.fold add_constraint constraints graph.

Lemma add_constraints_correct constraints G: forall e,
  EdgeSet.In e (sGraph.E (add_constraints constraints G)) <->
  (exists c, e = c.to_edge /\ c.1 <> c.2 /\ SortConstraintSet.In c constraints) \/
    EdgeSet.In e (sGraph.E G).
Proof.
  split.
  - unfold add_constraints. apply SortConstraintSetProp.fold_rec_nodep; [intro;right;assumption|].
    intros. apply add_constraint_correct in H1; destruct H1.
    + destruct H1; left; exists x; split; [assumption|split; assumption].
    + destruct (H0 H1); [left; assumption|right; assumption].
  - unfold add_constraints. apply SortConstraintSetProp.fold_rec_weak; intros.
    + apply H0. destruct H1; [|right; assumption].
      left. destruct H1. exists x. destruct H1. split; try assumption.
      destruct H2. split; [assumption|]; apply H; assumption.
    + destruct H; [| assumption].
      repeat destruct H. destruct H0. inversion H0.
    + apply add_constraint_correct. destruct H1; [|right;apply H0;right;assumption].
      destruct H1. destruct H1. destruct H2. destruct (SortConstraintSet.add_spec s x x0).
      destruct (H4 H3). destruct x0, x. destruct H6. inversion H6. cbn in H8. rewrite<- H8.
      inversion H7. cbn in H9. rewrite<- H9. left; split; assumption. right; apply H0.
      left; exists x0. repeat split; try assumption.
Qed.

Lemma add_constraints_vertices constraints G: (forall c, SortConstraintSet.In c constraints ->
  SortFamilySet.In c.1 (sGraph.V G) /\ SortFamilySet.In c.2 (sGraph.V G)) ->
  SortFamilySet.Equal (sGraph.V G) (sGraph.V (add_constraints constraints G)).
Proof.
  intros. unfold add_constraints. apply SortConstraintSetProp.fold_rec_nodep; [reflexivity|].
  intros. About SortConstraintSet.eq_leibniz.


Lemma add_constraints_no_loop constraints G: no_self_loop G -> no_self_loop (add_constraints constraints G).
Proof.
  intro. unfold add_constraints. apply SortConstraintSetProp.fold_rec_nodep; try assumption.
  intros. apply add_constraint_no_loop; assumption.
Qed.
*)
Definition initial_edges sorts := SortFamilySet.fold 
  (fun sort s => EdgeSet.add (SortFamily.sfType, sort).to_edge s)
  sorts EdgeSet.empty.

Lemma initial_edges_correct sorts: forall e,
  EdgeSet.In e (initial_edges sorts) <->
  exists s, e = (SortFamily.sfType, s).to_edge /\ SortFamilySet.In s sorts.
Proof.
  intro e. split; unfold initial_edges.
  - apply SortFamilySetProp.fold_rec_nodep.
    + intro H. inversion H.
    + intros x a H H0 H1. apply EdgeSet.add_spec in H1 as [->|H1]; [|exact (H0 H1)].
      exists x. split; [reflexivity|assumption].
  - apply SortFamilySetProp.fold_rec.
    + intros s' H [s [_ H1]]. apply SortFamilySetProp.empty_is_empty_1 in H.
      apply H in H1. inversion H1.
    + intros x a s' s'' H H0 H1%SortFamilySetProp.Add_Equal H2 [s [H3 H4]]. apply EdgeSet.add_spec.
      apply H1 in H4. apply SortFamilySet.add_spec in H4 as [->|H4]; [left; assumption|].
      right. apply H2. exists s. split; assumption.
Qed.

Definition is_not_self_loop edge : bool :=
  if SortFamily.eq_dec edge..s edge..t then false else true.

Definition remove_self_loops edges : EdgeSet.t :=
  EdgeSet.filter is_not_self_loop edges.

Lemma remove_self_loop_correct edges : forall e,
  EdgeSet.In e (remove_self_loops edges) <-> EdgeSet.In e edges /\ e..s <> e..t.
Proof.
  unfold remove_self_loops. intro e.
  assert (EdgeSet.In e edges /\ e..s <> e..t <-> EdgeSet.In e edges /\ is_not_self_loop e).
  + split; intros [H H0]; (split; [assumption|]);
    unfold is_not_self_loop in *; destruct (VSetDecide.F.eq_dec e..s e..t); [destruct (H0 e0)|reflexivity| |assumption].
    cbn in H0. inversion H0.
  + rewrite H. apply EdgeSet.filter_spec.
    intros [[]] [[]] ->. reflexivity.
Qed.

Definition no_self_loop G :=
  (forall e, sGraph.EdgeSet.In e (sGraph.E G) -> e..s <> e..t).

Section MakeGraph.
  Variable φ : SortConstraintSet.t.

  Definition vertices := constraints_to_set φ.
  Definition edges := remove_self_loops (EdgeSet.union (to_edges φ) (initial_edges vertices)).

  (* Changer la def en construisant ensembles de sommets et d'arêtes directement
     et essayer de passer avec des filter plutôt que tester dans add_constraint *)
  Definition make_graph : sGraph.t := (vertices, edges, SortFamily.sfType).

  Lemma make_graph_no_self_loop: no_self_loop make_graph.
  Proof.
    unfold make_graph. intros e H. cbn in H.
    unfold edges in H.
    destruct (remove_self_loop_correct (EdgeSet.union (to_edges φ) (initial_edges (constraints_to_set φ))) e) as [H0 H1].
    destruct (H0 H) as [_ H2]. assumption.
  Qed.

  Lemma make_graph_edges_caract : forall constraint, sGraph.EdgeSet.In constraint.to_edge edges <->
    (constraint.1 <> constraint.2) /\ 
    ((constraint.1 = SortFamily.sfType /\ SortFamilySet.In constraint.2 (constraints_to_set φ)) \/
     SortConstraintSet.In constraint φ).
  Proof.
     intro constraint. split.
    - intro H. split.
      + intro. apply (make_graph_no_self_loop constraint.to_edge); assumption.
      + unfold edges, make_graph in H. cbn in H. unfold edges in H. apply remove_self_loop_correct in H as [H H0].
        apply EdgeSet.union_spec in H. destruct H.
        * right. apply to_edges_correct. assumption.
        * left. destruct constraint. apply initial_edges_correct in H as [s [H H1]]. inversion H. cbn. split; [reflexivity|assumption].
    - intros [H [[H0 H1]|H0]]; unfold edges; apply remove_self_loop_correct;
      (split; [|cbn; assumption]); apply EdgeSet.union_spec.
      + right. apply initial_edges_correct. exists constraint.2.
        split; [|assumption]. destruct constraint. cbn in *. rewrite H0. reflexivity.
      + left. apply to_edges_correct. assumption.
  Qed.

  Lemma make_graph_edges_are_constaints : forall e,
    EdgeSet.In e edges <-> exists c, e = c.to_edge /\ EdgeSet.In c.to_edge edges.
  Proof.
    intro e. split.
    - intro H. unfold edges in H. apply remove_self_loop_correct in H as [H H0].
      apply EdgeSet.union_spec in H as [H|H].
      + unfold to_edges in H. unfold edges, vertices. induction φ using SortConstraintSetProp.set_induction.
        * rewrite (SortConstraintSet.eq_leibniz (SortConstraintSetProp.empty_is_empty_1 H1)) in H.
          rewrite SortConstraintSetProp.fold_empty in H. inversion H.
        * apply SortConstraintSetProp.Add_Equal in H2. rewrite (SortConstraintSet.eq_leibniz H2) in H.
          apply (SortConstraintSetProp.fold_add EdgeSet.eq_equiv add_edge_compat add_edge_trans) in H; try assumption.
          apply add_edge_correct in H as [H|H]; [exists x|destruct (IHt0_1 H) as [c [H3 H4]]; exists c];
          (split; [assumption|]); apply remove_self_loop_correct; [split; [|now rewrite<- H]|split; [|now rewrite<- H3]];
          apply EdgeSet.union_spec. 2: apply remove_self_loop_correct in H4 as [H4 H5];
          apply EdgeSet.union_spec in H4 as [H4%to_edges_correct|[s [H4 H6%constraints_to_set_correct]]%initial_edges_correct].
          1-2: left; apply to_edges_correct; apply H2.
          1: now apply SortConstraintSetFact.add_1.
          1: now apply SortConstraintSetFact.add_2.
          right; apply initial_edges_correct. exists s; split; try assumption.
          apply constraints_to_set_correct. destruct H6 as [H6|[constraint [H6 H7]]]; [left;assumption|]. right; exists constraint.
          split; [|assumption]. apply H2. now apply SortConstraintSetFact.add_2.
      + apply initial_edges_correct in H as [s [H H1]].
        exists (SortFamily.sfType, s). split; [assumption|].
        unfold edges. apply remove_self_loop_correct. split; [|now rewrite<- H].
        apply EdgeSetFact.union_3. now apply initial_edges_correct.
    - now intros [c [[=->] H0]].
  Qed.

  Lemma make_graph_well_formed: invariants make_graph.
  Proof.
    constructor.
    - intros e H. cbn in H. apply make_graph_edges_are_constaints in H as [c [[=->] H]].
      cbn. apply make_graph_edges_caract in H as [_ [[H H0]| H]].
      + split; [|assumption]. apply constraints_to_set_correct. left. assumption.
      + split; apply constraints_to_set_correct; right; exists c.
        * split; [assumption|now left].
        * split; [assumption|now right].
    - cbn. apply constraints_to_set_correct. now left.
    - cbn. intros x H. constructor.
      + destruct (SortFamily.eq_dec SortFamily.sfType x) as [->|e].
        * exists (paths_refl make_graph x). constructor. cbn. reflexivity.
        * destruct (make_graph_edges_caract (SortFamily.sfType, x)).
          assert (EdgeSet.In (SortFamily.sfType, 1%Z, x) (sGraph.E make_graph));
          [apply H1; cbn; split; [assumption| left; split; [reflexivity|assumption]]|].
          exists (paths_step make_graph SortFamily.sfType x x (1%Z;H2) (paths_refl make_graph x)).
          constructor. cbn. lia.
  Qed.

End MakeGraph.

Section GlobalConstraints.
  Definition global_sorts :=
    SortFamilySet.add SortFamily.sfType (SortFamilySet.add SortFamily.sfProp
    (SortFamilySet.singleton SortFamily.sfSProp)).

  Definition global_constraints : SortConstraintSet.t := 
    SortConstraintSet.add (SortFamily.sfType, SortFamily.sfProp)
    (SortConstraintSet.singleton (SortFamily.sfProp, SortFamily.sfSProp)).
  
  Definition add_global : SortConstraintSet.t -> SortConstraintSet.t := 
    fun c => SortConstraintSet.union c global_constraints.
End GlobalConstraints.

Section Eliminability.
  Variable (φ : SortConstraintSet.t).
  Definition G := make_graph (add_global φ).

  Definition is_eliminable : SortFamily.t -> SortFamily.t -> bool :=
    fun x y => match (sGraph.lsp G x y) with
      | None => false
      | Some n => true
    end. 

  Lemma is_eliminable_correct s1 s2 : is_eliminable s1 s2 <->
    ∥ SimplePaths G (sGraph.V G) s1 s2 ∥.
  Proof.
    set path := lsp0 G (sGraph.V G) s1 s2.
    assert (lsp0 G (sGraph.V G) s1 s2 = path). reflexivity.
    clearbody path.
    split.
    - intro. unfold is_eliminable, lsp in H0.
      destruct path as [a|].
      + destruct (lsp0_spec_eq G a H). apply (sq x).
      + rewrite H in H0. inversion H0.
    - intro; inversion H0. unfold is_eliminable, lsp.
      assert (Nbar.le (Some (sweight X)) path). rewrite<- H.
      apply (sGraph.lsp0_spec_le G X).
      rewrite H. induction path. reflexivity. inversion H1.
  Qed.

  Lemma is_eliminable_correct' s1 s2 : is_eliminable s1 s2 = true <->
      ∥ sGraph.Paths G s1 s2 ∥.
  Proof.
    destruct (is_eliminable_correct s1 s2).
    split.
    - intro. destruct (H H1). constructor. apply (sGraph.to_paths G X).
    - intro; destruct H1. apply is_eliminable_correct. constructor. apply simplify2'; [exact (make_graph_well_formed (add_global φ))|assumption].
  Qed.

  Definition is_impredicative : SortFamily.t -> bool :=
    fun s => is_eliminable SortFamily.sfProp s.
End Eliminability.

Section GoodConstraints.

End GoodConstraints.

(* TODO décider de la comparabilité d'univers ? *)

(* TODO acyclicité *)

(* TODO reste conforme aux contraintes globales *)
