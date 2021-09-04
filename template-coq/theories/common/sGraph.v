From Coq Require Import MSetList MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils config wGraph Universes.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Module SortFamilySet := MSetList.MakeWithLeibniz SortFamily.
Module SortFamilySetFact := WFactsOn SortFamily SortFamilySet.
Module SortFamilySetProp := WPropertiesOn SortFamily SortFamilySet.

Module WeightedGraphExt (V: UsualOrderedTypeWithLeibniz) (VSet : MSetList.SWithLeibniz with Module E := V).
  Include WeightedGraph V VSet.

  Section self_loops.
    Definition is_not_self_loop edge : bool :=
      if V.eq_dec edge..s edge..t then false else true.

    Definition remove_self_loops edges : EdgeSet.t :=
      EdgeSet.filter is_not_self_loop edges.

    Lemma remove_self_loop_correct edges : forall e,
      EdgeSet.In e (remove_self_loops edges) <-> EdgeSet.In e edges /\ e..s <> e..t.
    Proof.
      unfold remove_self_loops. intro e.
      assert (EdgeSet.In e edges /\ e..s <> e..t <-> EdgeSet.In e edges /\ is_not_self_loop e).
      + split; intros [H H0]; split => //;
        unfold is_not_self_loop in *; by destruct (VSetDecide.F.eq_dec e..s e..t).
      + rewrite H. apply EdgeSet.filter_spec.
        by intros [[]] [[]] ->.
    Qed.

    Definition no_self_loop G :=
      (forall e, EdgeSet.In e (E G) -> e..s <> e..t).
  End self_loops.

  Section Stuff.
    Context (G : t).

    Definition Partition (total part1 part2 part3 : VSet.t) : Prop :=
      VSet.union part1 (VSet.union part2 part3) = total /\
      VSet.Empty (VSet.inter part1 part2) /\
      VSet.Empty (VSet.inter part2 part3) /\
      VSet.Empty (VSet.inter part3 part1).

    Lemma partition_move_21 total v s l x : VSet.In x s -> Partition total v s l ->
      Partition total (VSet.add x v) (VSet.remove x s) l.
    Proof.
      intros H [[=<-] [inter12 [inter23 inter31]]].
      repeat split; [apply VSet.eq_leibniz| | |]; intro y.
      - repeat rewrite VSet.union_spec.
        rewrite VSet.add_spec. rewrite VSet.remove_spec. split.
        + by intros [[H3%V.eq_leibniz|?]|[[? _]|?]];
            [right;left;rewrite H3|left|right;left|right;right].
        + intros H3. destruct (V.eq_dec y x); [by left;left|].
          by destruct H3 as [?|[?|?]]; [left;right|right;left|right;right].
      - rewrite VSet.inter_spec VSet.add_spec VSet.remove_spec.
        intros [[?|?] [? ?]] => //. apply (inter12 y).
        now rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec VSet.remove_spec.
        intros [[? _] ?]. apply (inter23 y). now rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec VSet.add_spec. intros [? [H3|?]].
        + apply (inter23 y). rewrite VSet.inter_spec.
          split; [by rewrite H3|assumption].
        + apply (inter31 y). now rewrite VSet.inter_spec.
    Qed.

    Lemma partition_move_23 total v s l x : VSet.In x s -> Partition total v s l ->
      Partition total v (VSet.remove x s) (VSet.add x l).
    Proof.
      intros H [[=<-] [inter12 [inter23 inter31]]].
      repeat split; [apply VSet.eq_leibniz| | |]; intro y.
      - repeat rewrite VSet.union_spec. rewrite VSet.add_spec VSet.remove_spec.
        split.
        + by intros [?|[[? _]|[?|?]]];
          [left|right;left|right;left;rewrite H0|right;right].
        + intros H0. destruct (V.eq_dec y x); [now right;right;left|].
          by destruct H0 as [?|[?|?]]; [left|right;left|right;right;right].
      - rewrite VSet.inter_spec VSet.remove_spec.
        intros [? [? ?]]. apply (inter12 y). by rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec VSet.add_spec VSet.remove_spec.
        intros [[? ?] [?|?]]=> //. apply (inter23 y).
        by rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec VSet.add_spec. intros [[H0|?] ?]. 
        + rewrite<- H0 in H.
          apply (inter12 y). by rewrite VSet.inter_spec.
        + apply (inter31 y). by rewrite VSet.inter_spec.
    Qed.

    Lemma partition_move_13 total v s l x : ~ VSet.In x v ->
      Partition total (VSet.add x v) s (VSetProp.of_list l) ->
      Partition total v s (VSetProp.of_list (x::l)).
    Proof.
      intros H [[=<-] [inter12 [inter23 inter31]]].
      repeat split; [apply VSet.eq_leibniz| | |]; intro y.
      - cbn. repeat rewrite VSet.union_spec. repeat rewrite VSet.add_spec.
        split.
        + by intros [?|[?|[?|?]]]; [left;right|right;left|left;left|right;right].
        + by intros [[?|?]|[?|?]]; [right;right;left|left|right;left|right;right;right].
      - rewrite VSet.inter_spec. intros [? ?]. apply (inter12 y).
        rewrite VSet.inter_spec VSet.add_spec. by split; [right|].
      - cbn. rewrite VSet.inter_spec VSet.add_spec. intros [? [H0|?]].
        + apply (inter12 x). rewrite VSet.inter_spec VSet.add_spec. rewrite<- H0.
          by split; [left|].
        + apply (inter23 y). by rewrite VSet.inter_spec.
      - cbn. rewrite VSet.inter_spec VSet.add_spec. intros [[H0|?] ?].
        + apply H. by rewrite<- H0.
        + apply (inter31 y). rewrite VSet.inter_spec VSet.add_spec.
          by split; [|right].
    Qed.

    Lemma partition_move_31 total v s l x :
      ~ VSet.In x (VSetProp.of_list l) ->
      Partition total v s (VSet.add x (VSetProp.of_list l)) ->
      Partition total (VSet.add x v) s (VSetProp.of_list l).
    Proof.
      intros H [[=<-] [inter12 [inter23 inter31]]].
      repeat split; [apply VSet.eq_leibniz| | |]; intro y.
      - repeat rewrite VSet.union_spec. repeat rewrite VSet.add_spec.
        split.
        + by intros [[?|?]|[?|?]]; [right;right;left|left|right;left|right;right;right].
        + by intros [?|[?|[?|?]]]; [left;right|right;left|left;left|right;right].
      - rewrite VSet.inter_spec VSet.add_spec. intros [[?|?] ?].
        + apply (inter23 y). rewrite VSet.inter_spec VSet.add_spec.
          by split; [|left].
        + apply (inter12 y). by rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec. intros [? ?]. apply (inter23 y).
        rewrite VSet.inter_spec VSet.add_spec. by split; [|right].
      - rewrite VSet.inter_spec VSet.add_spec. intros [? [->|?]].
        + by apply H.
        + apply (inter31 y). rewrite VSet.inter_spec VSet.add_spec.
          by split; [right|].
    Qed.

    Lemma partition_in total v s l x : VSet.In x total ->
      Partition total v s l -> VSet.In x v \/ VSet.In x s \/ VSet.In x l.
    Proof.
      intros H [H0 _]. rewrite<- H0 in H. revert H.
      by repeat rewrite VSet.union_spec.
    Qed.

    Definition succ' x := map (fun x => x.2) (succs G x).

    Lemma edges_elements x y : (∑ n, In (x, n, y) (EdgeSet.elements (E G))) -> ∑ n, EdgeSet.In (x, n, y) (E G).
    Proof.
      intros [n Hn]. exists n. apply-> EdgeSet.elements_spec1.
      apply InA_alt. by exists (x, n, y).
    Qed.

    Lemma succ'_spec_1 x : forall y, In y (succ' x) -> Edges G x y.
    Proof.
      intros y Hy. apply edges_elements. unfold succ', succs in Hy. revert y Hy.
      induction (EdgeSet.elements (E G)).
      - easy.
      - simpl. intros y H. destruct (VSetDecide.F.eq_dec a..s x).
        + cbn in H. destruct (V.eq_dec a..t y).
          * exists (a..w). left. rewrite<- e0, <-e. by destruct a as [[] ?].
          * destruct (IHl y) as [n0 ?].
            -- destruct H => //.
            -- exists (n0). by right.
        + cbn in H. destruct (IHl y H) as [n0 ?]. exists n0. by right.
    Qed.

    Lemma succ'_spec_2 x y : Edges G x y -> In y (succ' x).
    Proof.
      intros [n e].
      apply<- in_map_iff. exists (n, y). split => //.
      apply<- in_map_iff. exists (x, n, y). split => //.
      apply filter_In. split.
      - apply EdgeSet.elements_spec1 in e as H1.
        apply InA_alt in H1 as [y0 [H1 H2]].
        by rewrite H1.
      - cbn. destruct V.eq_equiv as [refl _ _].
        by destruct (VSetDecide.F.eq_dec x x).
    Qed.

    Definition pred (x : V.t) : list V.t := 
      let l := List.filter (fun e => V.eq_dec e..t x) (EdgeSet.elements (E G)) in
      List.map (fun e => e..s) l.

    Lemma pred_spec_1 x y : In y (pred x) -> Edges G y x.
    Proof.
      intros Hy. apply edges_elements. unfold pred in Hy. revert y Hy.
      induction (EdgeSet.elements (E G)) => //.
      simpl. intros y H. destruct (VSetDecide.F.eq_dec a..t x).
      - cbn in H. destruct (V.eq_dec a..s y).
        * exists (a..w). left. rewrite<- e0, <-e. by destruct a as [[] ?].
        * destruct (IHl y) as [n0 ?].
          + by destruct H.
          + exists n0. by right.
      - cbn in H. destruct (IHl y H) as [n0 ?]. exists n0. by right.
    Qed.

    Lemma pred_spec_2 x y : Edges G x y -> In x (pred y).
    Proof.
      intros [n e]. apply in_map_iff. exists (x, n, y). split => //.
      apply filter_In. split.
      - apply EdgeSet.elements_spec1 in e as H1.
        apply InA_alt in H1 as [y0 [H1 H2]].
        by rewrite H1.
      - destruct V.eq_equiv as [refl _ _].
        simpl. by destruct (VSetDecide.F.eq_dec y y).
    Qed.

    Lemma inv_cardinal s x : VSet.In x s -> exists n, VSet.cardinal s = S n.
    Proof.
      intros [y [[=->] H%in_split]]%VSetFact.elements_1%InA_alt.
      destruct H as [l1 [l2 H]]. rewrite VSet.cardinal_spec H app_length.
      cbn. rewrite<- plus_n_Sm. by exists (#|l1| + #|l2|).
    Qed.

  Lemma path_last_edge x y : x <> y -> Paths G x y ->
    ∑ z, Paths G x z × Edges G z y.
  Proof.
    intros H p.
    induction p => //.
    destruct (V.eq_dec y z) as [<-|H0].
    - exists x. split => //. apply paths_refl.
    - destruct (IHp H0) as [x' [p' e']].
      exists x'.
      split => //.
      apply (paths_step _ _ _ _ e p').
  Qed.

  End Stuff.

  Section topological_sort.
    Context (G:t).
    Context {HI : invariants G}.

    Fixpoint topological_sort00 fuel (s:VSet.t) l (x:V.t) : list V.t × VSet.t :=
      match fuel with
      | O => (l, s)
      | S n =>
        match VSet.mem x s with
        | true => let a := (List.fold_left
            (fun a u => (topological_sort00 n a.2 a.1 u))
            (succ' G x) (l,VSet.remove x s)) in
            (x::a.1, a.2)
        | false => (l, s)
        end
      end.

    Lemma topological_sort00_subset l x fuel s:
      VSet.Subset (topological_sort00 fuel s l x).2 s.
    Proof.
      revert s l x.
      induction fuel.
      + cbn. intros. apply VSetProp.subset_refl.
      + cbn. intros s l x. case Hx: (VSet.mem x s); [|cbn; apply VSetProp.subset_refl].
        set l2 := (succ' _ _).
        assert (VSet.Subset (VSet.remove x s) s) as H;
          [intros a H; now apply VSet.remove_spec in H as [H _]|].
        generalize l (VSet.remove x s) H.
        induction l2.
        - cbn. easy.
        - cbn. intros l' t Ht.
          have H1:= IHfuel t l' a. move: H1.
          set a0 := topological_sort00 _ _ _ _.
          destruct a0. cbn. move => H1. apply (IHl2 l0 t0).
          etransitivity; eassumption.
    Qed.

    Lemma topological_sort00_subset_fold l1 : forall fuel a s',
      VSet.Subset a.2 s' ->
      VSet.Subset (fold_left (fun a u => (topological_sort00 fuel a.2 a.1 u))
        l1 a).2 s'.
    Proof.
      induction l1 as [|x l1] => //.
      intros fuel a s' H. cbn. apply IHl1.
      transitivity a.2 => //. apply topological_sort00_subset.
    Qed.

    Definition topological_sort0 s := topological_sort00 (VSet.cardinal s) s.

    Lemma topological_sort00_inc : forall m n s l x, m <= n -> VSet.cardinal s <= m ->
      topological_sort00 n s l x = topological_sort0 s l x.
    Proof.
      induction m.
      - intros n s l x H HH. unfold topological_sort0.
        inversion HH as [H1|H1]. rewrite H1. case n => //. apply VSetProp.cardinal_inv_1 in H1.
        specialize (H1 x). apply VSetProp.FM.not_mem_iff in H1. cbn.
        now rewrite H1.
      - intros n s0 l x H H0. unfold topological_sort0.
        destruct n; [inversion H|].
        remember (S m) as m0.
        destruct H0; [|apply IHm; lia].
        rewrite Heqm0.
        cbn. case Hx: (VSet.mem x s0) => //.
        set fa := fold_left _ _ _.
        set fb := fold_left _ _ _.
        enough (fa = fb) as H1; [now rewrite H1|].
        unfold fa, fb. set l2 := succ' _ _.
        apply VSetFact.mem_iff in Hx. apply VSetProp.remove_cardinal_1 in Hx.
        assert (S (VSet.cardinal (VSet.remove x s0)) <= VSet.cardinal s0) as H1; [lia|].
        generalize l (VSet.remove x s0) H1.
        induction l2 => //.
        simpl. intros l0 t0 Ht. rewrite IHm; [lia|lia|].
        rewrite IHm => //; [lia|].
        move: (topological_sort00_subset l0 a (VSet.cardinal t0) t0).
        unfold topological_sort0.
        set p := topological_sort00 _ _ _ _.
        destruct p. cbn. intro H3.
        apply IHl2. etransitivity; last eassumption. apply le_n_S.
        now apply VSetProp.subset_cardinal.
    Qed.

    Lemma fold_left_ext {A B: Type} (f g : A -> B -> A) (P : A -> Prop)
      (l : list B) : forall a, P a -> (forall a0 b, P a0 -> f a0 b = g a0 b) ->
      (forall a0 b, P a0 -> P (f a0 b)) -> fold_left f l a = fold_left g l a.
    Proof.
      induction l => //.
      cbn. intros a0 H H0 H1. rewrite<- (H0 a0 a H).
      apply IHl => //. now apply H1.
    Qed.

    Lemma topological_sort0_eq s l x: topological_sort0 s l x =
      match VSet.mem x s with
      | true => let a := (List.fold_left
          (fun a u => (topological_sort0 a.2 a.1 u))
          (succ' G x) (l, VSet.remove x s)) in
          (x::a.1, a.2)
      | false => (l, s)
      end.
    Proof.
      unfold topological_sort0. set (fuel := VSet.cardinal s).
      cut (VSet.cardinal s = fuel)=> //.
      clearbody fuel. revert s x. induction fuel.
      - intros s x H. apply VSetProp.cardinal_inv_1 in H.
        specialize (H x). apply VSetProp.FM.not_mem_iff in H.
        by rewrite H.
      - intros s x H. simpl.
        case_eq (VSet.mem x s)=> //.
        intro HH. rewrite<- (@VSetProp.remove_cardinal_1 s x) in H;
        [|now apply VSetFact.mem_iff]. inversion H as [H1].
        rewrite H1. rewrite (fold_left_ext _ 
          (fun a u => topological_sort00 (VSet.cardinal a.2) a.2 a.1 u)
          (fun a => VSet.cardinal a.2 <= fuel)) => //.
        + cbn. rewrite H1. apply le_n.
        + intros a0 b H2. now apply (topological_sort00_inc (VSet.cardinal a0.2)).
        + intros a0 b H2. transitivity (VSet.cardinal a0.2) => //.
          apply VSetProp.subset_cardinal. apply topological_sort00_subset.
    Qed.

    Definition topological_sort := (topological_sort0 (V G) nil (s G)).1.

    Lemma topological_sort00_input_list fuel s l x : exists l', (topological_sort00 fuel s l x).1 = l' ++ l.
    Proof.
      revert x l s.
      induction fuel.
      - exists []. now cbn.
      - intros x l s.
        cbn. destruct (VSet.mem x s).
        + set l2 := succ' _ _. clearbody l2. cbn. set p := (l, VSet.remove x s).
          assert (exists l', p.1 = l' ++ l) as H; [by exists []|]. revert H. generalize p.
          induction l2.
          * cbn. intros p0 [l' H]. rewrite H. by exists (x :: l').
          * cbn. intros p0 [l' H]. apply (IHl2 (topological_sort00 fuel p0.2 p0.1 a)).
            destruct (IHfuel a p0.1 p0.2) as [l'' H0].
            exists (l'' ++ l'). rewrite<- app_assoc. rewrite H0. now rewrite H.
        + by exists [].
    Qed.

    Lemma topological_sort00_fold_input_list fuel s l l2 : exists l', (fold_left (fun a u => topological_sort00 fuel a.2 a.1 u) l2 (l, s)).1 = l' ++ l.
    Proof.
      revert fuel s l.
      induction l2.
      - cbn. by exists [].
      - cbn. intros fuel s l. destruct (topological_sort00_input_list fuel s l a) as [l'' H].
        set p := topological_sort00 _ _ _ _. destruct (IHl2 fuel p.2 p.1) as [l' H0].
        exists (l' ++ l''). rewrite<- app_assoc. rewrite<- (surjective_pairing p) in H0.
        rewrite H0. unfold p, topological_sort0. now rewrite H.
    Qed.


    Definition acyclic := forall x y, Edges G x y -> Paths G y x -> False.

    Inductive is_topo_sorted : list V.t -> Prop :=
      | is_topo_sorted_nil : is_topo_sorted []
      | is_topo_sorted_cons x l : (forall y, Paths G x y -> In y (x::l)) -> is_topo_sorted l -> is_topo_sorted (x::l).

    Lemma is_topo_sorted_alt l : is_topo_sorted l <->
      (forall x y l1 l2, l = l1 ++ x :: l2 -> Paths G x y -> In y (x::l2)).
    Proof.
      split.
      - intros H x0 y l1 l2 H1 p. revert l H H1. induction l1.
        + intros l H H1. induction H.
          * contradiction (app_cons_not_nil [] l2 x0 H1).
          * injection H1. intros [=->] [=->]. apply H => //.
        + intros l H H1. rewrite<- app_comm_cons in H1. rewrite H1 in H.
          inversion H as [|x l0 H0 H2 [H3 H4]]. apply (IHl1 (l1 ++ x0 :: l2)) => //.
      - intros H. induction l; [constructor|].
        constructor.
        + intros y p. apply (H _ _ []) => //.
        + apply IHl. intros x y l1 l2 H0 p. apply (H _ _ (a::l1)) => //.
          rewrite<- app_comm_cons. by rewrite H0.
    Qed.

    Lemma in_nodup_inv {A : Type} (z : A) l1 : forall l2 l3 l4,
      NoDup (l1 ++ z :: l2) ->
      l1 ++ z :: l2 = l3 ++ z :: l4 ->
      l1 = l3 /\ l2 = l4.
    Proof.
      induction l1.
      + intros l2 l3 l4 H H0. rewrite H0 in H.
        apply NoDup_remove_2 in H.
        destruct l3.
        * by injection H0.
        * injection H0 => _ H3. rewrite H3 in H. exfalso. apply H.
          rewrite<- app_comm_cons. apply in_eq.
      + intros l2 l3 l4 H H0.
        destruct l3.
        * rewrite<- app_comm_cons in H0.
          injection H0 => _ H1. rewrite H1 in H.
          apply NoDup_remove_2 in H. exfalso. apply H.
          rewrite<- app_comm_cons. apply in_eq.
        * repeat rewrite<- app_comm_cons in H0.
          rewrite<- app_comm_cons in H.
          depelim H.
          injection H1 => H2 H3.
          destruct (IHl1 l2 l3 l4) => //.
          by rewrite H3 H4.
    Qed.

    Lemma topo_sort_change_way l (x y : V.t) : NoDup l ->
      In x l -> In y l ->
      (forall l1 l2, l = l1 ++ x :: l2 -> In y (x::l2)) <->
      (forall l1 l2, l = l1 ++ y :: l2 -> In x l1 \/ x = y).
    Proof.
      intros Hd Hx Hy.
      split.
      - intros H l1 l2 H0.
        apply in_split in Hx as [l3 [l4 H1]].
        destruct (H _ _ H1) as [->|H2]; [by right|].
        apply in_split in H2 as [l5 [l6 ->]].
        rewrite app_comm_cons in H1.
        rewrite app_assoc in H1.
        rewrite H0 in Hd H1.
        destruct (in_nodup_inv _ _ _ _ _ Hd H1) as [-> _].
        left. apply in_or_app. right. apply in_eq.
      - intros H l1 l2 H0.
        apply in_split in Hy as [l3 [l4 H1]].
        destruct (H _ _ H1) as [H2| ->]; [|apply in_eq].
        apply in_split in H2 as [l5 [l6 ->]].
        rewrite<- app_assoc in H1. rewrite<- app_comm_cons in H1.
        rewrite H0 in H1 Hd.
        destruct (in_nodup_inv _ _ _ _ _ Hd H1) as [_ ->].
        apply in_cons. apply in_or_app. right. apply in_eq.
    Qed.

    Lemma is_topo_sorted_pred l : NoDup l -> is_topo_sorted l ->
      (forall x y l1 l2, l = l1 ++ y :: l2 -> In x l -> Paths G x y -> In x l1 \/ x = y).
    Proof.
      rewrite is_topo_sorted_alt.
      intros Hd H x y l1 l2 H0 Hx p.
      destruct (topo_sort_change_way l x y) as [H1 _] => //.
      - rewrite H0. apply in_or_app. right. apply in_eq.
      - refine (H1 _ _ l2 _) => //.
        intros l3 l4 H2. by apply (H x y l3 l4).
    Qed.

    Lemma is_topo_sorted_weak l y z : is_topo_sorted l -> In y l ->
      Paths G y z -> In z l.
    Proof.
      intros H [l1 [l2 H0]]%in_split p. rewrite H0 in H |- *. clear H0.
      induction l1.
      - inversion H. apply H2 => //.
      - rewrite<- app_comm_cons. apply in_cons. apply IHl1. inversion H => //.
    Qed.

    Definition configuration v s l x : Prop := Partition (V G) v s (VSetProp.of_list l) /\
      (forall y, Paths G x y -> VSet.In y v -> False) /\ is_topo_sorted l.

    Definition config' v s l : Prop := Partition (V G) v s (VSetProp.of_list l) /\
      is_topo_sorted l.

    Lemma config_init : configuration VSet.empty (V G) [] (s G).
    Proof.
      repeat split; cbn; have Hempty := VSet.empty_spec.
      - rewrite (VSet.eq_leibniz (VSetProp.empty_union_1 _ _)) => //.
        rewrite (VSet.eq_leibniz (VSetProp.empty_union_2 _ _)) => //.
      - apply VSetProp.empty_inter_1 => //.
      - apply VSetProp.empty_inter_2 => //.
      - apply VSetProp.empty_inter_1 => //.
      - intros ? _ ?%VSetFact.empty_1 => //.
      - constructor.
    Qed.

    Context {Ha : acyclic}.

    Lemma topological_sort00_spec fuel : forall v s l x, configuration v s l x ->
      VSet.cardinal s <= fuel ->
      let a := (topological_sort00 fuel s l x) in configuration v a.2 a.1 x.
    Proof.
      induction fuel => //.
      intros v s l x config Hfuel.
      destruct config as [part [back_path topo_sort]]. cbn delta fix match beta.
      destruct (VSet.mem x s) eqn: H0 => //.
      apply VSetFact.mem_iff in H0.
      set l0 := succ' G x.
      assert (succ' G x = [] ++ l0) as H => //.
      assert (let a := fold_left (fun a u => topological_sort00 fuel a.2 a.1 u)
        [] (l, VSet.remove x s) in config' (VSet.add x v) a.2 a.1 /\
          forall y z, Edges G x y -> In y [] -> Paths G y z -> In z (x::a.1)).
      - split => //. split => //. apply partition_move_21 => //.
      - rewrite<- (app_nil_l l0). elim: l0 [] H H1.
        + intro l1. rewrite app_nil_r. intros H [[? ?] ?].
          split; [|split] => //.
          * apply partition_move_13 => //. destruct part as [_ [part _]].
            intro. apply (part x). by rewrite VSet.inter_spec.
          * constructor => //.
            intros y path. destruct path; [apply in_eq|].
               apply (H3 y) => //. rewrite<- H. apply succ'_spec_2 => //.
        + intros x0 l0 IHl0 l1. set a := fold_left (fun a0 u => topological_sort00 fuel a0.2 a0.1 u) l1
            (l, VSet.remove x s).
          intros H [[Hpart Hsorted] Hpath].
          assert (l1 ++ x0 :: l0 = (l1 ++ [x0]) ++ l0) as H2; [by rewrite<- app_assoc|].
          rewrite H2. apply IHl0; [easy|].
          rewrite fold_left_app. fold a. cbn.
          destruct (IHfuel (VSet.add x v) a.2 a.1 x0) as [? [? ?]]; [| |split => //].
          * split; [|split] => //. intros y path [Hy|Hy]%VSet.add_spec;
            [rewrite Hy in path; unfold acyclic in Ha; apply (Ha x x0) => //|
             apply (back_path y) => //; apply (paths_step _ _ x0); [|eassumption]];
            apply succ'_spec_1; fold (succ' G x); rewrite H; apply in_or_app;
            right; apply in_eq.
          * assert (S (VSet.cardinal (VSet.remove x s)) = VSet.cardinal s) as H6;
              [apply VSetProp.remove_cardinal_1 => //|].
            rewrite<- H6 in Hfuel. apply le_S_n in Hfuel.
            transitivity (VSet.cardinal (VSet.remove x s)) => //.
            apply VSetProp.subset_cardinal. apply topological_sort00_subset_fold.
            apply VSetProp.subset_refl.
          * intros y z e [Hy|[[=->]|?]]%in_app_or p => //.
            -- destruct (Hpath y z e Hy p); [by left|]. right.
               destruct (topological_sort00_input_list fuel a.2 a.1 x0) as [? [=->]].
               apply in_or_app. by right.
            -- right. destruct HI as [edges _ _]. specialize (edges _ e.π2) as [_ Iny].
               cbn in Iny.
               destruct (partition_in _ _ _ _ _ Iny H1) as [[H5%V.eq_leibniz|H5]%VSet.add_spec|[H5|H5]].
               ++ exfalso. unfold acyclic in Ha. apply (Ha x y) => //. rewrite H5.
                  apply paths_refl.
               ++ exfalso. apply (back_path y) => //.
                  apply (paths_step _ _ y) => //. apply paths_refl.
               ++ assert (S (VSet.cardinal (VSet.remove x s)) = VSet.cardinal s) as H6;
                    [apply VSetProp.remove_cardinal_1 => //|].
                  rewrite<- H6 in Hfuel. apply le_S_n in Hfuel.
                  assert (VSet.In y a.2); [apply (topological_sort00_subset a.1 y fuel a.2) => //|].
                  assert (VSet.Subset a.2 (VSet.remove x s)).
                  1: {apply topological_sort00_subset_fold. apply VSetProp.subset_refl. }
                  assert (VSet.cardinal a.2 <= fuel). 
                  1: {transitivity (VSet.cardinal (VSet.remove x s)) => //. apply VSetProp.subset_cardinal => //. }
                  destruct (inv_cardinal a.2 y) as [n H10] => //. rewrite H10 in H9.
                  destruct fuel; [inversion H9|]. apply (is_topo_sorted_weak _ y) => //.
                  cbn. apply (VSetFact.mem_iff a.2 y) in H7 as [=->]. apply in_eq.
               ++ apply (is_topo_sorted_weak _ y) => //. revert H5.
                  rewrite VSetProp.of_list_1. by intros [? [[=->] ?]]%InA_alt.
    Qed.

    Lemma topological_sort_reach x z v s l: Paths G x z -> VSet.In x s ->
      configuration v s l x -> In z (topological_sort0 s l x).1.
    Proof.
      intros p H%VSetFact.mem_iff config.
      apply (topological_sort00_spec (VSet.cardinal s)) in config => //.
      destruct config as [_ [_ ?]].
      apply (is_topo_sorted_weak _ x) => //. rewrite topological_sort0_eq H.
      apply in_eq.
    Qed.

    Lemma topological_sort_in y: Paths G (s G) y ->
      In y (topological_sort).
    Proof.
      intro H. destruct HI as [edges source path].
      apply (topological_sort_reach _ _ VSet.empty) => //.
      apply config_init.
    Qed.

    Lemma topological_sort_in_graph y : In y topological_sort ->
      VSet.In y (V G).
    Proof.
      intro H. unfold topological_sort, topological_sort0 in H.
      destruct (topological_sort00_spec 
                  (VSet.cardinal (V G)) VSet.empty (V G) [] (s G)) as [H0 _] => //.
      + apply config_init.
      + destruct H0 as [tot _]. rewrite<- tot.
        rewrite VSet.union_spec. right.
        rewrite VSet.union_spec. right.
        apply VSetProp.of_list_1. apply InA_alt.
        by exists y.
    Qed.

    Lemma topological_sort_spec x l l': topological_sort = l ++ x::l' ->
      forall y, Paths G x y -> In y (x::l').
    Proof.
      intros H y p.
      have config := config_init. apply (topological_sort00_spec (VSet.cardinal (V G))) in config => //.
      destruct config as [_ [_ is_sorted]].
      destruct (is_topo_sorted_alt topological_sort) as [H0 _].
      apply (H0 is_sorted x y l l' H p).
    Qed.

    Lemma topological_sort00_not_mem fuel : forall s l x a, ~ VSet.In x s -> ~ In x l ->
      ~ In x (topological_sort00 fuel s l a).1.
    Proof.
      induction fuel => //.
      intros s l x a Hs Hl. apply VSetFact.not_mem_iff in Hs. cbn.
      destruct (V.eq_dec a x) as [H|H].
      - rewrite H. rewrite Hs => //.
      - destruct (VSet.mem a s) => //. intro H0. destruct H0 => //.
        assert (~ VSet.In x (VSet.remove a s)) as H1.
        + rewrite<- VSetFact.not_mem_iff in Hs. rewrite VSet.remove_spec.
          intros [] => //.
        + move: (VSet.remove a s) l H1 Hl H0. induction (succ' G a) as [|y l'] => //.
          cbn. intros s' l Hs' Hl H0. have Ht := surjective_pairing (topological_sort00 fuel s' l y).
          rewrite Ht in H0.
          apply (IHl' (topological_sort00 fuel s' l y).2 (topological_sort00 fuel s' l y).1) => //.
          * intro H1. apply Hs'. apply: (VSetProp.in_subset); [exact H1|].
            apply topological_sort00_subset.
          * apply IHfuel => //.
    Qed.

    Lemma topological_sort00_partition fuel : forall v s l x,
      Partition (V G) v s (VSetProp.of_list l) ->
      Partition (V G) v (topological_sort00 fuel s l x).2 (VSetProp.of_list (topological_sort00 fuel s l x).1).
    Proof.
      induction fuel => //.
      cbn. intros v s l x part. destruct (VSet.mem x s) eqn: H => //.
      assert (~ VSet.In x (VSetProp.of_list l)) as H0.
      * destruct part as [_ [_ [H0 _]]].
        intro. apply (H0 x). apply VSetFact.mem_iff in H. rewrite VSet.inter_spec => //.
      * assert (Partition (V G) v (VSet.remove x s) (VSet.add x (VSetProp.of_list l))) as part2.
        - apply partition_move_23 => //. by apply VSetFact.mem_iff.
        - elim: (succ' G x) (VSet.remove x s) l H0 {part} part2 => //.
          intros a l0 IHl0 s' l' H0 H1. cbn.
          rewrite (surjective_pairing (topological_sort00 fuel s' l' a)).
          destruct (IHfuel (VSet.add x v) s' l' a) as [total [inter12 [inter23 inter31]]].
          + by apply partition_move_31.
          + apply IHl0.
            ++ rewrite VSetProp.of_list_1. rewrite InA_alt. intros [? [<- H2]].
               move: H2. apply topological_sort00_not_mem.
               -- intros ?. destruct H1 as [_ [_ [H1 _]]]. apply (H1 x).
                 rewrite VSet.inter_spec VSet.add_spec. by split; [|left].
               -- intro. apply H0. apply VSetProp.of_list_1. apply InA_alt.
                 by exists x.
            ++ apply partition_move_13.
               -- destruct H1 as [_ [_ [_ H1]]]. intro. apply (H1 x).
                  rewrite VSet.inter_spec VSet.add_spec. by split; [left|].
               -- by repeat split.
    Qed.

    Lemma topological_sort00_nodup fuel : forall v s l x, NoDup l ->
      Partition (V G) v s (VSetProp.of_list l) -> NoDup (topological_sort00 fuel s l x).1.
    Proof.
      induction fuel => //. intros v s l x H part.
      cbn. destruct (VSet.mem x s) eqn: H0 => //. apply VSetFact.mem_iff in H0.
      assert (~ In x l).
      - intro H1. destruct part as [_ [_ [inter23 _]]]. apply (inter23 x). rewrite VSet.inter_spec. split => //. apply VSetProp.of_list_1.
        apply InA_alt. by exists x.
      - constructor.
        + assert (~ VSet.In x (VSet.remove x s)); [intros [? H2]%VSet.remove_spec => //; by apply H2|].
          generalize l (VSet.remove x s) H1 H2. induction (succ' G x) => //. cbn.
          intros l1 s0 H3 H4. have H5 := surjective_pairing (topological_sort00 fuel s0 l1 a).
          rewrite H5. apply IHl0.
          * by apply topological_sort00_not_mem.
          * intro H6. apply H4. apply: VSetProp.in_subset; [exact H6|].
            apply topological_sort00_subset.
        + assert (Partition (V G) (VSet.add x v) (VSet.remove x s) (VSetProp.of_list l)) as part2.
          * by apply partition_move_21.
          * move: H part2. generalize (VSet.remove x s) l.
            induction (succ' G x) => //. intros s' l' H2 H3. cbn.
            rewrite (surjective_pairing (topological_sort00 fuel s' l' a)).
            apply (IHl0).
            -- by apply (IHfuel (VSet.add x v)). 
            -- by apply topological_sort00_partition.
    Qed.

    Lemma topological_sort_nodup : NoDup topological_sort.
    Proof.
      apply (topological_sort00_nodup _ VSet.empty); [constructor|].
      repeat split; try (apply VSetProp.empty_inter_2; apply VSet.empty_spec).
      * apply VSet.eq_leibniz.
        rewrite VSetProp.empty_union_1; [|apply VSet.empty_spec].
        rewrite VSetProp.empty_union_2 => //.
        apply VSet.empty_spec.
      * apply VSetProp.empty_inter_1. apply VSet.empty_spec.
    Qed.

    Lemma topological_sort_sorted : is_topo_sorted topological_sort.
    Proof.
      unfold topological_sort, topological_sort0.
      destruct (topological_sort00_spec (VSet.cardinal (V G)) VSet.empty (V G) [] (s G)) as [?[? ?]] => //.
      apply config_init.
    Qed.

  End topological_sort.

End WeightedGraphExt.

Module Import sGraph := WeightedGraphExt SortFamily SortFamilySet.

Definition add_sorts : SortConstraint.t -> SortFamilySet.t -> SortFamilySet.t :=
  fun c s => SortFamilySet.add c.2 (SortFamilySet.add c.1 s).

Lemma add_sorts_correct (constraint: SortConstraint.t) (sorts: SortFamilySet.t) :
  forall s, SortFamilySet.In s (add_sorts constraint sorts) <->
    s = constraint.1 \/ s = constraint.2 \/ SortFamilySet.In s sorts.
Proof.
  intro s. split; intro H.
  - unfold add_sorts in H.
    apply SortFamilySet.add_spec in H. destruct H; [by right;left|].
    apply SortFamilySet.add_spec in H. by destruct H; [left| right;right].
  - apply SortFamilySet.add_spec. destruct H.
    + right. apply SortFamilySet.add_spec. by left.
    + destruct H; [by left|]. by right; apply SortFamilySet.add_spec; right.
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
  by rewrite (SortFamilySetProp.add_add _ x.2 y.1).
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
    + apply fold_add_edges in H1 => //.
      apply SortFamilySet.add_spec in H1 as [->|H1].
      * right. exists x. now split; [apply SortConstraintSet.add_spec;left|right].
      * apply SortFamilySet.add_spec in H1 as [->|H1].
      -- right. exists x. now split; [apply SortConstraintSet.add_spec;left|left].
      -- apply H in H1 as [->|[constraint [H1 H2]]]; [by left|].
        right; exists constraint; (by split; [apply SortConstraintSet.add_spec;right|]).
    + apply fold_add_edges => //.
      apply add_sorts_correct. right;right. apply H. now left.
    + apply fold_add_edges => //.
      apply add_sorts_correct. apply SortConstraintSet.add_spec in H1 as [[[=<-][=<-]]|H1]; [rewrite<- or_assoc; left; apply H2|].
      right;right. apply<- H. right. exists constraint. now split.
Qed.

Lemma constraints_to_set_inc φ1 φ2 : SortConstraintSet.Subset φ1 φ2 ->
  SortFamilySet.Subset (constraints_to_set φ1) (constraints_to_set φ2).
Proof.
  intros H x. repeat rewrite constraints_to_set_correct.
  intros [->|[c [H0 H1]]]; [by left|]. right. exists c.
  split => //. by apply H.
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
    + rewrite (SortConstraintSetProp.fold_add EdgeSet.eq_equiv _ _) => //; [|exact add_edge_compat|exact add_edge_trans].
      apply EdgeSet.add_spec. now apply SortConstraintSet.add_spec in H1 as [[[=H2][=H4]]|H2];
      [left; unfold to_edge; rewrite H2; rewrite H4|right; apply IHconstraints1].
    + apply SortConstraintSet.add_spec.
      apply (SortConstraintSetProp.fold_add EdgeSet.eq_equiv add_edge_compat add_edge_trans) in H1 => //.
      apply EdgeSet.add_spec in H1. destruct H1; [left; inversion H1; by constructor|].
      right. by apply IHconstraints1.
Qed.

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
      by exists x.
  - apply SortFamilySetProp.fold_rec.
    + intros s' H [s [_ H1]]. apply SortFamilySetProp.empty_is_empty_1 in H.
      apply H in H1. inversion H1.
    + intros x a s' s'' H H0 H1%SortFamilySetProp.Add_Equal H2 [s [H3 H4]]. apply EdgeSet.add_spec.
      apply H1 in H4. apply SortFamilySet.add_spec in H4 as [->|H4]; [by left|].
      right. apply H2. by exists s.
Qed.

Section MakeGraph.
  Variable φ : SortConstraintSet.t.

  Definition vertices := constraints_to_set φ.
  Definition edges := remove_self_loops (EdgeSet.union (to_edges φ) (initial_edges vertices)).

  Definition make_graph : sGraph.t := (vertices, edges, SortFamily.sfType).

  Lemma make_graph_no_self_loop: no_self_loop make_graph.
  Proof.
    unfold make_graph. intros e H. cbn in H.
    unfold edges in H.
    destruct (remove_self_loop_correct (EdgeSet.union (to_edges φ) (initial_edges (constraints_to_set φ))) e) as [H0 H1].
    by destruct (H0 H) as [_ H2].
  Qed.

  Lemma make_graph_edges_caract : forall constraint, sGraph.EdgeSet.In constraint.to_edge edges <->
    (constraint.1 <> constraint.2) /\ 
    ((constraint.1 = SortFamily.sfType /\ SortFamilySet.In constraint.2 (constraints_to_set φ)) \/
     SortConstraintSet.In constraint φ).
  Proof.
     intro constraint. split.
    - intro H. split.
      + intro. by apply (make_graph_no_self_loop constraint.to_edge).
      + unfold edges, make_graph in H. cbn in H. unfold edges in H. apply remove_self_loop_correct in H as [H H0].
        apply EdgeSet.union_spec in H. destruct H.
        * right. by apply to_edges_correct.
        * left. destruct constraint. apply initial_edges_correct in H as [s [H H1]]. by inversion H.
    - intros [H [[H0 H1]|H0]]; unfold edges; apply remove_self_loop_correct;
      (split => //); apply EdgeSet.union_spec.
      + right. apply initial_edges_correct. exists constraint.2.
        split => //. destruct constraint. cbn in *. by rewrite H0.
      + left. by apply to_edges_correct.
  Qed.

  Lemma make_graph_edges_are_constraints : forall e,
    EdgeSet.In e edges <-> exists c, e = c.to_edge /\ EdgeSet.In c.to_edge edges.
  Proof.
    intro e. split.
    - intro H. unfold edges in H. apply remove_self_loop_correct in H as [H H0].
      apply EdgeSet.union_spec in H as [H|H].
      + unfold to_edges in H. unfold edges, vertices. induction φ using SortConstraintSetProp.set_induction.
        * rewrite (SortConstraintSet.eq_leibniz (SortConstraintSetProp.empty_is_empty_1 H1)) in H.
          rewrite SortConstraintSetProp.fold_empty in H. inversion H.
        * apply SortConstraintSetProp.Add_Equal in H2. rewrite (SortConstraintSet.eq_leibniz H2) in H.
          apply (SortConstraintSetProp.fold_add EdgeSet.eq_equiv add_edge_compat add_edge_trans) in H => //.
          apply add_edge_correct in H as [H|H]; [exists x|destruct (IHt0_1 H) as [c [H3 H4]]; exists c];
          (split=> //); apply remove_self_loop_correct; [split; [|now rewrite<- H]|split; [|now rewrite<- H3]];
          apply EdgeSet.union_spec. 2: apply remove_self_loop_correct in H4 as [H4 H5];
          apply EdgeSet.union_spec in H4 as [H4%to_edges_correct|[s [H4 H6%constraints_to_set_correct]]%initial_edges_correct].
          1-2: left; apply to_edges_correct; apply H2.
          1: now apply SortConstraintSetFact.add_1.
          1: now apply SortConstraintSetFact.add_2.
          right; apply initial_edges_correct. exists s; split=> //.
          apply constraints_to_set_correct. destruct H6 as [H6|[constraint [H6 H7]]]; [by left|]. right; exists constraint.
          split=> //. apply H2. now apply SortConstraintSetFact.add_2.
      + apply initial_edges_correct in H as [s [H H1]].
        exists (SortFamily.sfType, s). split=> //.
        unfold edges. apply remove_self_loop_correct. split; [|now rewrite<- H].
        apply EdgeSetFact.union_3. now apply initial_edges_correct.
    - now intros [c [[=->] H0]].
  Qed.

  Lemma make_graph_well_formed: invariants make_graph.
  Proof.
    constructor.
    - intros e H. cbn in H. apply make_graph_edges_are_constraints in H as [c [[=->] H]].
      cbn. apply make_graph_edges_caract in H as [_ [[H H0]| H]].
      + split=> //. apply constraints_to_set_correct. by left.
      + by split; apply constraints_to_set_correct; right; exists c; split => //; [left|right].
    - cbn. apply constraints_to_set_correct. now left.
    - cbn. intros x H. constructor.
      + destruct (SortFamily.eq_dec SortFamily.sfType x) as [->|e].
        * exists (paths_refl make_graph x). by constructor.
        * destruct (make_graph_edges_caract (SortFamily.sfType, x)).
          assert (EdgeSet.In (SortFamily.sfType, 1%Z, x) (sGraph.E make_graph));
          [apply H1; cbn; split; [|left; split]|] => //.
          exists (paths_step make_graph SortFamily.sfType x x (1%Z;H2) (paths_refl make_graph x)).
          constructor. cbn. lia.
  Qed.

  Lemma make_graph_positive_path : forall x y (p : Paths make_graph x y),
    (0 <= weight p)%Z.
  Proof.
    intros x y p. induction p => //.
    destruct e as [n He]. cbn in He. have H := He.
    apply make_graph_edges_are_constraints in H as [c [[=H -> H2] _]].
    transitivity (weight p)=> //. rewrite<- (Z.add_0_l (weight p)).
    apply Zplus_le_compat_r => //.
  Qed.

  Lemma is_constraints_graph_acyclic_spec : is_acyclic make_graph <-> acyclic make_graph.
  Proof.
    split.
    - unfold acyclic. intros H x y e p.
      assert (∑ (p' : Paths make_graph x x), 0 < weight p')%Z as [p' H0].
      + exists (paths_step make_graph _ y _ e p).
        cbn. destruct e as [n He]. cbn.
        apply make_graph_edges_are_constraints in He as [c [[= _ -> _] _]].
        rewrite<- (Z.add_0_l 0). apply Zplus_lt_le_compat => //.
        apply make_graph_positive_path.
      + apply (is_acyclic_spec make_graph (HI := make_graph_well_formed)) in H as H'.  
        unfold acyclic_no_loop in H'. now specialize (H' x p').
    - intro H. apply (is_acyclic_spec make_graph (HI := make_graph_well_formed)).
      unfold acyclic, acyclic_no_loop in *. intros x.
      enough (forall x' (p : Paths make_graph x x'), x = x' -> (weight p <= 0)%Z).
      + intro p. apply (H0 x p eq_refl).
      + intros x' p Heq. destruct p => //.
      exfalso. apply (H x y) => //. rewrite Heq => //.
  Qed.

  Lemma topological_sort_constraints_init : {l | topological_sort make_graph = SortFamily.sfType :: l}.
  Proof.
    unfold topological_sort. rewrite topological_sort0_eq.
    assert (SortFamilySet.mem (sGraph.s make_graph) (sGraph.V make_graph) = true) as H.
    + apply SortFamilySetFact.mem_iff. apply constraints_to_set_correct.
      by left.
    + rewrite H. set a0 := fold_left _ _ _. by exists a0.1.
  Qed.

  Lemma topological_sort_constraints_reach x : acyclic make_graph ->
    SortFamilySet.In x vertices ->
    In x (topological_sort make_graph).
  Proof.
    intros H H0. apply (topological_sort_reach _ _ _ SortFamilySet.empty
                    (HI := make_graph_well_formed) (Ha := H)).
    - destruct (SortFamily.eq_dec SortFamily.sfType x) as [<-|H1]; [apply paths_refl|].
      apply (paths_step _ _ x); [|apply paths_refl].
      exists 1%Z. change (_, _, _) with (sGraph.s make_graph, x).to_edge.
      apply make_graph_edges_caract. split => //.
      left. split => //.
    - apply constraints_to_set_correct. by left.
    - apply config_init.
  Qed.

End MakeGraph.

Section Eliminability.
  Variable φ : SortConstraintSet.t.
  Local Definition G := make_graph φ.

  Definition is_eliminable : SortFamily.t -> SortFamily.t -> bool :=
    fun x y => match (sGraph.lsp G x y) with
      | None => false
      | Some n => true
    end.

  Lemma is_eliminable_correct s1 s2 : is_eliminable s1 s2 <->
    ∥ SimplePaths G (sGraph.V G) s1 s2 ∥.
  Proof.
    set path := lsp0 G (sGraph.V G) s1 s2.
    assert (lsp0 G (sGraph.V G) s1 s2 = path) => //.
    clearbody path.
    split.
    - intro. unfold is_eliminable, lsp in H0.
      destruct path as [a|].
      + destruct (lsp0_spec_eq G a H). apply (sq x).
      + rewrite H in H0 => //.
    - intro; inversion H0. unfold is_eliminable, lsp.
      assert (Nbar.le (Some (sweight X)) path). rewrite<- H.
      apply (sGraph.lsp0_spec_le G X).
      rewrite H. induction path => //.
  Qed.

  Lemma is_eliminable_correct' s1 s2 : is_eliminable s1 s2 = true <->
      ∥ sGraph.Paths G s1 s2 ∥.
  Proof.
    destruct (is_eliminable_correct s1 s2).
    split.
    - intro. destruct (H H1). constructor. apply (sGraph.to_paths G X).
    - intro; destruct H1. apply is_eliminable_correct. constructor.
      by apply simplify2'; [exact (make_graph_well_formed φ)|].
  Qed.

  Definition is_impredicative : SortFamily.t -> bool :=
    fun s => is_eliminable SortFamily.sfProp s.
End Eliminability.

Section GlobalConstraints.
  Definition global_sorts :=
    SortFamilySet.add SortFamily.sfType (SortFamilySet.add SortFamily.sfProp
    (SortFamilySet.singleton SortFamily.sfSProp)).

  Definition global_constraints : SortConstraintSet.t := 
    SortConstraintSet.add (SortFamily.sfType, SortFamily.sfProp)
    (SortConstraintSet.singleton (SortFamily.sfProp, SortFamily.sfSProp)).

  Lemma global_constraints_support: SortFamilySet.Equal (constraints_to_set global_constraints) global_sorts.
  Proof.
    unfold SortFamilySet.Equal. intro a.
    rewrite constraints_to_set_correct.
    unfold global_constraints, global_sorts.
    repeat rewrite SortFamilySet.add_spec.
    rewrite SortFamilySet.singleton_spec.
    split.
    - move=> [->|[constraint [H H0]]]; [now left|].
      apply SortConstraintSet.add_spec in H as [H|H].
      + destruct H as [[=<-][=<-]]. destruct H0; [now left|right; now left].
      + apply SortConstraintSet.singleton_spec in H.
        destruct H as [[=<-][=<-]]. now right.
    - intros [H|H]; [now left|]. right. exists (SortFamily.sfProp, SortFamily.sfSProp).
      rewrite SortConstraintSet.add_spec; rewrite SortConstraintSet.singleton_spec. now split ; [right|cbn].
  Qed.

  Definition add_global : SortConstraintSet.t -> SortConstraintSet.t := 
    fun c => SortConstraintSet.union c global_constraints.

  Definition global_graph := make_graph global_constraints.

  Lemma global_sorts_not_variables s : SortFamilySet.In s global_sorts ->
    SortFamily.is_var s = false.
  Proof.
    unfold global_sorts. repeat rewrite SortFamilySet.add_spec.
    rewrite SortFamilySet.singleton_spec.
    intros [->|[->| ->]] => //.
  Qed.

  Definition global_elimination s1 s2 : bool :=
    match s1, s2 with
    | SortFamily.sfVar _, _ | _, SortFamily.sfVar _ => false
    | SortFamily.sfType, _
    | SortFamily.sfProp, (SortFamily.sfProp | SortFamily.sfSProp)
    | SortFamily.sfSProp, SortFamily.sfSProp => true
    | SortFamily.sfGlobal s, SortFamily.sfGlobal s' => (s =? s')%string
    | _, _ => false
    end.

  Lemma global_elimination_correct u1 u2 :
    global_elimination (SortFamily.from_univ u1) (SortFamily.from_univ u2) <->
    globally_eliminable u1 u2.
  Proof.
    by destruct u1, u2.
  Qed.

  Lemma global_elimination_trans y x z :
    global_elimination x y -> global_elimination y z ->
    global_elimination x z.
  Proof.
    destruct x, y, z => //.
    simpl. move=> /eqb_eq -> //.
  Qed.

  Lemma global_graph_correct u1 u2 :
    SortFamilySet.In (SortFamily.from_univ u1) global_sorts ->
    SortFamilySet.In (SortFamily.from_univ u2) global_sorts ->
    is_eliminable global_constraints
      (SortFamily.from_univ u1)
      (SortFamily.from_univ u2) <->
    globally_eliminable u1 u2.
  Proof.
    intros Hu1 Hu2. split.
    - intros H. induction u1, u2 => //.
      apply is_eliminable_correct' in H as [H]. inversion H as [|? ? ? e p H2 H3].
      + apply eqb_refl.
      + destruct (make_graph_well_formed (global_constraints)) as [edges _ _].
        destruct e as [n H1].
        specialize (edges (SortFamily.from_univ (UGlobal s), n, y) H1) as [H4 _].
        unfold make_graph, sGraph.V, vertices in H4. revert H4.
        rewrite (global_constraints_support). unfold global_sorts. cbn.
        repeat rewrite SortFamilySet.add_spec. rewrite SortFamilySet.singleton_spec.
        by intros [|[|]].
    - move=> /global_sort_eliminationP H. induction H => //.
      + apply is_eliminable_correct'. constructor. apply paths_refl.
      + revert Hu2. unfold global_sorts. repeat rewrite SortFamilySet.add_spec.
        rewrite SortFamilySet.singleton_spec. by intros [->|[->| ->]].
  Qed.

End GlobalConstraints.

Section Join.
  Definition upper_bound (v:SortFamily.t) (S:SortFamilySet.t) :=
    SortFamilySet.For_all (fun c => global_elimination c v) S.

  Definition join_bin s1 s2 := match s1, s2 with
    | SortFamily.sfType, _ => Some s2
    | _, SortFamily.sfType => Some s1
    | SortFamily.sfProp, SortFamily.sfSProp 
    | SortFamily.sfSProp, SortFamily.sfProp => Some SortFamily.sfSProp
    | SortFamily.sfSProp, SortFamily.sfSProp => Some SortFamily.sfSProp
    | SortFamily.sfProp, SortFamily.sfProp => Some SortFamily.sfProp
    | SortFamily.sfGlobal u, SortFamily.sfGlobal v => if String.eqb u v then Some s1 else None
    | _, _ => None
  end.

  Definition join S : option SortFamily.t :=
    SortFamilySet.fold 
      (fun s j => match j with | None => None | Some s' => join_bin s s' end)
      S (Some SortFamily.sfType).

  Lemma join_bin_output_global s1 s2 n :
    join_bin s1 s2 = Some n ->
    SortFamily.is_var s1 = false -> SortFamily.is_var s2 = false ->
    SortFamily.is_var n = false.
  Proof.
    destruct s1, s2; try move => // [=<-] //.
    cbn. destruct (_ =? _)%string => // [=<-] //.
  Qed.

  Lemma join_outputs_global S : forall n,
    SortFamilySet.For_all (fun s => SortFamily.is_var s = false) S ->
    join S = Some n -> SortFamily.is_var n = false.
  Proof.
    unfold join. apply SortFamilySetProp.fold_rec_nodep.
    - by intros ? ? [=<-].
    - move=> s1 [s2|] // H H0 n' H1 H2. apply (join_bin_output_global s1 s2) => //.
      + by apply H1.
      + by apply H0.
  Qed.

  Lemma join_bin_bound s1 s2 n : join_bin s1 s2 = Some n ->
    SortFamily.is_var s1 = false -> SortFamily.is_var s2 = false ->
    global_elimination s1 n /\ global_elimination s2 n.
  Proof.
    destruct s1, s2; try move => // [=<-] //;
    unfold global_elimination.
    1-2: by rewrite eqb_refl.
    unfold join_bin.
    destruct (_ =? _)%string eqn: H => // [=<-] //.
    by rewrite eqb_sym eqb_refl.
  Qed.

  Lemma join_bin_trans : transpose eq
    (fun (s : SortFamilySet.elt) (j : option SortFamily.t_) =>
      match j with
      | Some s' => join_bin s s'
      | None => None
      end).
  Proof.
    move => s1 s2 [] // s3.
    destruct s1, s2, s3 => //; unfold join_bin;
      destruct (_ =? _)%string eqn: H => //.
    - rewrite eqb_sym H. apply eqb_eq in H. by rewrite H.
    - by rewrite eqb_sym H.
    - destruct (s =? s1)%string eqn: H1 => //.
      + rewrite eqb_sym. destruct (s0 =? s)%string eqn: H2 => //.
        apply eqb_eq in H2. by rewrite H2.
      + apply eqb_eq in H. by rewrite H H1.
    - destruct (s =? s1)%string eqn: H1 => //. apply eqb_eq in H1.
      by rewrite H1 H.
  Qed.

  Lemma join_bound (S:SortFamilySet.t) : forall n,
    SortFamilySet.For_all (fun s => SortFamily.is_var s = false) S ->
    join S = Some n -> upper_bound n S.
  Proof.
    unfold join. induction S using SortFamilySetProp.set_induction_bis.
    - apply SortFamilySet.eq_leibniz in H. by rewrite<- H.
    - easy.
    - rewrite SortFamilySetProp.fold_add => //.
      + destruct (SortFamilySet.fold _ _ _) eqn: H0 => //.
        intros n HS H1 s [->|H2]%SortFamilySet.add_spec.
        * destruct (join_bin_bound x t0 n) => //.
          -- apply HS. apply SortFamilySet.add_spec. by left.
          -- apply (join_outputs_global S) => //.
             intros s Hs. apply HS. apply SortFamilySet.add_spec. by right.
        * apply (global_elimination_trans t0).
          -- apply IHS => //. intros ? ?. apply HS. apply SortFamilySet.add_spec. by right.
          -- destruct (join_bin_bound x t0 n) => //.
             ++ apply HS. apply SortFamilySet.add_spec. by left.
             ++ apply (join_outputs_global S) => //.
                intros ? Hs. apply HS. apply SortFamilySet.add_spec. by right.
      + apply join_bin_trans.
  Qed.

  Lemma join_bin_univ_prop s1 s2 n :
    join_bin s1 s2 = Some n ->
    SortFamily.is_var s1 = false -> SortFamily.is_var s2 = false ->
    forall v, 
      (global_elimination s1 v -> global_elimination s2 v ->
       global_elimination n v).
  Proof.
    destruct s1, s2; try move => // [=<-] //.
    unfold join_bin. destruct (_ =? _)%string eqn: H => // [=<-] //.
  Qed.

  Lemma join_univ_prop (S:SortFamilySet.t) : forall n,
    join S = Some n ->
    SortFamilySet.For_all (fun s => SortFamily.is_var s = false) S ->
    forall v, (upper_bound v S -> SortFamily.is_var v = false -> global_elimination n v).
  Proof.
    induction S using SortFamilySetProp.set_induction_bis.
    - apply SortFamilySet.eq_leibniz in H. by rewrite<- H.
    - by intros ? [=<-] ? [] ?.
    - unfold join. rewrite SortFamilySetProp.fold_add => //; [|apply join_bin_trans].
      intros n H0 H1 v H2 H3. destruct (SortFamilySet.fold _ _ _) eqn: H4 => //.
      apply (join_bin_univ_prop x t0) => //.
      + apply H1. apply SortFamilySet.add_spec. by left.
      + apply (join_outputs_global S) => //. intros ? ?. apply H1.
        apply SortFamilySet.add_spec. by right.
      + apply H2. apply SortFamilySet.add_spec. by left.
      + apply IHS => //.
        * intros ? ?. apply H1. apply SortFamilySet.add_spec. by right.
        * intros ? ?. apply H2. apply SortFamilySet.add_spec. by right.
  Qed.

  Lemma bounded_join_bin s1 s2 n :
    SortFamily.is_var s1 = false -> SortFamily.is_var s2 = false ->
    global_elimination s1 n -> global_elimination s2 n ->
    exists v, join_bin s1 s2 = Some v.
  Proof.
    destruct s1, s2 => //;
    (try by exists SortFamily.sfType);
    (try by exists SortFamily.sfProp);
    (try by exists SortFamily.sfSProp);
    (try by exists (SortFamily.sfGlobal s));
    (try by destruct n).
    destruct n => //.
    cbn. intros _ _ <-%eqb_eq <-%eqb_eq.
    rewrite eqb_refl.
    by exists (SortFamily.sfGlobal s0).
  Qed.

  Lemma bounded_join (S:SortFamilySet.t) : forall n,
    upper_bound n S ->
    SortFamilySet.For_all (fun s => SortFamily.is_var s = false) S ->
    exists v, join S = Some v.
  Proof.
    induction S using SortFamilySetProp.set_induction_bis.
    - apply SortFamilySet.eq_leibniz in H. by rewrite<- H.
    - by exists SortFamily.sfType.
    - unfold join. rewrite SortFamilySetProp.fold_add => //; [|apply join_bin_trans].
      intros n H0 H1.
      destruct (SortFamilySet.fold _ _ _) eqn: H4.
      + apply (bounded_join_bin x t0 n).
        * apply H1. apply SortFamilySet.add_spec. by left.
        * apply (join_outputs_global S) => //. intros ? ?. apply H1.
          apply SortFamilySet.add_spec. by right.
        * apply H0. apply SortFamilySet.add_spec. by left.
        * apply (join_univ_prop S) => //.
          -- intros ? ?. apply H1. apply SortFamilySet.add_spec. by right.
          -- intros ? ?. apply H0. apply SortFamilySet.add_spec. by right.
          -- assert (global_elimination x n).
             ++ apply H0. apply SortFamilySet.add_spec. by left.
             ++ destruct n, x => //.
      + fold (join S) in H4. destruct (IHS n) as [v H5].
        * intros ? ?. apply H0. apply SortFamilySet.add_spec. by right.
        * intros ? ?. apply H1. apply SortFamilySet.add_spec. by right.
        * by rewrite H4 in H5.
  Qed.

  Lemma join_bin_in s1 s2 s VSet :
    SortFamilySet.Subset global_sorts VSet ->
    SortFamilySet.In s1 VSet ->
    SortFamilySet.In s2 VSet ->
    join_bin s1 s2 = Some s ->
    SortFamilySet.In s VSet.
  Proof.
    intros H H0 H1 H2.
    specialize (H s). unfold global_sorts in H.
    revert H.
    repeat rewrite SortFamilySet.add_spec.
    rewrite SortFamilySet.singleton_spec.
    intro H.
    destruct s1, s2 => //; try injection H2 => <-; (try by apply H0); (try by apply H1).
    simpl in H2. destruct (s0 =? s1)%string => //. by injection H2 => <-.
  Qed.

  Lemma join_in S : forall s VSet,
    join S = Some s->
    SortFamilySet.Subset global_sorts VSet ->
    SortFamilySet.For_all (fun s => SortFamilySet.In s VSet) S ->
    SortFamilySet.In s VSet.
  Proof.
    induction S using SortFamilySetProp.set_induction_bis.
    - by apply SortFamilySet.eq_leibniz in H as ->.
    - intros s VSet [=<-] H ?. apply H. apply SortFamilySet.add_spec.
      by left.
    - unfold join. rewrite SortFamilySetProp.fold_add => //; [|apply join_bin_trans].
      fold (join S). intros s VSet H0 H1 H2. destruct (join S) as [s'|] eqn: H3 => //.
      apply (join_bin_in x s') => //.
      + apply H2. rewrite SortFamilySet.add_spec. by left.
      + apply IHS => //. intros ? ?. apply H2.
        rewrite SortFamilySet.add_spec. by right.
  Qed.

End Join.

Section local_global.
  Lemma make_graph_edges_inc φ φ2 : SortConstraintSet.Subset φ φ2 ->
    EdgeSet.Subset (edges φ) (edges φ2).
  Proof.
    intros H e H0.
    apply make_graph_edges_are_constraints in H0 as [c [-> H0]].
    apply make_graph_edges_caract. apply-> make_graph_edges_caract in H0.
    destruct H0 as [? [[? H1]|?]]; split => //.
    + left. split => //.
      apply constraints_to_set_correct.
      apply constraints_to_set_correct in H1.
      destruct H1 as [?|[c2 [? ?]]].
      - by left.
      - right. exists c2. split => //. by apply H.
    + right. by apply H.
  Qed.

  Lemma local_refines_global φ s1 s2 : global_elimination s1 s2 ->
    SortFamilySet.In s2 (sGraph.V (make_graph (add_global φ))) -> 
    is_eliminable (add_global φ) s1 s2.
  Proof.
    intros H H0. apply is_eliminable_correct'. constructor.
    destruct s1,s2 => //; try apply paths_refl.
    5: {apply eqb_eq in H. rewrite H. apply paths_refl. }
    all: apply: paths_step; [|apply paths_refl].
    all: exists 1%Z.
    1: change (_, _,_) with (SortFamily.sfProp, SortFamily.sfSProp).to_edge.
    2: change (_, _,_) with (SortFamily.sfType, SortFamily.sfProp).to_edge.
    3: change (_, _,_) with (SortFamily.sfType, SortFamily.sfSProp).to_edge.
    4: change (_, _,_) with (SortFamily.sfType, SortFamily.sfGlobal s).to_edge.
    all: apply make_graph_edges_caract.
    all: split => //.
    2-4: by left.
    right.
    rewrite SortConstraintSet.union_spec.
    right.
    repeat rewrite SortConstraintSet.add_spec.
    rewrite SortConstraintSet.singleton_spec.
    by right.
  Qed.

  Lemma composition_local φ s : SortFamilySet.In s (constraints_to_set φ) ->
    {SortFamilySet.In s global_sorts} + {SortFamily.is_var s}.
  Admitted.
End local_global.


Section GoodConstraints.
  Variable (φ: SortConstraintSet.t).
  Definition constraints := add_global φ.
  Definition local_graph := make_graph constraints.
  Definition non_var_sorts := SortFamilySet.filter 
    (fun s => negb (SortFamily.is_var s)) (sGraph.V local_graph).

  Definition respect_constraints s s':=
    (is_eliminable constraints s s') ==> (global_elimination s s').

  Definition global_local_agreement: bool := SortFamilySet.for_all
    (fun s => SortFamilySet.for_all 
      (fun s' => respect_constraints s s') non_var_sorts) non_var_sorts.

  Definition assignment : Set := list (nat × SortFamily.t).
  Definition replace_variables (ρ : assignment) (s : SortFamily.t) : SortFamily.t :=
    match s with
    | SortFamily.sfVar n => match find (fun p => Nat.eqb p.1 n) ρ with
      | None => SortFamily.sfType
      | Some (m, s') => s'
      end
    | _ => s
    end.

  Definition correct_assignment (ρ:assignment) := 
    forallb (fun p => negb (SortFamily.is_var p.2)) ρ.

  Lemma correct_assignment_cons ρ n s : SortFamily.is_var s = false ->
    correct_assignment ρ -> correct_assignment ((n, s)::ρ).
  Proof.
    intros ? ?. apply andb_true_intro. split => //. by apply negb_true_iff.
  Qed.

  Lemma replace_variables_not_variable ρ s : correct_assignment ρ ->
    SortFamily.is_var (replace_variables ρ s) = false.
  Proof.
    destruct s => //. cbn. move=> /forallb_forall H.
    destruct (find _) eqn: H0 => //. apply find_some in H0.
    rewrite (surjective_pairing p). apply negb_true_iff. apply H.
    by destruct H0.
  Qed.

  Lemma join_replace_not_variable ρ s s' : correct_assignment ρ ->
    join (SortFamilySetProp.of_list
      (map (replace_variables ρ) (pred local_graph s))) = Some s' ->
    SortFamily.is_var s' = false.
  Proof.
    move=> H0 /join_outputs_global H. apply H.
    move=> s0 /SortFamilySetProp.of_list_1 /InA_alt [y [-> /in_map_iff [x [<- _]]]].
    by apply replace_variables_not_variable.
  Qed.

  Definition to_univ' s : universe_family :=
    match s with
    | SortFamily.sfType | SortFamily.sfVar _ => UType
    | SortFamily.sfProp => UProp
    | SortFamily.sfSProp => USProp
    | SortFamily.sfGlobal x => UGlobal x
    end.

  Lemma from_to_univ u : to_univ' (SortFamily.from_univ u) = u.
  Proof.
    by destruct u.
  Qed.

  Definition find_assignment ρ n : universe_family :=
    match find (fun p => Nat.eqb p.1 n) ρ with
    | None => UType
    | Some (m, s) => to_univ' s
    end.

  Definition join_preds ρ s := join (SortFamilySetProp.of_list
    (map (fun s => SortFamily.from_univ (SortFamily.sort_val
        (Build_valuation (fun _ => xH) (fun _ => 0) (find_assignment ρ)) s))
      (pred local_graph s))).

  Fixpoint assign_variables (ρ: assignment) (vertices: list SortFamily.t): option assignment :=
    match vertices with
    | [] => Some ρ
    | sort :: l => match sort with
      | SortFamily.sfVar n => 
        let preds := map (replace_variables ρ) (pred local_graph (sort)) in
        match join (SortFamilySetProp.of_list preds) with
        | None => None
        | Some sort => assign_variables ((n, sort)::ρ) l
        end
      | _ => assign_variables ρ l
      end
    end.

  Lemma assign_variables_input ρ1 l ρ : assign_variables ρ1 l = Some ρ ->
    exists ρ2, ρ = ρ2 ++ ρ1.
  Proof.
    elim: l ρ1 ρ.
    - intros ? ? [=->]. by exists [].
    - intros a l IHl ρ1 ρ. simpl. destruct a as [| | | |n]; try apply IHl.
      set join_pred := join _. destruct join_pred as [t|] => //.
      intro H. destruct (IHl ((n, t)::ρ1) ρ H) as [ρ2 H0].
      exists (ρ2 ++ [(n, t)]). by rewrite<- app_assoc.
  Qed.

  Lemma assign_variables_app l1 : forall l2 ρ ρ',
    assign_variables ρ l1 = Some ρ' ->
    assign_variables ρ (l1 ++ l2) = assign_variables ρ' l2.
  Proof.
    induction l1.
    + by intros ? ? ? [=->].
    + intros l2 ρ ρ'. rewrite<- app_comm_cons. simpl.
      destruct a as [| | | |n]; try apply IHl1.
      set join_pred := join _. destruct join_pred as [t|] => //.
      apply IHl1.
  Qed.

  Lemma assign_variables_app_progress l1 : forall l2 ρ,
    assign_variables ρ l1 = None ->
    assign_variables ρ (l1 ++ l2) = None.
  Proof.
    induction l1 => //.
    intros l2 ρ H. rewrite<- app_comm_cons. simpl.
    destruct a as [| | | |n]; try apply IHl1 => //.
    destruct (join _) eqn: H0 => //. apply IHl1.
    simpl in H. by rewrite H0 in H.
  Qed.

  (*
  Lemma assign_variables_variable n l ρ l' :
    assign_variables ρ (SortFamily.sfVar n :: l) = Some l' ->
    exists s, In (n, s) l' /\ SortFamily.is_var s = false.
  Proof.
    simpl. destruct (join _) as [s|] eqn: H => //.
    intro H0. exists s. split; [|apply global_sorts_not_variables; apply: join_outputs_global; exact H].
    destruct (assign_variables_input ((n, s)::ρ) l l' H0) as [? ->].
    apply in_or_app. right. apply in_eq.
  Qed.*)

  Lemma assign_variables_not_in l : forall l1 l2 n, ~ In (SortFamily.sfVar n) l ->
    assign_variables l1 l = Some (l2 ++ l1) ->
    forall s, ~ InA (fun p q => p.1 = q.1) (n, s) l2.
  Proof.
    induction l.
    - intros ? ? ? ? [=H] ?. rewrite<- (app_nil_l l1) in H.
      rewrite app_assoc in H. apply app_inv_tail in H.
      rewrite app_nil_r in H. rewrite<- H. by rewrite InA_nil.
    - intros l1 l2 n H H0 s.
      destruct a as [| | | |n0]. 1-4: by apply (IHl l1) => // ?; apply H; right.
      simpl in H0. destruct (join _) as [s'|] => //.
      destruct (assign_variables_input _ _ _ H0) as [l' H1].
      rewrite H1 in H0. assert ((n0, s') :: l1 = [(n0, s')] ++ l1) as H2 => //.
      rewrite H2 in H1. rewrite app_assoc in H1. apply app_inv_tail in H1.
      rewrite H1. rewrite InA_app_iff. intros [H3|H3].
      + refine (IHl _ _ _ _ H0 s H3). intro. apply H. by right.
      + apply H. left. apply InA_singleton in H3. cbn in H3. by rewrite H3.
  Qed.

  Lemma assign_variables_nodup l : forall ρ l' n s, NoDup l ->
    correct_assignment l' ->
    assign_variables l' l = Some ρ ->
    In (n, s) ρ -> ~ InA (fun p q => p.1 = q.1) (n, s) l' ->
    SortFamily.from_univ (find_assignment ρ n) = s.
  Proof.
    induction l.
    - intros ? ? ? ? ? ? [=<-] ? H2. exfalso. apply H2. apply InA_alt.
      by exists (n, s).
    - intros ρ l' n s H Hl' H1 H2 H3. depelim H.
      destruct a as [| | | |n']; try by apply (IHl _ l').
      destruct (Nat.eq_dec n n') as [<-|H4].
      + simpl in H1. destruct (join _) as [s'|] eqn: H6 => //.
        destruct (assign_variables_input _ _ _ H1) as [l1 ->].
        unfold find_assignment. apply in_app_or in H2 as [H2|[H2|H2]].
        * exfalso. refine (assign_variables_not_in l _ _ _ H H1 s _).
          apply InA_alt. by exists (n, s).
        * destruct (find _ _) as [u|] eqn: H4.
          -- apply find_some in H4 as [[H4|[H4|H4]]%in_app_or H5].
            ++ exfalso. refine (assign_variables_not_in l _ _ _ H H1 u.2 _).
               apply InA_alt. exists u. split => //. by apply beq_nat_true in H5.
            ++ injection H2 => <-. rewrite<- H4. destruct s' => //.
               by apply join_replace_not_variable in H6.
            ++ exfalso. apply H3. apply InA_alt. exists u. split => //.
               by apply beq_nat_true in H5.
          -- specialize (find_none _ _ H4) => H5.
             specialize (H5 (n, s')). cbn in H5. rewrite<- beq_nat_refl in H5.
             assert (In (n, s') (l1 ++ (n, s')::l')) as H7; [apply in_or_app; right; by left|].
             specialize (H5 H7). discriminate.
        * exfalso. apply H3. apply InA_alt. by exists (n, s).
      + simpl in H1. destruct (join _) as [s'|] eqn: H5 => //.
        apply (IHl _ ((n', s')::l')) => //.
        1: {apply correct_assignment_cons => //.
            apply (join_replace_not_variable _ _ _ Hl' H5). }
        intros [y [[=H7] H8]]%InA_alt.
        destruct H8.
        * apply H4. rewrite<- H6 in H7. apply H7.
        * apply H3. apply InA_alt. by exists y.
  Qed.

  Lemma assign_variables_nodupA l ρ : NoDup l ->
    assign_variables [] l = Some ρ ->
    NoDupA (fun p q => p.1 = q.1) ρ.
  Proof.
    assert (NoDupA (fun p q => p.1 = q.1) [] (A := nat × SortFamily.t)) as H => //.
    assert (correct_assignment []) as H0 => //.
    assert (forall n s, In (SortFamily.sfVar n) l -> 
            ~ InA (fun p q : nat × SortFamily.t => p.1 = q.1) (n, s) []) as H1.
    1: {intros. by rewrite InA_nil. }
    elim: l ρ [] H H0 H1.
    - intros ? ? ? ? ? ? [=<-] => //.
    - intros a l IHl ρ l' H H0 H1 H2 H4. depelim H2.
      destruct a as [| | | |n].
      1-4: apply (IHl _ l') => //; intros; apply H1; by apply in_cons.
      simpl in H4. destruct (join _) as [s|] eqn: H5 => //.
      apply (IHl _ ((n,s)::l')) => //.
      + constructor => //. apply H1. apply in_eq.
      + apply correct_assignment_cons => //.
        apply: join_outputs_global; [|exact H5].
        intros s0 H6. apply-> SortFamilySetProp.of_list_1 in H6.
        apply InA_alt in H6 as [s' [<- H6]].
        apply in_map_iff in H6 as [x [<- H6]].
        by apply replace_variables_not_variable.
      + intros n' s' H6 H7. destruct (Nat.eq_dec n n') as [->|H8].
        * by apply H2.
        * apply InA_cons in H7. destruct H7.
          -- by apply H8.
          -- apply: H1; [|exact H7]. by apply in_cons.
  Qed.

  Lemma correct_assignment_no_variables l : forall n ρ,
    NoDup l ->
    assign_variables [] l = Some ρ ->
    SortFamily.from_univ (find_assignment ρ n) = replace_variables ρ (SortFamily.sfVar n).
  Proof.
    intros n ρ H0 H1.
    assert (forall n, SortFamily.from_univ (find_assignment [] n) = replace_variables [] (SortFamily.sfVar n)) as H => //.
    assert (forall (s:SortFamily.t), ~InA (fun p q => p.1 = q.1) (n, s) []) as H2; [intros; by rewrite InA_nil|].
    assert (correct_assignment []) => //.
    elim: l [] n ρ H H0 H1 H2 H3.
    - intros l' n ρ Hd H H0 H1 H2. simpl in H0. by injection H0 => <-.
    - intros a l IHl l' n ρ H Hd H0 H1 Hl'. depelim Hd. destruct a as [| | | |n0]; try by apply (IHl l').
      have H1' := H1. simpl in H1. destruct (join _ ) as [s|] eqn: H3 => //.
      destruct (Nat.eq_dec n n0) as [->|H4].
      + destruct (assign_variables_input _ _ _ H1) as [ρ2 H4].
        rewrite (assign_variables_nodup _ _ _ _ s _ Hl' H1') => //.
        * by constructor.
        * rewrite H4. apply in_or_app. right. apply in_eq.
        * unfold replace_variables. destruct (find _ _) as [p|] eqn: H5.
          -- apply find_some in H5. rewrite H4 in H5.
             destruct H5 as [[H5|[<-|H5]]%in_app_or H6] => //.
             ++ exfalso. rewrite H4 in H1.
                apply: (assign_variables_not_in _ _ _ _ H0 H1 s).
                apply InA_alt. exists p. split => //. simpl.
                by rewrite (beq_nat_true _ _ H6).
             ++ exfalso. apply (H2 s). apply InA_alt. exists p.
                by rewrite (beq_nat_true _ _ H6).
          -- specialize (find_none _ _ H5 (n0,s)) as H6.
             exfalso. apply (eq_true_false_abs ((fun p => p.1 =? n0) (n0,s))).
             ++ by rewrite (beq_nat_refl n0).
             ++ apply H6. rewrite H4. apply in_or_app. right. apply in_eq.
      + apply (IHl ((n0,s)::l')) => //.
        * intro n1. unfold find_assignment. cbn.
          apply join_replace_not_variable in H3 => //.
          destruct (n0 =? n1).
          -- by destruct s.
          -- apply H.
        * intros s' H5. apply InA_alt in H5 as [y [H5 [H6|H6]]].
          -- rewrite<- H6 in H5. by apply H4.
          -- apply (H2 s'). apply InA_alt. by exists y.
        * apply correct_assignment_cons => //.
          apply (join_replace_not_variable _ _ _ Hl' H3).
  Qed.


  Lemma map_ext {A B : Type} (f g : A -> B) l : (forall x, In x l -> (f x) = (g x)) ->
    map f l = map g l.
  Proof.
    induction l => //.
    intro H. simpl. rewrite IHl.
    - intros x H0. apply H. by apply in_cons.
    - rewrite (H a) => //. apply in_eq.
  Qed.

  Lemma nodup_app_in_l {A : Type} (x : A) l1 l2 : In x l1 -> NoDup (l1 ++ l2) ->
    ~ In x l2.
  Proof.
    intros H H0.
    apply in_split in H as [l3 [l4 ->]].
    rewrite<- app_assoc, <-app_comm_cons in H0.
    have H1 := NoDup_remove_2 _ _ _ H0.
    intro H2. apply H1. apply in_or_app. right. apply in_or_app. by right.
  Qed.

  Lemma nodup_app_l {A : Type} (l1 l2 : list A) : NoDup (l1 ++ l2) ->
    NoDup l1.
  Proof.
    intro H. induction l1.
    - constructor.
    - rewrite<- app_comm_cons in H. depelim H. constructor.
      + intros ?. apply H. apply in_or_app. by left.
      + by apply IHl1.
  Qed.

  Lemma assign_variables_eq ρ n {Ha : acyclic local_graph} :
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    In (SortFamily.sfVar n) (topological_sort local_graph) ->
    exists s, join_preds ρ (SortFamily.sfVar n) = Some s /\ 
      In (n, s) ρ.
  Proof.
    destruct (topological_sort_constraints_init constraints) as [l H].
    rewrite H.
    assert (exists l0, assign_variables [] (SortFamily.sfType :: []) = Some l0) as [l0 H0];
      [by exists []|].
    assert (is_topo_sorted local_graph (SortFamily.sfType :: l)) as H1.
    - apply is_topo_sorted_alt. intros x y l1 l2 H2. 
      apply (topological_sort_spec local_graph x l1 l2 (HI := make_graph_well_formed constraints) (Ha := Ha)).
      etransitivity; [exact H|exact H2].
    - assert (forall n, In (SortFamily.sfVar n) [SortFamily.sfType] ->
      exists s, join_preds ρ (SortFamily.sfVar n) = Some s /\
        In (n, s) ρ) as H3; [intros ? [] => //|].
      assert (l = [] ++ l) as H2 => //.
      assert (NoDup (SortFamily.sfType :: l)) as H4; 
        [rewrite<- H; apply topological_sort_nodup|].
      assert (forall x, SortFamilySet.In x (sGraph.V local_graph) -> In x (SortFamily.sfType :: l)) as H7;
        [intros; rewrite<- H; by apply topological_sort_constraints_reach|].
      move=> H5 H6.
      move: l0 ρ {H} H0 H1 H3 H5 H6 H4 H7. rewrite H2. elim: l ([]: list SortFamily.t_) {H2}.
      + intros l l' ρ H H0 H1 H2 H3 H4 H5. rewrite app_nil_r in H3.
        by apply H1.
      + intros a l IHl l0 l1 ρ H H0 H1 H2 H3 H4 HIn.
        rewrite app_comm_cons in H2 H3. rewrite (assign_variables_app _ _ _ l1) in H2 => //.
        apply in_app_or in H3 as [H3|H3];
          [destruct (H1 n H3) as [s [? ?]]; exists s; by split|].
        assert (SortFamily.sfType :: l0 ++ a :: l = (SortFamily.sfType :: l0 ++ [a]) ++ l) as H5;
            [rewrite<- app_comm_cons; by rewrite<- app_assoc|].
          destruct (assign_variables [] (SortFamily.sfType :: l0 ++ [a])) as [l2|] eqn: H6.
          2: {have H7 := (assign_variables_app_progress _ l _ H6).
              rewrite- H5 in H7. rewrite app_comm_cons in H7.
              rewrite (assign_variables_app _ _ _ _ H) in H7. rewrite H2 in H7.
              discriminate. }
          apply (IHl (l0 ++ [a]) l2) => //. 5-6: by rewrite<- app_assoc.
          * rewrite app_comm_cons. by rewrite<- H5.
          * rewrite app_comm_cons.
            rewrite app_comm_cons (assign_variables_app _ _ _ _ H) in H6.
            destruct (assign_variables_input _ _ _ H6) as [l3 ->].
            intros n' [H7|H7]%in_app_or.
            ++ destruct (H1 n' H7) as [s [? ?]]. by exists s.
            ++ destruct H7 as [->|?] => //. simpl in H6. destruct (join _) as [s|] eqn: H7 => //.
               exists s. have H2' := H2. simpl in H2. rewrite H7 in H2.
               destruct (assign_variables_input _ _ _ H2) as [l2 H8].
               split.
               ** rewrite<- H7. unfold join_preds.
                  set ma := map _ _.
                  set mb := map _ _.
                  assert (ma = mb) as H9; [|by rewrite H9].
                  unfold ma, mb. apply map_ext. intros x H9.
                  destruct x as [| | | |n0] => //. cbn -[replace_variables].
                  assert (In (SortFamily.sfVar n0) (SortFamily.sfType::l0)).
                  -- apply pred_spec_1 in H9. rewrite app_comm_cons in H4.
                     specialize (is_topo_sorted_pred local_graph _ H4 H0) as H10.
                     destruct (H10 (SortFamily.sfVar n0) (SortFamily.sfVar n')
                      (SortFamily.sfType :: l0) l) as [H11|H11] => //.
                      +++ apply HIn. destruct (make_graph_well_formed constraints) as [H11 _ _].
                          destruct H9 as [? H9]. by destruct (H11 (SortFamily.sfVar n0,x,SortFamily.sfVar n')).
                      +++ by apply: paths_step; [|apply paths_refl].
                      +++ exfalso. rewrite H11 in H9.
                          by apply (Ha (SortFamily.sfVar n') (SortFamily.sfVar n'));
                            [|apply paths_refl].
                  -- transitivity (SortFamily.from_univ (find_assignment l1 n0)).
                     2:{refine (correct_assignment_no_variables _ _ _ _ H).
                        rewrite app_comm_cons in H4.
                        apply (nodup_app_l _ _ H4). }
                     destruct (H1 n0 H10) as [s0 [H11 H12]].
                     rewrite<- (assign_variables_app _ _ _ _ H) in H2'.
                     rewrite (assign_variables_nodup _ _ _ _ _ H4 _ H2' H12)=> // ; [by rewrite InA_nil|].
                     rewrite<- (app_nil_l l1) in H8. rewrite app_comm_cons in H8.
                     rewrite app_assoc in H8. rewrite H8 in H2'.
                     rewrite (assign_variables_app _ _ _ _ H) in H2'.
                     have H16 := nodup_app_in_l _ _ _ H10 H4.
                     have H17 := assign_variables_not_in _ _ _ _ H16 H2' s0.
                     rewrite H8 in H12.
                     apply in_app_or in H12 as [H12|H12].
                     1: {by exfalso; apply H17; apply InA_alt; exists (n0, s0). }
                     assert (NoDup (SortFamily.sfType :: l0)) as H18; [rewrite app_comm_cons in H4; apply: nodup_app_l; eassumption|].
                     by rewrite (assign_variables_nodup _ _ _ _ _ H18 _ H H12) => //; rewrite InA_nil.
               ** rewrite H8. apply in_or_app. right. apply in_eq.
          * rewrite<- app_assoc. rewrite app_comm_cons.
            by rewrite (assign_variables_app _ _ _ l1).
          * apply in_cons. apply in_or_app. destruct H3 as [->|H3].
            ++ left. apply in_or_app. right. apply in_eq.
            ++ by right.
  Qed.

  Lemma assign_variables_inv l ρ n s :
    assign_variables [] l = Some ρ ->
    In (n, s) ρ ->
    In (SortFamily.sfVar n) l.
  Proof.
    assert (~InA (fun p q => p.1 = q.1) (n, s) []);
      [by rewrite InA_nil|].
    move: [] H.
    induction l.
    - intros ? H [=<-] H1. exfalso. apply H. apply InA_alt. by exists (n, s).
    - intros l' H H0 H1.
      destruct a as [| | | |n']; try by (intros; apply in_cons; apply (IHl l')).
      destruct (Nat.eq_dec n n') as [->|H2]; [apply in_eq|].
      simpl in H0. destruct (join _) as [s'|] eqn: H3 => //.
      apply in_cons.
      apply (IHl ((n', s')::l')) => //.
      intros [H4|H4]%InA_cons.
      + by apply H2.
      + by apply H.
  Qed.

  Lemma assign_variables_output_universes {Ha : acyclic local_graph} n ρ :
    (assign_variables [] (topological_sort local_graph)) = Some ρ ->
    In (SortFamily.sfVar n) (topological_sort local_graph) ->
    exists s, In (n, s) ρ /\ SortFamily.is_var s = false.
  Proof.
    intros.
    destruct (assign_variables_eq ρ n (Ha := Ha)) as [s [H1 H2]] => //.
    apply join_outputs_global in H1; [by exists s|].
    move=> ? /SortFamilySetProp.of_list_1 /InA_alt [y [-> /in_map_iff [x [<- H3]]]].
    destruct x => //. cbn. destruct (find_assignment _ _) => //.
  Qed.

  Lemma NoDupA_alt {A : Type} {eqA : A -> A -> Prop} 
    (eqA_equiv : Equivalence eqA) l : forall x y,
    NoDupA eqA l -> In x l -> In y l -> eqA x y -> x = y.
  Proof.
    induction l => //.
    intros x y H H1 H2 H3. depelim H.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    - by rewrite<- H1.
    - exfalso. apply H. apply InA_alt. rewrite H1. by exists y.
    - exfalso. apply H. apply InA_alt. rewrite H2. destruct eqA_equiv as [_ Hsym _].
      apply Hsym in H3. by exists x.
    - by apply IHl.
  Qed.

  Lemma assign_variables_in ρ n s {Ha : acyclic local_graph} :
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    In (n, s) ρ -> SortFamilySet.In s (sGraph.V local_graph).
  Proof.
    assert (forall s, In s (topological_sort local_graph) -> SortFamilySet.In s (sGraph.V local_graph)) as H;
      [apply topological_sort_in_graph => //; apply make_graph_well_formed|].
    assert (is_topo_sorted local_graph (topological_sort local_graph)) as H0;
      [apply topological_sort_sorted => //; apply make_graph_well_formed|].
    assert (forall n s, In (SortFamily.sfVar n) [] -> In (n, s) ρ ->
            SortFamilySet.In s (sGraph.V local_graph)) as H2 => //.
    assert (exists l, assign_variables [] [] = Some l) as [l0 H1];
      [by exists []|].
    assert (NoDup (topological_sort local_graph)) as H3; [apply topological_sort_nodup|].
    rewrite<- (app_nil_l (topological_sort local_graph)) in H,H0,H3|-*.
    elim: (topological_sort local_graph) ([]:list SortFamily.t) l0 H1 n s H3 H H0 H2.
    + simpl. move=> l l0 Hl0 n s Hl H H0 H1 H2 H3. apply (H1 n s) => //.
      rewrite app_nil_r in H2.
      by apply (assign_variables_inv _ _ _ s H2).
    + intros a l IHl l' l0 Hl0 n s Hl H H0 H1 H2 H3.
      assert (l' ++ a :: l = (l' ++ [a]) ++ l) as H4;
        [rewrite<- app_assoc; by rewrite<- app_comm_cons|].
      rewrite H4 in H,H0,H2,Hl.
      have H5 := assign_variables_app l' [a] [] l0 Hl0.
      destruct a as [| | | |n'].
      1-4: simpl in H5; apply (IHl _ _ H5 n s) => //; intros n0 ? H6 ?;
        apply (H1 n0) => //; apply in_app_or in H6 as [H6|H6] => //;
        simpl in H6; destruct H6 => //.
      simpl in H5. destruct (join _) as [s'|] eqn: H6 => //.
      2: {apply (assign_variables_app_progress _ l) in H5. by rewrite H5 in H2. }
      apply (IHl _ _ H5 n s) => //.
      intros n0 s0 [H7|H7]%in_app_or H8; [by apply (H1 n0)|].
      destruct H7 as [[=<-]|H7] => //. have H7 := assign_variables_nodupA _ _ Hl H2.
      have H9 := (NoDupA_alt _ _ _ _ H7).
      rewrite (assign_variables_app _ _ _ _ H5) in H2.
      destruct (assign_variables_input _ _ _ H2) as [l1 H10].
      specialize (fun a b => H9 a (n', s') (n', s0) b H8 eq_refl).
      injection H9.
      * move=> <-. apply (join_in _ _ _ H6).
        -- move=> x Hx. apply constraints_to_set_correct. unfold global_sorts in Hx.
           move: Hx. repeat rewrite SortFamilySet.add_spec.
           rewrite SortFamilySet.singleton_spec. intros [->|[->| ->]].
           ++ by left.
           ++ right. exists (SortFamily.sfProp, SortFamily.sfSProp).
              split; [|by left]. apply SortConstraintSet.union_spec. right.
              repeat (apply SortConstraintSet.add_spec; right).
              by apply SortConstraintSet.singleton_spec.
           ++ right. exists (SortFamily.sfProp, SortFamily.sfSProp).
              split; [|by right]. apply SortConstraintSet.union_spec. right.
              repeat (apply SortConstraintSet.add_spec; right).
              by apply SortConstraintSet.singleton_spec.
        -- move=> x /SortFamilySetProp.of_list_1 /InA_alt [? [<- /in_map_iff [y [H11 /pred_spec_1 H12]]]].
           destruct (make_graph_well_formed constraints) as [He _ _].
           destruct H12 as [e H12]. specialize (He _ H12) as [He _].
           destruct y as [| | | |n0]; try (by rewrite<- H11).
           cbn in H11. destruct (find _ _) as [p|] eqn: H13;
             [|rewrite<- H11; apply constraints_to_set_correct; by left].
           apply find_some in H13. apply (H1 p.1).
           ++ apply (assign_variables_inv _ l0 _ p.2) => //. destruct H13.
              by rewrite<- (surjective_pairing p).
           ++ rewrite H10. apply in_or_app. right. apply in_cons.
              rewrite<- H11. by destruct p, H13.
      * easy.
      * rewrite H10. apply in_or_app. right. apply in_eq.
  Qed.

  Definition ancestor_sorts n := (SortFamilySet.filter
      (fun s => is_eliminable constraints s (SortFamily.sfVar n)) non_var_sorts).

  Lemma join_preds_elim ρ n s :
    acyclic local_graph ->
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    In (SortFamily.sfVar n) (topological_sort local_graph) ->
    join_preds ρ (SortFamily.sfVar n) = Some s ->
    upper_bound s (ancestor_sorts n).
  Proof.
    intros Ha.
    assert (is_topo_sorted local_graph (topological_sort local_graph)) as H; 
      [apply topological_sort_sorted=> //;apply make_graph_well_formed|].
    assert (forall s, SortFamilySet.In s (sGraph.V local_graph) -> In s (topological_sort local_graph)) as H0;
      [intro s0;by apply topological_sort_constraints_reach|].
    assert (exists l, assign_variables [] [] = Some l) as [l0 H2]; [by exists []|].
    assert (forall n' s', In (SortFamily.sfVar n') [] -> join_preds ρ (SortFamily.sfVar n') = Some s' ->
      upper_bound s' (ancestor_sorts n')) as H1 => //.
    move: l0 H2 H H0 H1.
    rewrite<- (app_nil_l (topological_sort local_graph)).
    elim: (topological_sort local_graph) ([]: list SortFamily.t).
    - intros ? ? ? ? ? ? ? []%in_app_or => //. easy.
    - intros a l IHl l' l0 H H0 H1 H2 H3 H4 H5.
      assert (l' ++ a :: l = (l' ++ [a]) ++ l) as H6;
        [rewrite<- app_assoc; by rewrite<- app_comm_cons|].
      have H7 := assign_variables_app l' [a] [] l0 H.
      rewrite H6 in H0,H1,H3,H4.
      destruct a as [| | |str|n'].
      all: simpl in H7.
      5: destruct (join _) as [s'|] eqn: H9 => //;
        [|by rewrite assign_variables_app_progress in H3].
      all: apply (IHl _ _ H7) => //.
      all: intros n0 s0 [H8|[[=<-]|]]%in_app_or => //.
      1-5: by apply H2.
      move=> H8 x /SortFamilySet.filter_spec.
      move=> [/SortFamilySet.filter_spec [H10 H11] /is_eliminable_correct' [H12]].
      assert (x <> SortFamily.sfVar n') as H13;
        [by intros ->|].
      apply path_last_edge in H12 => //.

  Lemma assign_variables_elim_gather ρ n : acyclic local_graph ->
    global_local_agreement ->
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    join_preds ρ (SortFamily.sfVar n) =  join (SortFamilySet.filter 
      (fun s => is_eliminable constraints s (SortFamily.sfVar n)) non_var_sorts).
  Proof.
    intros Ha Hl Hρ. unfold join_preds.
    set S1 := SortFamilySetProp.of_list _.
    set S2 := SortFamilySet.filter _ _.
    destruct (join S1) as [s1|] eqn: H; destruct (join S2) as [s2|] eqn: H0 => //.
    - assert (upper_bound s1 S2); [|assert (upper_bound s2 S1)].
      + intros x H1. apply SortFamilySet.filter_spec in H1 as [H1 H2]; [|by intros ? ? <-].
        apply is_eliminable_correct' in H2 as [H2].
        apply SortFamilySet.filter_spec in H1 as [H1 Hx]; [|by intros ? ? <-].
        apply path_last_edge in H2 as [z [p e]]; [|by intros ->].
        induction p.
        * apply: join_bound; [|exact H|].
          -- move=> ? /SortFamilySetProp.of_list_1 /InA_alt [? [<- /in_map_iff [x1 [<- ?]]]].
             elim: (SortFamily.sort_val _ _) => //.
          -- apply SortFamilySetProp.of_list_1. apply InA_alt.
             exists x. split => //. apply in_map_iff. exists x.
             split; [|by apply pred_spec_2]. by destruct x.
        * destruct (make_graph_well_formed constraints) as [He _ _].
          specialize (He _ e0.π2) as [_ Hy].
          destruct (SortFamily.is_var y) eqn: H2.
          -- destruct y as [| | | |n'] => //.
             destruct (assign_variables_eq ρ n' (Ha := Ha)) as [s [H3 H4]] => //;
              [by apply topological_sort_constraints_reach|].

    enough (global_elimination (join S1) (join S2) /\ global_elimination (join S2) (join S1)).

  Lemma assign_variables_elim_compat n tgt ρ :
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    In (SortFamily.sfVar n) (topological_sort local_graph) ->
    is_eliminable constraints (SortFamily.sfVar n) tgt ->
    SortFamily.is_var tgt = false -> global_local_agreement ->
    upper_bound tgt (SortFamilySetProp.of_list 
      (map (replace_variables ρ) (pred local_graph (SortFamily.sfVar n)))).
  Proof.
    assert (forall n, In (SortFamily.sfVar n) [] -> upper_bound tgt
      (SortFamilySetProp.of_list (map (replace_variables ρ)
        (pred local_graph (SortFamily.sfVar n))))) as H => //.
    have H1 := app_nil_l (topological_sort local_graph).
    rewrite<- H1.
    assert (exists l, assign_variables [] [] = Some l) as [l0 H3]; [by exists []|].
    intros H4 H5 H6 Htgt Ha.
    set top := topological_sort local_graph. fold top in H1. unfold top in H1 at 1.
    elim: (topological_sort local_graph) ([]: list SortFamily.t) l0 H3 H1 n H H4 H5 H6.
    - intros ? ?. rewrite app_nil_r. easy.
    - intros a l IHl l' l0 H H0 n H1 H2 H3 H4 s H5.
      assert (l' ++ a :: l = (l' ++ [a]) ++ l) as H6;
        [rewrite<- app_assoc; by rewrite<- app_comm_cons|].
      have H7 := assign_variables_app l' [a] [] l0 H.
      rewrite H6 in H0,H2,H3.
      destruct a as [| | | |n'].
      5: simpl in H7.
      5: destruct (join _) as [s'|] eqn: H9 => //;
        [|by rewrite assign_variables_app_progress in H2].
      all: apply: (IHl _ _ H7 _ n) => //.
      all: intros n0 [H8|[[=<-]|]]%in_app_or => //.
      1-5: by apply H1.
      

(*
  Lemma assign_variables_elim_compat n ρ :
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    In (SortFamily.sfVar n) (topological_sort local_graph) ->
    is_eliminable constraints (SortFamily.from_univ (find_assignment ρ n)) (SortFamily.sfVar n).
  Proof.
    intros H H0.
    assert (forall n, In (SortFamily.sfVar n) [] ->
      is_eliminable constraints 
        (SortFamily.from_univ (find_assignment ρ n)) 
        (SortFamily.sfVar n)) as H1 => //.
    have H2 := app_nil_l (topological_sort local_graph).
    rewrite<- H2 in H,H0.
    assert (exists l, assign_variables [] [] = Some l) as [l0 H3]; [by exists []|].
    set top := topological_sort local_graph. fold top in H2. unfold top in H2 at 1.
    elim: (topological_sort local_graph) ([]:list SortFamily.t) l0 H3 H n H0 H1 H2.
    - intros ? ?. rewrite app_nil_r. easy.
    - intros a l IHl l' l0 H H0 n H1 H2 H3.
      assert (l' ++ a :: l = (l' ++ [a]) ++ l) as H4;
        [rewrite<- app_assoc; by rewrite<- app_comm_cons|].
      have H5 := assign_variables_app l' [a] [] l0 H.
      destruct a as [| | | |n'].
      1-4: rewrite H4 in H0,H1,H3.
      1-4: apply (IHl _ _ H5) => //.
      1-4: intros n0 [H6|[]]%in_app_or => //.
      1-4: by apply H2.
      apply in_app_or in H1 as [H1|H1];
        [by apply H2|].
      destruct H1 as [[=->]|H1].
      + have H0' := (assign_variables_app _ (SortFamily.sfVar n::l) _ _ H).
        rewrite H0 in H0'.
        simpl in H0',H5. destruct (join _) as [s|] eqn: H6 => //.
        destruct (assign_variables_input _ _ _ (eq_sym H0')) as [l1 H1].
        rewrite (assign_variables_nodup _ ρ _ n s _ _ H0) => //.
        * rewrite H3. apply topological_sort_nodup.
        * rewrite H1. apply in_or_app. right. apply in_eq.
        * by rewrite InA_nil.
        * 

  Lemma assign_to_global ρ s : is_acyclic local_graph ->
    assign_variables [] (topological_sort local_graph) = Some ρ ->
    SortFamilySet.In s (constraints_to_set φ) ->
    SortFamilySet.In (SortFamily.from_univ 
      (SortFamily.sort_val 
        (Build_valuation (fun _ => xH) (fun _ => 0) (find_assignment ρ)) s))
      global_sorts.
  Proof.
    intros Ha H H0.
    destruct (composition_local φ s) as [H4|H4] => //.
    - specialize (global_sorts_not_variables _ H4).
      destruct s => //.
    - apply is_constraints_graph_acyclic_spec in Ha.
      assert (In s (topological_sort local_graph)) as H5.
      + apply (topological_sort_reach _ _ _ SortFamilySet.empty
               (HI := make_graph_well_formed constraints) (Ha := Ha)).
        * apply (paths_step _ _ s); [|apply paths_refl].
          exists 1%Z. cbn.
          change (_ , _ , _) with (SortFamily.sfType, s).to_edge.
          apply<- make_graph_edges_caract. split => //.
          -- cbn. intro H5. rewrite<- H5 in H4 => //.
          -- left. split => //. apply (constraints_to_set_inc φ constraints) => //.
             unfold constraints, add_global.
             apply SortConstraintSetProp.union_subset_1.
        * apply constraints_to_set_correct. by left.
        * apply config_init.
      + destruct s as [| | | |n] eqn: H6 => //.
        destruct (assign_variables_output_universes n ρ H H5
                  (Ha := Ha)) as [s' [H7 H8]].
        rewrite (assign_variables_nodup _ _ _ _ s' _ _ H) => //.
        2: {intro H9. apply-> InA_nil. exact H9. }
        apply topological_sort_nodup.
  Qed.*)

  Definition constraints_correct : bool := is_acyclic local_graph &&
    global_local_agreement && isSome (assign_variables [] (topological_sort local_graph)).

  Theorem constraints_correct_spec : constraints_correct <-> sort_consistent φ.
  Proof.
    split.
    - unfold constraints_correct, sort_consistent.
      intros [[H H0]%andb_prop H1]%andb_prop. unfold isSome in H1.
      destruct (assign_variables [] _) as [ρ|] eqn: H2 => //.
      exists (Build_valuation (fun _ => xH) (fun _ => O) (find_assignment ρ)).
      set (v := Build_valuation _ _ _).
      intros c H3. apply global_elimination_correct.
      apply SortFamilySet.for_all_spec in H0.
      2: by intros ? ? ->.
      destruct (make_graph_well_formed constraints) as [H4 _ _].
      destruct (SortFamily.eq_dec c.1 c.2) as [->|Hneq].
      1: {destruct c.2 => //; [apply eqb_refl|].
          cbn. destruct (find_assignment _ _) => //. apply eqb_refl. }
      destruct (H4 (c.to_edge)) as [H5 H6].
      + apply make_graph_edges_caract. split => //. right.
        rewrite SortConstraintSet.union_spec. by left.
      + destruct c as [src tgt].
        apply is_constraints_graph_acyclic_spec in H. 
        destruct (SortFamily.is_var tgt) eqn: Hc.
        * destruct tgt as [| | | |n] => //.
          destruct (assign_variables_eq _ n H2 (Ha := H)) as [s [H7 H8]];
            [by apply topological_sort_constraints_reach|].
          rewrite (assign_variables_nodup _ _ _ _ _ _ _ H2 H8) => //;
            [apply topological_sort_nodup|by rewrite InA_nil|].
          apply: (join_bound); [|exact H7|].
          -- move=> ? /SortFamilySetProp.of_list_1 /InA_alt [? [<- /in_map_iff [? [<- ?]]]].
             by elim: (SortFamily.sort_val _ _).
          -- apply SortFamilySetProp.of_list_1. apply InA_alt.
             eexists (_). split; [exact eq_refl|].
             apply in_map_iff. exists src. split => //.
             apply pred_spec_2. exists 1%Z. 
             change (_, _, _) with (src, SortFamily.sfVar n).to_edge.
             apply make_graph_edges_caract. split => //. right.
             apply SortConstraintSet.union_spec. by left.
        * simpl. assert (SortFamily.from_univ (SortFamily.sort_val v tgt) = tgt) as ->; [by destruct tgt|].
          destruct (SortFamily.is_var src) eqn: Hs.
          -- destruct src as [| | | |n] => //.
             destruct (assign_variables_eq _ n H2 (Ha := H)) as [s [H7 H8]];
               [by apply topological_sort_constraints_reach|].
             rewrite (assign_variables_nodup _ _ _ _ _ _ _ H2 H8) => //;
               [apply topological_sort_nodup|by rewrite InA_nil|].
             apply: join_univ_prop => //; [exact H7| |].
             ++ move=> ? /SortFamilySetProp.of_list_1 /InA_alt [? [<- /in_map_iff [? [<- ?]]]].
                by elim: (SortFamily.sort_val _ _).
             ++ move=> s' /SortFamilySetProp.of_list_1 /InA_alt [? [<- /in_map_iff [x [<- H9]]]].
                set s0 := SortFamily.from_univ _.
                specialize (H0 s0). simpl in H0. 
                revert H0. rewrite SortFamilySet.for_all_spec.
                intro H0. specialize (fun a => H0 a tgt). simpl in H0.
                rewrite (eqb_prop _ _ (H0 _ _)).
                1-2: apply SortFamilySet.filter_spec; [by intros ? ? ->|].
                2: split; [easy|by rewrite Hc].
                ** split; [|unfold s0; by case: (SortFamily.sort_val _ _)].
                   apply pred_spec_1 in H9 as [z e].
                   destruct (make_graph_well_formed constraints) as [He _ _].
                   destruct (He _ e) as [Hx _].
                   unfold s0. destruct x as [| | | |n0] eqn: H9 => //; simpl; try by rewrite<- H9.
                   destruct (assign_variables_eq ρ n0 (Ha := H)) as [s1 [H10 H11]] => //;
                     [by apply topological_sort_constraints_reach|].
                   rewrite (assign_variables_nodup _ _ _ _ _ _ _ H2 H11) => //;
                     [apply topological_sort_nodup|by rewrite InA_nil|].
                   apply (assign_variables_in _ _ _ H2 H11 (Ha := H)) => //.
                ** apply local_refines_global => //.
                   apply 
        rewrite (eqb_prop (global_elimination _ _)
            (is_eliminable constraints (SortFamily.from_univ (SortFamily.sort_val v src))
                                       (SortFamily.from_univ (SortFamily.sort_val v tgt)))).
          1: apply H0.
          1-2: apply SortFamilySet.filter_spec; [by intros ? ? ->|].
          1-2: split; [|by case: (SortFamily.sort_val _ _)].
          1: destruct src eqn: H7 => //; simpl; try by rewrite<- H7.
          2: destruct tgt eqn: H7 => //; simpl; try by rewrite<- H7.
          1: destruct (assign_variables_eq ρ n (Ha := H)) as [s [H8 H9]] => //;
              [apply topological_sort_constraints_reach => //|].
          1: rewrite (assign_variables_nodup _ _ _ _ _ _ _ H2 H9) => //;
              [apply topological_sort_nodup|by rewrite InA_nil|].
          1: apply (assign_variables_in _ _ _ H2 H9 (Ha := H)).
             About join_univ_prop.
          -- assert (SortFamily.from_univ (SortFamily.sort_val v src) = src) as ->; [by destruct src|].
             apply is_eliminable_correct'. constructor. apply (paths_step _ _ tgt); [|apply paths_refl].
             exists 1%Z. change (_, _, _) with (src, tgt).to_edge.
             apply make_graph_edges_caract. split => //. right.
             apply SortConstraintSet.union_spec. by left.
      + destruct (SortFamily.sort_val _ _) => //.
      1: {apply assign_to_global => //.
          apply constraints_to_set_correct. right. 
          exists c. split => //. by left. }
        specialize (H0 H4). simpl in H0.
        apply SortFamilySet.for_all_spec in H0.
        2: by intros ? ? ->.
        specialize (H0 (SortFamily.from_univ (SortFamily.sort_val v c.2))).
        assert (SortFamilySet.In (SortFamily.from_univ (SortFamily.sort_val v c.2)) global_sorts) as H5.
        1: {apply assign_to_global => //.
            apply constraints_to_set_correct. right.
            exists c. split => //. by right. }
        specialize (H0 H5).
        simpl in H0.
        rewrite (eqb_prop _ _ (H0)). apply is_eliminable_correct'.
        constructor. rew
        (apply (paths_step _ _ c.2); [|apply paths_refl]).
        apply is_eliminable_correct'. constructor. apply (paths_step _ _ c.2.
        2: apply paths_refl.

End GoodConstraints.

(* TODO décider de la comparabilité d'univers ? *)

(* TODO reste conforme aux contraintes globales *)
