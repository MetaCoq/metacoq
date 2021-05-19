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
      + split; intros [H H0]; (split; [assumption|]);
        unfold is_not_self_loop in *; destruct (VSetDecide.F.eq_dec e..s e..t); [destruct (H0 e0)|reflexivity| |assumption].
        cbn in H0. inversion H0.
      + rewrite H. apply EdgeSet.filter_spec.
        intros [[]] [[]] ->. reflexivity.
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
        + intros [[H3%V.eq_leibniz|?]|[[? _]|?]];
            [right;left;by rewrite H3|now left|now right;left|right; now right].
        + intros H3. destruct (V.eq_dec y x); [now left;left|].
          destruct H3 as [?|[?|?]]; [now left;right|now right;left|now right;right].
      - rewrite VSet.inter_spec VSet.add_spec VSet.remove_spec.
        intros [[?|?] [? ?]]; [contradiction|]. apply (inter12 y).
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
        + intros [?|[[? _]|[?|?]]];
          [by left|by right;left|by right;left;rewrite H0|by right;right].
        + intros H0. destruct (V.eq_dec y x); [now right;right;left|].
          destruct H0 as [?|[?|?]]; [by left|by right;left|by right;right;right].
      - rewrite VSet.inter_spec VSet.remove_spec.
        intros [? [? ?]]. apply (inter12 y). by rewrite VSet.inter_spec.
      - rewrite VSet.inter_spec VSet.add_spec VSet.remove_spec.
        intros [[? ?] [?|?]]; [contradiction|]. apply (inter23 y).
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

    Lemma partition_in total v s l x : VSet.In x total ->
      Partition total v s l -> VSet.In x v \/ VSet.In x s \/ VSet.In x l.
    Proof.
      intros H [H0 _]. rewrite<- H0 in H. revert H.
      by repeat rewrite VSet.union_spec.
    Qed.

    Lemma aaa x y : (∑ n, In (x, n, y) (EdgeSet.elements (E G))) -> ∑ n, EdgeSet.In (x, n, y) (E G).
    Proof.
      intros [n Hn]. exists n. apply-> EdgeSet.elements_spec1.
      apply InA_alt. by exists (x, n, y).
    Qed.

    Lemma aaaa x : forall y, In y (map (fun x => x.2) (succs G x)) -> Edges G x y.
    Proof.
      intros y Hy. apply aaa. unfold succs in Hy. revert y Hy.
      induction (EdgeSet.elements (E G)).
      - easy.
      - simpl. intros y H. destruct (VSetDecide.F.eq_dec a..s x).
        + cbn in H. destruct (V.eq_dec a..t y).
          * exists (a..w). left. rewrite<- e0, <-e. destruct a as [[] ?].
            reflexivity.
          * destruct (IHl y) as [n0 ?].
            -- destruct H; [contradiction|assumption].
            -- exists (n0). by right.
        + cbn in H. destruct (IHl y H) as [n0 ?]. exists n0. by right.
    Qed.

    Lemma aaaa_rev x y : Edges G x y -> In y (map (fun x => x.2) (succs G x)).
    Proof.
      intros [n e].
      apply<- in_map_iff. exists (n, y). split; [reflexivity|].
      apply<- in_map_iff. exists (x, n, y). split; [reflexivity|].
      apply filter_In. split.
      - apply EdgeSet.elements_spec1 in e as H1.
        apply InA_alt in H1 as [y0 [H1 H2]].
        now rewrite H1.
      - cbn. destruct V.eq_equiv as [refl _ _].
        destruct (VSetDecide.F.eq_dec x x); [reflexivity|].
        now specialize (V.eq_leibniz x x (refl x)).
    Qed.

    Lemma inv_cardinal s x : VSet.In x s -> exists n, VSet.cardinal s = S n.
    Proof.
      intros [y [[=->] H%in_split]]%VSetFact.elements_1%InA_alt.
      destruct H as [l1 [l2 H]]. rewrite VSet.cardinal_spec H app_length.
      cbn. rewrite<- plus_n_Sm. by exists (#|l1| + #|l2|).
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
            (List.map (fun x => x.2) (succs G x)) (l,VSet.remove x s)) in
            (x::a.1, a.2)
        | false => (l, s)
        end
      end.

    Lemma topological_sort00_truc l x fuel s:
      VSet.Subset (topological_sort00 fuel s l x).2 s.
    Proof.
      revert s l x.
      induction fuel.
      + cbn. intros. apply VSetProp.subset_refl.
      + cbn. intros s l x. case Hx: (VSet.mem x s); [|cbn; apply VSetProp.subset_refl].
        set l2 := (map _ _).
        assert (VSet.Subset (VSet.remove x s) s) as H;
          [intros a H; now apply VSet.remove_spec in H as [H _]|].
        generalize l (VSet.remove x s) H.
        induction l2.
        - cbn. easy.
        - cbn. intros l' t Ht.
          have H1:= IHfuel t l' a. move: H1.
          set zebulon := topological_sort00 _ _ _ _.
          destruct zebulon. cbn. move => H1. apply (IHl2 l0 t0).
          etransitivity; eassumption.
    Qed.

    Lemma topological_sort00_truc2 l1 : forall fuel a s',
      VSet.Subset a.2 s' ->
      VSet.Subset (fold_left (fun a u => (topological_sort00 fuel a.2 a.1 u))
        l1 a).2 s'.
    Proof.
      induction l1 as [|x l1] => //.
      intros fuel a s' H. cbn. apply IHl1.
      transitivity a.2 => //. apply topological_sort00_truc.
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
        unfold fa, fb. set l2 := map _ _.
        apply VSetFact.mem_iff in Hx. apply VSetProp.remove_cardinal_1 in Hx.
        assert (S (VSet.cardinal (VSet.remove x s0)) <= VSet.cardinal s0) as H1; [lia|].
        generalize l (VSet.remove x s0) H1.
        induction l2.
        * reflexivity.
        * simpl. intros l0 t0 Ht. rewrite IHm; [lia|lia|].
          rewrite IHm; [reflexivity|lia|].
          move: (topological_sort00_truc l0 a (VSet.cardinal t0) t0).
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
      induction l.
      - cbn. reflexivity.
      - cbn. intros a0 H H0 H1. rewrite<- (H0 a0 a H).
        apply IHl.
        + now apply H1.
        + exact H0.
        + exact H1.
    Qed.

    Lemma topological_sort0_eq s l x: topological_sort0 s l x =
      match VSet.mem x s with
      | true => let a := (List.fold_left
          (fun a u => (topological_sort0 a.2 a.1 u))
          (List.map (fun x => x.2) (succs G x)) (l, VSet.remove x s)) in
          (x::a.1, a.2)
      | false => (l, s)
      end.
    Proof.
      unfold topological_sort0. set (fuel := VSet.cardinal s).
      cut (VSet.cardinal s = fuel); [|reflexivity].
      clearbody fuel. revert s x. induction fuel.
      - intros s x H. apply VSetProp.cardinal_inv_1 in H.
        specialize (H x). apply VSetProp.FM.not_mem_iff in H.
        rewrite H. reflexivity.
      - intros s x H. simpl.
        case_eq (VSet.mem x s); [|reflexivity].
        intro HH. rewrite<- (@VSetProp.remove_cardinal_1 s x) in H;
        [|now apply VSetFact.mem_iff]. inversion H as [H1].
        rewrite H1. rewrite (fold_left_ext _ 
          (fun a u => topological_sort00 (VSet.cardinal a.2) a.2 a.1 u)
          (fun a => VSet.cardinal a.2 <= fuel)).
        + cbn. rewrite H1. apply le_n.
        + intros a0 b H2. now apply (topological_sort00_inc (VSet.cardinal a0.2)).
        + intros a0 b H2. transitivity (VSet.cardinal a0.2); [|assumption].
          apply VSetProp.subset_cardinal. apply topological_sort00_truc.
        + reflexivity.
    Qed.

    Definition topological_sort := (topological_sort0 (V G) nil (s G)).1.

    Lemma topological_sort0_set_eq {s s' x} :
      VSet.Equal s s' -> topological_sort0 s x = topological_sort0 s' x.
    Proof.
      intros [=->]%VSet.eq_leibniz. reflexivity.
    Qed.

    Lemma topological_sort00_bla fuel s l x : exists l', (topological_sort00 fuel s l x).1 = l' ++ l.
    Proof.
      revert x l s.
      induction fuel.
      - exists []. now cbn.
      - intros x l s.
        cbn. destruct (VSet.mem x s).
        + set l2 := map _ _. clearbody l2. cbn. set p := (l, VSet.remove x s).
          assert (exists l', p.1 = l' ++ l) as H; [exists [] ;reflexivity|]. revert H. generalize p.
          induction l2.
          * cbn. intros p0 [l' H]. rewrite H. exists (x :: l'). reflexivity.
          * cbn. intros p0 [l' H]. apply (IHl2 (topological_sort00 fuel p0.2 p0.1 a)).
            destruct (IHfuel a p0.1 p0.2) as [l'' H0].
            exists (l'' ++ l'). rewrite<- app_assoc. rewrite H0. now rewrite H.
        + exists []. reflexivity.
    Qed.

    Lemma topological_sort00_blabla fuel s l l2 : exists l', (fold_left (fun a u => topological_sort00 fuel a.2 a.1 u) l2 (l, s)).1 = l' ++ l.
    Proof.
      revert fuel s l.
      induction l2.
      - cbn. by exists [].
      - cbn. intros fuel s l. destruct (topological_sort00_bla fuel s l a) as [l'' H].
        set p := topological_sort00 _ _ _ _. destruct (IHl2 fuel p.2 p.1) as [l' H0].
        exists (l' ++ l''). rewrite<- app_assoc. rewrite<- (surjective_pairing p) in H0.
        rewrite H0. unfold p, topological_sort0. now rewrite H.
    Qed.

    Definition topological_sort0_bla s l x : exists l', (topological_sort0 s l x).1 = l' ++ l :=
      topological_sort00_bla (VSet.cardinal s) s l x.

    Definition topological_sort0_blabla s l l2 : exists l', (fold_left (fun a u => topological_sort0 a.2 a.1 u) l2 (l, s)).1 = l' ++ l.
    Proof.
      destruct (topological_sort00_blabla (VSet.cardinal s) s l l2) as [l' H].
      exists l'. rewrite<- H. set fa := fold_left _ _ _. set fb := fold_left _ _ _.
      enough (fa = fb).
      + by rewrite H0.
      + unfold fa, fb. apply (fold_left_ext _ _ (fun a => VSet.Subset a.2 s )); try easy.
        * intros a b H0. symmetry. apply (topological_sort00_inc (VSet.cardinal s)).
          - apply le_n.
          - now apply VSetProp.subset_cardinal.
        * intros a b H0. transitivity a.2; [|assumption]. apply topological_sort00_truc.
    Qed.

    Lemma topological_sort0_diet fuel s l x z : VSet.In z s -> ~ In z (topological_sort00 fuel s l x).1 ->
      VSet.In z (topological_sort00 fuel s l x).2.
    Proof.
      revert s l x. induction fuel.
      - easy.
      - cbn. intros s l x. destruct (VSet.mem x s); [|easy].
        set l' := map _ _. cbn. intros H [H0 H1]%not_in_cons.
        assert (forall l'' p, VSet.In z p.2 -> ~ In z (fold_left (fun a u => topological_sort00 fuel a.2 a.1 u) l'' p).1->
          VSet.In z (fold_left (fun a u => topological_sort00 fuel a.2 a.1 u) l'' p).2) as H2.
        + induction l''.
          * easy.
          * cbn. intros p H2 H3. apply IHl''; [|assumption].
            apply IHfuel; [assumption|]. remember (topological_sort00 _ _ _ _) as p0. destruct (topological_sort00_blabla fuel p0.2 p0.1 l'') as [l0 H4].
            rewrite<- surjective_pairing in H4. rewrite H4 in H3.
            intro. apply H3. apply in_or_app. right. assumption.
        + apply H2; [now apply VSet.remove_spec|easy].
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

    Lemma is_topo_sorted_weak l y z : is_topo_sorted l -> In y l ->
      Paths G y z -> In z l.
    Proof.
      intros H [l1 [l2 H0]]%in_split p. rewrite H0 in H |- *. clear H0.
      induction l1.
      - inversion H. apply H2 => //.
      - rewrite<- app_comm_cons. apply in_cons. apply IHl1. inversion H => //.
    Qed.

    Lemma union_add_remove x s s' : VSet.In x s ->
      VSet.union (VSet.add x s') (VSet.remove x s) = VSet.union s' s.
    Proof.
      intro. apply VSet.eq_leibniz. intro a.
      repeat rewrite VSet.union_spec. rewrite VSet.add_spec VSet.remove_spec.
      split.
      - intros [[?|?]|[? ?]].
        + rewrite H0. by right.
        + by left.
        + by right.
      - intros [?|?].
        + by left; right.
        + destruct (V.eq_dec a x) as [[=->]|H1].
          * by left; left.
          * right. by split.
    Qed.

    Lemma union_add x s s' : VSet.union (VSet.add x s) s' = VSet.add x (VSet.union s s').
    Proof.
      apply VSet.eq_leibniz. intro a.
      rewrite VSet.union_spec VSet.add_spec VSet.add_spec VSet.union_spec.
      split.
      - by intros [[?|?]|?]; [left|right;left|right;right].
      - by intros [?|[?|?]]; [left;left|left;right|right].
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

(*
    Lemma truc fuel x : 
      forall l0 l1 v s l, map (fun x => x.2) (succs G x) = l1 ++ l0 ->
      let a := fold_left (fun a u => topological_sort00 fuel a.2 a.1 u)
        l1 (l, s) in configuration v a.2 a.1 x -> 
      let a := fold_left (fun a u => topological_sort00 fuel a.2 a.1 u)
        (l1 ++ l0) (l, s) in configuration v a.2 a.1 x.
    Proof.
      intro l0. induction l0.
      - intros l1 v s l H. by rewrite (app_nil_r l1).
      - intros l1 v s0 l H. assert (l1 ++ a :: l0 = (l1 ++ [a]) ++ l0) as H0.
        + by rewrite<- app_assoc.
        + intros a0 Hl1. rewrite H0. apply IHl0; [easy|].
          rewrite fold_left_app. fold a0. cbn.
    Admitted.
*)
    Definition succ' x := map (fun x => x.2) (succs G x).

    Context {Ha : acyclic}.

    Lemma violent fuel : forall v s l x, configuration v s l x ->
      VSet.cardinal s <= fuel ->
      let a := (topological_sort00 fuel s l x) in configuration v a.2 a.1 x.
    Proof.
      induction fuel => //.
      intros v s l x config Hfuel.
      destruct config as [part [back_path topo_sort]]. cbn delta fix match beta.
      destruct (VSet.mem x s) eqn: H0 => //.
      apply VSetFact.mem_iff in H0.
      set l0 := succ' x.
      assert (succ' x = [] ++ l0) as H => //.
      assert (let a := fold_left (fun a u => topological_sort00 fuel a.2 a.1 u)
        [] (l, VSet.remove x s) in config' (VSet.add x v) a.2 a.1 /\
          forall y z, Edges G x y -> In y [] -> Paths G y z -> In z (x::a.1)).
      - split => //. split => //. apply partition_move_21 => //.
      - fold (succ' x). rewrite H. elim: l0 [] H H1.
        + intro l1. rewrite app_nil_r. intros H [[? ?] ?].
          split; [|split] => //.
          * apply partition_move_13 => //. destruct part as [_ [part _]].
            intro. apply (part x). by rewrite VSet.inter_spec.
          * constructor => //.
            intros y path. destruct path; [apply in_eq|].
               apply (H3 y) => //. rewrite<- H. apply aaaa_rev => //.
        + intros x0 l0 IHl0 l1. set a := fold_left (fun a0 u => topological_sort00 fuel a0.2 a0.1 u) l1
            (l, VSet.remove x s).
          intros H [[Hpart Hsorted] Hpath].
          assert (l1 ++ x0 :: l0 = (l1 ++ [x0]) ++ l0) as H2; [by rewrite<- app_assoc|].
          rewrite H2. apply IHl0; [easy|].
          rewrite fold_left_app. fold a. cbn.
          destruct (IHfuel (VSet.add x v) a.2 a.1 x0) as [? [? ?]]; [| |split => //].
          * split; [|split] => //. intros y path [Hy|Hy]%VSet.add_spec.
            -- rewrite Hy in path. unfold acyclic in Ha. apply (Ha x x0) => //.
               apply aaaa. fold (succ' x). rewrite H. apply in_or_app. right.
               apply in_eq.
            -- apply (back_path y) => //. apply (paths_step _ _ x0); [|eassumption].
               apply aaaa. fold (succ' x). rewrite H. apply in_or_app. right. apply in_eq.
          *  assert (S (VSet.cardinal (VSet.remove x s)) = VSet.cardinal s) as H6;
              [apply VSetProp.remove_cardinal_1 => //|].
            rewrite<- H6 in Hfuel. apply le_S_n in Hfuel.
            transitivity (VSet.cardinal (VSet.remove x s)) => //.
            apply VSetProp.subset_cardinal. apply topological_sort00_truc2.
            apply VSetProp.subset_refl.
          * intros y z e [Hy|[[=->]|?]]%in_app_or p => //.
            -- destruct (Hpath y z e Hy p); [by left|]. right.
               destruct (topological_sort00_bla fuel a.2 a.1 x0) as [? [=->]].
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
                  assert (VSet.In y a.2); [apply (topological_sort00_truc a.1 y fuel a.2) => //|].
                  assert (VSet.Subset a.2 (VSet.remove x s)).
                  1: {apply topological_sort00_truc2. apply VSetProp.subset_refl. }
                  assert (VSet.cardinal a.2 <= fuel). 
                  1: {transitivity (VSet.cardinal (VSet.remove x s)) => //. apply VSetProp.subset_cardinal => //. }
                  destruct (inv_cardinal a.2 y) as [n H10] => //. rewrite H10 in H9.
                  destruct fuel; [inversion H9|]. apply (is_topo_sorted_weak _ y) => //.
                  cbn. apply (VSetFact.mem_iff a.2 y) in H7 as [=->]. apply in_eq.
               ++ apply (is_topo_sorted_weak _ y) => //. revert H5.
                  rewrite VSetProp.of_list_1. by intros [? [[=->] ?]]%InA_alt.
    Qed.

    Lemma machin x z v s l: Paths G x z -> VSet.In x s ->
      configuration v s l x -> In z (topological_sort0 s l x).1.
    Proof.
      intros p H%VSetFact.mem_iff config.
      apply (violent (VSet.cardinal s)) in config => //.
      destruct config as [_ [_ ?]].
      apply (is_topo_sorted_weak _ x) => //. rewrite topological_sort0_eq H.
      apply in_eq.
    Qed.

    Lemma topological_sort0_in y: VSet.In y (V G) ->
      In y (topological_sort).
    Proof.
      intro H. destruct HI as [edges source path].
      apply (machin _ _ VSet.empty) => //.
      - admit.
      - apply config_init.
    Admitted.

    Lemma topological_sort0_spec x l l': topological_sort = l ++ x::l' ->
      forall y, Paths G x y -> In y (x::l').
    Proof.
      intros H y p.
      have config := config_init. apply (violent (VSet.cardinal (V G))) in config => //.
      destruct config as [_ [_ is_sorted]].
      destruct (is_topo_sorted_alt topological_sort) as [H0 _].
      apply (H0 is_sorted x y l l' H p).
    Qed.

  Definition pred (x : V.t) : list V.t := 
    let l := List.filter (fun e => V.eq_dec e..t x) (EdgeSet.elements (E G)) in
    List.map (fun e => e..s) l.
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

  Lemma global_constraints_support: SortFamilySet.Equal (constraints_to_set global_constraints) global_sorts.
  Proof.
    unfold SortFamilySet.Equal. intro a.
    rewrite constraints_to_set_correct.
    unfold global_constraints, global_sorts.
    repeat rewrite SortFamilySet.add_spec.
    rewrite SortFamilySet.singleton_spec.
    split.
    - move=> [[=->]|[constraint [H H0]]]; [now left|].
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

Section Join.
  Definition upper_bound (v:SortFamily.t) (S:SortFamilySet.t) :=
    SortFamilySet.for_all (fun c => is_eliminable global_constraints c v) S.

  Definition join : SortFamilySet.t -> option SortFamily.t.
  Admitted.

  Lemma join_bound (n:SortFamily.t) (S:SortFamilySet.t) : join S = Some n -> upper_bound n S.
  Admitted.

  Lemma join_univ_prop (n: SortFamily.t) (S:SortFamilySet.t):
  join S = Some n -> forall v, (upper_bound v S -> is_eliminable global_constraints n v).
  Admitted.

  Lemma join_when_bound (n: SortFamily.t) (S:SortFamilySet.t):
    upper_bound n S -> exists v, join S = Some v.
  Admitted.
End Join.

Section GoodConstraints.
  Variable (φ: SortConstraintSet.t).
  Definition constraints := add_global φ.
  Definition local_graph := make_graph constraints.

  Definition respect_constraints s s':=
    Bool.eqb (is_eliminable global_constraints s s') (is_eliminable constraints s s').

  Definition global_local_agreement: bool := SortFamilySet.for_all
    (fun s => SortFamilySet.for_all (fun s' => respect_constraints s s') global_sorts) global_sorts.

  Definition assignment : Set := list (nat × SortFamily.t).
  Definition get_value (ρ : assignment) (s : SortFamily.t) : option SortFamily.t :=
    match s with
    | SortFamily.sfVar n => match find (fun p => Nat.eqb p.1 n) ρ with
      | None => None
      | Some (m, s') => Some s'
      end
    | _ => Some s
    end.

  Fixpoint gather_option (l : list (option (SortFamily.t))) : option SortFamilySet.t :=
    match l with
    | [] => Some SortFamilySet.empty
    | None :: l' => None
    | Some s :: l' => match gather_option l' with
      | None => None
      | Some sfSet => Some (SortFamilySet.add s sfSet)
      end
    end.

  Definition join_option (l : option (SortFamilySet.t)) : option SortFamily.t :=
    match l with
    | None => None
    | Some s => join s
    end.

  Fixpoint assign_variables (ρ: assignment) (vertices: list SortFamily.t): option assignment :=
    match vertices with
    | [] => Some ρ
    | sort :: l => match sort with
      | SortFamily.sfVar n => 
        match gather_option (map (get_value ρ) (pred local_graph (sort))) with
        | None => None
        | Some preds => match join preds with
          | None => None
          | Some sort => assign_variables ((n, sort)::ρ) l
          end
        end 
      | _ => assign_variables ρ l
      end
    end.

  Definition constraints_correct
End GoodConstraints.

(* TODO décider de la comparabilité d'univers ? *)

(* TODO acyclicité *)

(* TODO reste conforme aux contraintes globales *)
