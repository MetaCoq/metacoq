From Coq Require Import ssreflect.
From Coq Require Import MSetList MSetFacts MSetProperties MSetDecide.
From MetaCoq.Template Require Import utils BasicAst config.
From MetaCoq.Template Require Export Levels Sorts.

Local Open Scope nat_scope.
Local Open Scope string_scope2.


Ltac absurd :=
  match goal with
  | [H : False |- _] => elim H
  end.
Hint Extern 10 => absurd : core.

(** {6 Universe instances} *)

Module Instance.

  (** A universe instance represents a vector of argument sorts
      to a polymorphic definition (constant, inductive or constructor).
      The optional level needs to be present if the sort is predicative. *)
  Definition t : Set := list Level.t * list SortFamily.t.

  Definition empty : t := ([], []).
  Definition is_empty (i : t) : bool :=
    match i with
    | ([], []) => true
    | _ => false
    end.

  Definition eqb (i j : t) :=
    forallb2 Level.eqb (fst i) (fst j) && forallb2 SortFamily.eqb (snd i) (snd j).

  Definition equal_upto (f : Level.t -> Level.t -> bool) (i j : t) :=
    forallb2 f (fst i) (fst j) && forallb2 SortFamily.eqb (snd i) (snd j).
End Instance.

Module ConstraintSet.
  Definition t := SortConstraintFormula.t × UnivConstraintSet.t.

  Definition empty := (SortConstraintFormula.True, UnivConstraintSet.empty).

  Definition is_empty t :=
    SortConstraintFormula.is_True (fst t) && UnivConstraintSet.is_empty (snd t).
End ConstraintSet.

(** ** Contexts *)

(** * Universe Context *)
(* Context of named variables *)
Module UContext.
  Definition t := Instance.t × ConstraintSet.t.

  Definition make : Instance.t -> SortConstraintFormula.t -> UnivConstraintSet.t -> t :=
    fun ins scs ucs => (ins, (scs, ucs)).

  Definition empty : t :=
    (Instance.empty, ConstraintSet.empty).

  Definition instance : t -> Instance.t := fst.
  Definition sort_constraints : t -> SortConstraintFormula.t := fst ∘ snd.
  Definition univ_constraints : t -> UnivConstraintSet.t := snd ∘ snd.

  Definition dest : t -> Instance.t * (SortConstraintFormula.t * UnivConstraintSet.t) := fun x => x.
End UContext.


(** * Abstract Universe Context *)
(* Context of DeBruijn variables *)
Module AUContext.

  (* Following the convention of Instance.t
     the first list is for universe-levels, the second for sort families
     names are irrelevant *)
  Definition t := (list name × list name) × ConstraintSet.t.

  Definition make (lvl_ids sort_ids: list name) (sctrs : SortConstraintFormula.t) (uctrs : UnivConstraintSet.t) : t := ((lvl_ids, sort_ids), (sctrs, uctrs)).

  Definition repr (x : t) : UContext.t :=
    let '((uvs0,sorts0), cst) := x in
    let uvs := mapi (fun i _ => Level.Var i) uvs0 in
    let sorts := mapi (fun i _ => SortFamily.sfVar i) sorts0 in
    ((uvs, sorts), cst).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (fst (repr uctx))).
End AUContext.

(** * Only for monomorphic universes *)
Module UnivContextSet.
  Definition t := LevelSet.t × UnivConstraintSet.t.

  Definition empty : t := (LevelSet.empty, UnivConstraintSet.empty).

  Definition is_empty (uctx : t)
    := LevelSet.is_empty (fst uctx) && UnivConstraintSet.is_empty (snd uctx).
End UnivContextSet.


Inductive universes_decl : Type :=
| Monomorphic_ctx (ctx : UnivContextSet.t)
| Polymorphic_ctx (cst : AUContext.t).

Definition monomorphic_udecl u :=
  match u with
  | Monomorphic_ctx ctx => ctx
  | _ => UnivContextSet.empty
  end.

Definition monomorphic_levels φ := (monomorphic_udecl φ).1.
Definition monomorphic_constraints φ := (monomorphic_udecl φ).2.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => fst ctx
  | Polymorphic_ctx ctx => AUContext.levels ctx
  end.

Definition universe_constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => snd ctx
  | Polymorphic_ctx ctx => snd (snd (AUContext.repr ctx))
  end.


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

  (* val check_subtype : t -> t -> bool *)
  (* val sup : t -> t -> t *)
End Variance.


Definition univ_le_n n u u' :=
  (Z.of_nat u <= Z.of_nat u' - n)%Z.

Notation "x <_ n y" := (univ_le_n n x y) (at level 10, n ident) : univ_scope.
Notation "x < y" := (univ_le_n 1 x y) : univ_scope.
Notation "x <= y" := (univ_le_n 0 x y) : univ_scope.

Ltac lle := unfold univ_le_n in *.

Section Univ.
  Context {cf:checker_flags}.

  Global Instance lle_refl : Reflexive (univ_le_n 0).
  Proof.
    intro x; red; lia.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof. split; lia. Qed.


  Global Instance le_n_trans n : Transitive (univ_le_n (Z.of_nat n)).
  Proof.
    intros ? ? ?; unfold univ_le_n; simpl; lia.
  Qed.

  Global Instance lle_trans : Transitive (univ_le_n 0).
  Proof. apply (le_n_trans 0). Qed.

  Global Instance llt_trans : Transitive (univ_le_n 1).
  Proof. apply (le_n_trans 1). Qed.

  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, UnivConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, UnivConstraintType.Eq, l').

  Definition satisfies v : UnivConstraintSet.t -> Prop :=
    UnivConstraintSet.For_all (satisfies0 v).

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition eq_universe0 (φ : UnivConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (val v u = val v u').

  Definition leq_universe_n n (φ : UnivConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (univ_le_n n (val v u) (val v u'))%u.

  Definition leq_universe0 (φ : UnivConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (val v u <= val v u')%u.

  Lemma leq_universe0_leq_universe_n (φ : UnivConstraintSet.t) u u' :
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
    : UnivConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
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
    destruct (val v u), (val v u'); try now auto.
  Qed.


  Lemma leq_universe0_sup_l' φ (s1 s2 : UniverseLevel.t) :
    leq_universe0 φ s1 (UniverseLevel.sup s1 s2).
  Proof.
    intros v Hv. cbn. rewrite val_sup. red; lia.
  Qed.

  Lemma leq_universe0_sup_r' φ (s1 s2 : UniverseLevel.t) :
    leq_universe0 φ s2 (UniverseLevel.sup s1 s2).
  Proof.
    intros v Hv. cbn. rewrite val_sup. red; lia.
  Qed.

  Lemma leq_universe_product φ (s1 s2 : UniverseLevel.t)
    : leq_universe φ s2 (UniverseLevel.level_of_product s1 s2).
  Proof.
    unfold leq_universe; destruct check_univs; [cbn|constructor].
    apply leq_universe0_sup_r'.
  Qed.

  (* We are only comparing universe levels for predicative sorts *)
  Lemma leq_universe_product_dom φ (s1 s2 : UniverseLevel.t)
    : leq_universe φ s1 (UniverseLevel.level_of_product s1 s2).
  Proof.
    unfold leq_universe; destruct check_univs; [cbn|constructor].
    apply leq_universe0_sup_l'.
  Qed.

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
    - intros x H. red in H. simpl in *; lia.
    - exact _.
  Qed.


  Global Instance lle_antisym : Antisymmetric _ eq (univ_le_n 0).
  Proof.
    intros ? ? h h'; red in h, h'; lia.
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


  Definition eq_universe_leq_universe' {cf} φ u u'
    := @eq_universe_leq_universe cf φ u u'.
  Definition leq_universe_refl' φ u
    := @leq_universe_refl φ u.

  Hint Resolve eq_universe_leq_universe' leq_universe_refl' : core.

End Univ.





(* (** * NOT SURE IF RELEVANT *) *)

(* Inductive universes := *)
(*   | UProp *)
(*   | USProp *)
(*   | UType (i : nat). *)

(* Definition univ_val := *)
(*   fun v u => match u with *)
(*           | lSProp => USProp *)
(*           | lProp => UProp *)
(*           | lType l => UType (val v l) *)
(*           end. *)


(* Lemma val_make v l *)
(*   : univ_val v (make l) = UType (val v l). *)
(* Proof. *)
(*   destruct l; cbnr. *)
(* Qed. *)

(* Lemma val_make_npl v (l : Level.t) *)
(*   : univ_val v (make l) = UType (val v l). *)
(* Proof. *)
(*   destruct l; cbnr. *)
(* Qed. *)


(* Definition is_propositional u :=  *)
(*   Universe.is_prop u || Universe.is_sprop u. *)

(* (** This coercion allows to see the universes as a [UnivExprSet.t] *) *)
(* Coercion Universe.t_set : Universe.t0 >-> UnivExprSet.t. *)

Notation "⟦ u ⟧_ v" := (val v u) (at level 0, format "⟦ u ⟧_ v", v ident) : univ_scope.


(* (* Definition univ_val_max v1 v2 := *) *)
(* (*   match v1, v2 with *) *)
(* (*   | UProp, UProp => UProp *) *)
(* (*   | USProp, USProp => USProp *) *)
(* (*   | UType v, UType v' => UType (Nat.max v v') *) *)
(* (*   | _, UType _ => v2 *) *)
(* (*   | UType _, _ => v1 *) *)
(* (*   | UProp, USProp => UProp *) *)
(* (*   | USProp, UProp => UProp *) *)
(* (*   end. *) *)

(* (* Lemma val_universe_sup v u1 u2 : *) *)
(* (*   Universe.univ_val v (Universe.sup u1 u2) = univ_val_max (Universe.univ_val v u1) (Universe.univ_val v u2). *) *)
(* (* Proof. *) *)
(* (*   destruct u1 as [ | | l1]; destruct u2 as [ | | l2];cbn;try lia; auto. *) *)
(* (*   f_equal. apply val_sup. *) *)
(* (* Qed. *) *)

(* (* Lemma is_prop_val u : *) *)
(* (*   Universe.is_prop u -> forall v, Universe.univ_val v u = UProp. *) *)
(* (* Proof. *) *)
(* (*   destruct u as [| | u];try discriminate;auto. *) *)
(* (* Qed. *) *)

(* (* Lemma is_sprop_val u : *) *)
(* (*   Universe.is_sprop u -> forall v, Universe.univ_val v u = USProp. *) *)
(* (* Proof. *) *)
(* (*   destruct u as [| | u];try discriminate;auto. *) *)
(* (* Qed. *) *)


(* (* Lemma val_is_prop u v : *) *)
(* (*   Universe.univ_val v u = UProp <-> Universe.is_prop u. *) *)
(* (* Proof. *) *)
(* (*   destruct u; auto;cbn in *; intuition congruence. *) *)
(* (* Qed. *) *)

(* (* Lemma val_is_sprop u v : *) *)
(* (*   Universe.univ_val v u = USProp <-> Universe.is_sprop u. *) *)
(* (* Proof. *) *)
(* (*   destruct u;auto;cbn in *; intuition congruence. *) *)
(* (* Qed. *) *)

(* (* Lemma is_prop_and_is_sprop_val_false u : *) *)
(* (*   Universe.is_prop u = false -> Universe.is_sprop u = false ->  *) *)
(* (*   forall v, ∑ n, Universe.univ_val v u = UType n. *) *)
(* (* Proof. *) *)
(* (*   intros Hp Hsp v. *) *)
(* (*   destruct u; try discriminate. simpl. eexists; eauto. *) *)
(* (* Qed. *) *)

(* (* Lemma val_is_prop_false u v n : *) *)
(* (*   Universe.univ_val v u = UType n -> Universe.is_prop u = false. *) *)
(* (* Proof. *) *)
(* (*   pose proof (is_prop_val u) as H. destruct (Universe.is_prop u); cbnr. *) *)
(* (*   rewrite (H eq_refl v). discriminate. *) *)
(* (* Qed. *) *)



(* (** Sort families *) *)

(* Inductive sort_family : Set := InSProp | InProp | InSet | InType. *)

(* (* Prop <= Set, Type but SProp </= Prop, Set, Type *) *)
(* Definition leb_sort_family x y := *)
(*   match x, y with *)
(*   | InProp, InSProp => false *)
(*   | InProp, _ => true *)
(*   | InSProp, InSProp => true *)
(*   | InSProp, _ => false *)
(*   | InSet, (InProp | InSProp) => false *)
(*   | InSet, _ => true *)
(*   | InType, (InProp | InSProp | InSet) => false *)
(*   | InType, InType => true *)
(*   end. *)

(* (** Family of a universe [u]. *) *)
(* Definition universe_family (u : Universe.t) := *)
(*   if Universe.is_prop u then InProp *)
(*   else if Universe.is_sprop u then InSProp *)
(*   else if Universe.is_small u then InSet *)
(*   else InType. *)

(* (** * END NOT SURE IF RELEVANT *) *)





(* This universe is a hack used in plugins to generate fresh universes *)
Definition fresh_universe : UniverseLevel.t.
Proof. exact UniverseLevel.type0. Qed.
(* This level is a hack used in plugins to generate fresh levels *)
Definition fresh_level : Level.t.
Proof. exact Level.lSet. Qed.


(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Instance subst_instance_level : UnivSubst Level.t :=
  fun u l =>
    match l with
    | Level.lSet | Level.Level _ => l
    | Level.Var n => List.nth n (fst u) Level.lSet
    end.

Instance subst_instance_sort_family : UnivSubst SortFamily.t :=
  fun u sf =>
    match sf with
    | SortFamily.sfType | SortFamily.sfGlobal _ => sf
    | SortFamily.sfVar i => List.nth i (snd u) SortFamily.sfType
    end.

Instance subst_instance_ucstr : UnivSubst UnivConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

Instance subst_instance_scstr : UnivSubst SortConstraint.t :=
  fun u '(SortConstraint.Eliminable sf1 sf2) =>
    SortConstraint.Eliminable (subst_instance u sf1) (subst_instance u sf2).

Instance subst_instance_clause : UnivSubst SortConstraintSet.t :=
  fun u ctrs =>
    SortConstraintSet.fold
      (fun c => SortConstraintSet.add (subst_instance_scstr u c))
      ctrs SortConstraintSet.empty.

Instance subst_instance_formula : UnivSubst SortConstraintFormula.t :=
  fun u ctrs =>
    SortConstraintFormula.fold
      (fun c => SortConstraintFormula.add (subst_instance u c))
      ctrs SortConstraintFormula.empty.

Instance subst_instance_ucstrs : UnivSubst UnivConstraintSet.t :=
  fun u ctrs =>
    UnivConstraintSet.fold
      (fun c => UnivConstraintSet.add (subst_instance u c))
      ctrs UnivConstraintSet.empty.

Instance subst_instance_cstrs : UnivSubst ConstraintSet.t :=
  fun u ctrs => (subst_instance u (fst ctrs), subst_instance u (snd ctrs)).

Instance subst_instance_level_expr : UnivSubst UnivExpr.t :=
  fun u e => match e with
          | (Level.lSet, _)
          | (Level.Level _, _) => e
          | (Level.Var n, b) =>
            match nth_error (fst u) n with
            | Some l => (l,b)
            | None => (Level.lSet, b)
            end
          end.

Instance subst_instance_univ_level : UnivSubst UniverseLevel.t :=
  fun u => UniverseLevel.map (subst_instance_level_expr u).

Instance subst_instance_sort : UnivSubst Sort.t :=
  fun u s =>
    match s with
    | Sort.ImpredicativeSort sf =>
      Sort.ImpredicativeSort (subst_instance u sf)
    | Sort.PredicativeSort sf l =>
      Sort.PredicativeSort (subst_instance u sf) (subst_instance u l)
    end.

Instance subst_instance_instance : UnivSubst Instance.t :=
  fun u u' =>
    (List.map (subst_instance_level u) (fst u'),
     List.map (subst_instance_sort_family u) (snd u')).


(** Tests that the term is closed over [j] sort variables and [k] universe level variables *)
Section Closedu.
  Context (j k : nat).

  Definition closedu_level (l : Level.t) :=
    match l with
    | Level.Var n => (n <? k)%nat
    | _ => true
    end.

  Definition closedu_level_expr (s : UnivExpr.t) :=
    closedu_level (UnivExpr.get_level s).

  Definition closedu_universe_levels (u : UniverseLevel.t) :=
    UnivExprSet.for_all closedu_level_expr u.

  Definition closedu_sort_family (sf : SortFamily.t) :=
    match sf with
    | SortFamily.sfVar i => (i <? j)%nat
    | _ => true
    end.

  Definition closedu_universe (u : Sort.t) :=
    match u with
    | Sort.ImpredicativeSort sf => closedu_sort_family sf
    | Sort.PredicativeSort sf l =>
      closedu_sort_family sf &&
      closedu_universe_levels l
    end.

  Definition closedu_instance (u : Instance.t) :=
    forallb closedu_level (fst u)
    && forallb closedu_sort_family (snd u).
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

  Lemma closedu_subst_instance_univ_levels u s
    : closedu_universe_levels 0 s -> subst_instance_univ_level u s = s.
  Proof.
    intros H; destruct s as [elts Hs].
    unfold closedu_universe_levels in *;cbn in *.
    unfold subst_instance_univ_level. simpl.
    apply eq_univ'.
    unfold closedu_universe_levels in *;cbn in *.
    intro e; split; intro He.
    - apply UniverseLevel.map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      2: now subst.
      apply UnivExprSet.for_all_spec in H; proper.
      exact (H _ He').
    - apply UniverseLevel.map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply UnivExprSet.for_all_spec in H; proper. now apply H.
  Qed.


  Lemma closedu_subst_instance_sort_family u sf
    : closedu_sort_family 0 sf -> subst_instance_sort_family u sf = sf.
  Proof. intros; destruct sf; cbnr; discriminate. Qed.

  Lemma closedu_subst_instance_sort u s
    : closedu_universe 0 0 s -> subst_instance_sort u s = s.
  Proof.
    intro H.
    destruct s;auto;cbn in *; f_equal.
    - move: H => /andP [+ _]; apply closedu_subst_instance_sort_family.
    - move: H => /andP [_]; apply closedu_subst_instance_univ_levels.
    - now apply closedu_subst_instance_sort_family.
  Qed.

  Lemma closedu_subst_instance_instance u t
    : closedu_instance 0 0 t -> subst_instance_instance u t = t.
  Proof.
    intros [H1 H2]%andP.
    destruct t as [t1 t2].
    unfold subst_instance_instance; f_equal.
    all: apply forall_map_id_spec; apply Forall_forall; intros l Hl.
    1: {
      apply closedu_subst_instance_level.
      eapply forallb_forall in H1; eassumption.
    }
    apply closedu_subst_instance_sort_family.
    eapply forallb_forall in H2; eassumption.
  Qed.

End UniverseClosedSubst.

Hint Resolve closedu_subst_instance_level closedu_subst_instance_level_expr
     closedu_subst_instance_univ_levels closedu_subst_instance_sort_family
     closedu_subst_instance_sort closedu_subst_instance_instance : substu.

(** Substitution of a universe-closed instance of the right size
    produces a universe-closed term. *)
Section SubstInstanceClosed.
  Context (u : Instance.t) (Hcl : closedu_instance 0 0 u).

  Lemma subst_instance_level_closedu l
    : closedu_level #|fst u| l -> closedu_level 0 (subst_instance_level u l).
  Proof.
    destruct l; cbnr; move: Hcl=> /andP [H1 _].
    destruct (nth_in_or_default n (fst u) Level.lSet).
    - intros _. eapply forallb_forall in H1; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_level_expr_closedu e :
    closedu_level_expr #|fst u| e -> closedu_level_expr 0 (subst_instance_level_expr u e).
  Proof.
    destruct e as [l b]. destruct l;cbnr; move: Hcl=> /andP [H1 _].
    case_eq (nth_error (fst u) n); cbnr. intros [] Hl X; cbnr.
    apply nth_error_In in Hl.
    eapply forallb_forall in H1; tea.
    discriminate.
  Qed.

  Lemma subst_instance_universe_levels_closedu s
    : closedu_universe_levels #|fst u| s -> closedu_universe_levels 0 (subst_instance u s).
  Proof.
    intro H.
    destruct s as [l Hl];cbnr.
    apply UnivExprSet.for_all_spec; proper.
    intros e He. eapply UniverseLevel.map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply UnivExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.

  Lemma subst_instance_sort_family_closedu sf :
    closedu_sort_family #|snd u| sf -> closedu_sort_family 0 (subst_instance_sort_family u sf).
  Proof.
    intro H; destruct sf; cbnr; move: Hcl=> /andP [_ H2].
    destruct (nth_in_or_default n (snd u) SortFamily.sfType).
    - eapply forallb_forall in H2; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_sort_closedu s :
    closedu_universe #|snd u| #|fst u| s -> closedu_universe 0 0 (subst_instance_sort u s).
  Proof.
    intros H; destruct s; cbnr.
    1: move: H=> /andP [? ?]; apply andb_and; split.
    1,3:now apply subst_instance_sort_family_closedu.
    now apply subst_instance_universe_levels_closedu.
  Qed.

  Lemma subst_instance_instance_closedu t :
    closedu_instance #|snd u| #|fst u| t -> closedu_instance 0 0 (subst_instance_instance u t).
  Proof.
    intros [H1 H2]%andP.
    apply andb_and; split.
    all: etransitivity; first eapply forallb_map.
    all: eapply forallb_impl; tea; intros l Hl; cbn.
    1: apply subst_instance_level_closedu.
    apply subst_instance_sort_family_closedu.
  Qed.
End SubstInstanceClosed.

Hint Resolve subst_instance_level_closedu subst_instance_level_expr_closedu
     subst_instance_universe_levels_closedu subst_instance_sort_family_closedu
    subst_instance_sort_closedu subst_instance_instance_closedu : substu.


(** ** Printing universes *)

Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ^ string_of_nat n
  end.

Definition string_of_level_expr (e : UnivExpr.t) : string :=
  let '(l, n) := e in
  string_of_level l ^ (if n =? 0 then "+" ^ string_of_nat n else "").

Definition string_of_universe_level (e : UniverseLevel.t) : string :=
  match UnivExprSet.elements e with
  | [ e ] => string_of_level_expr e
  | l => "max(" ^ string_of_list_aux string_of_level_expr ", " l ^ ")"
  end.

Definition string_of_sort_family (sf : SortFamily.t) :=
  match sf with
  | SortFamily.sfType => "Type"
  | SortFamily.sfGlobal i (* FIXME : should have a name *) => "Sort_" ^ string_of_nat i
  | SortFamily.sfVar i => "SortVar_" ^ string_of_nat i
  end.

Definition string_of_sort (u : Sort.t) :=
  match u with
  | Sort.PredicativeSort sf l =>
    string_of_sort_family sf ^ "@{" ^ string_of_universe_level l ^ "}"
  | Sort.ImpredicativeSort sf => string_of_sort_family sf
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Definition string_of_level_list u :=
  match u with
  | [] => ""
  | _ => "@{" ^ print_list string_of_level " " u ^ "}"
  end.

#[deprecated(note="Use string_of_level_list")]
Notation print_universe_instance := string_of_level_list.

Definition print_lset t :=
  print_list string_of_level " " (LevelSet.elements t).

Definition string_of_constraint_type d :=
  match d with
  | UnivConstraintType.Le n =>
    if (n =? 0)%Z then "<=" else
    if (n =? 1)%Z then "<" else
    if (n <? 0)%Z then "<=" ^ string_of_nat (Z.to_nat (Z.abs n)) ^ " + "
    else " + " ^ string_of_nat (Z.to_nat n) ^ " <= "
  | UnivConstraintType.Eq => "="
  end.

#[deprecated(note="use string_of_constraint_type")]
Notation print_constraint_type := string_of_constraint_type.

Definition string_of_constraint '(l1, d, l2) :=
  string_of_level l1 ^ " " ^ string_of_constraint_type d ^ " " ^ string_of_level l2.

Definition string_of_univ_constraint_set t :=
  print_list string_of_constraint " /\ " (UnivConstraintSet.elements t).

#[deprecated(note="use string_of_univ_constraint_set")]
Notation print_constraint_set := string_of_univ_constraint_set.




(** ** Universe Entries *)

(* FIXME : I have no clue what this correspond to *)
Inductive universes_entry :=
| Monomorphic_entry (ctx : UnivContextSet.t)
| Polymorphic_entry (names : list name) (ctx : UContext.t).

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry ctx.1.1 (Universes.AUContext.repr ctx)
  | Monomorphic_ctx ctx => Monomorphic_entry ctx
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx c => Instance.empty
  | Polymorphic_ctx c => fst (AUContext.repr c)
  end.





(** * Properties on the order ? *)

(* Lemma val_universe_sup_not_prop vv v u : *)
(*   Universe.is_prop v = false -> Universe.is_sprop v = false -> *)
(*   ∑ n, Universe.univ_val vv (Universe.sup u v) = UType n. *)
(* Proof. *)
(*   intros Hp Hsp. *)
(*   destruct u,v;cbn;try discriminate;try lia; try apply val_zero_exprs; *)
(*   eexists; eauto. *)
(* Qed. *)

(* Lemma univ_le_prop_inv {cf:checker_flags} u : (u <= UProp)%u -> u = UProp. *)
(* Proof. destruct u; simpl; try congruence; auto. Qed. *)

(* Lemma univ_le_sprop_inv {cf:checker_flags} u : (u <= USProp)%u -> u = USProp. *)
(* Proof. destruct u; simpl; try congruence; auto. Qed. *)

(* Lemma univ_prop_le_inv {cf:checker_flags} u : (UProp <= u)%u ->  *)
(*   (u = UProp \/ (prop_sub_type /\ exists n, u = UType n)). *)
(* Proof. destruct u; simpl; try congruence; auto. *)
(*   destruct prop_sub_type; firstorder auto. *)
(*   right; split; auto. exists i. auto. *)
(* Qed. *)

(* Ltac cong := intuition congruence. *)

(* Lemma univ_val_max_mon {cf:checker_flags} u u' v v' : (u <= u')%u -> (UType v <= UType v')%u ->  *)
(*   (univ_val_max u (UType v) <= univ_val_max u' (UType v'))%u. *)
(* Proof. *)
(*   intros. *)
(*   destruct u, u'; simpl in *; auto. lia. lia. *)
(* Qed. *)

Lemma leq_universe_product_mon {cf: checker_flags} ϕ u u' v v' :
  leq_universe ϕ u u' ->
  leq_universe ϕ v v' ->
  leq_universe ϕ (UniverseLevel.level_of_product u v) (UniverseLevel.level_of_product u' v').
Proof.
  unfold leq_universe in *; destruct check_univs; [|trivial].
  intros H1 H2 vv Hv. specialize (H1 _ Hv). specialize (H2 _ Hv).
  cbn in *. unfold UniverseLevel.level_of_product.
  rewrite 2!val_sup. red in H1, H2 |- *; lia.
Qed.

(* Lemma impredicative_product {cf:checker_flags} {ϕ l u} : *)
(*   Universe.is_prop u -> *)
(*   leq_universe ϕ (Universe.sort_of_product l u) u. *)
(* Proof. *)
(*   unfold Universe.sort_of_product. *)
(*   intros ->. reflexivity. *)
(* Qed. *)

Section UniverseLevelLemmas.
  Context {cf:checker_flags}.

  Ltac unfold_eq_universe
    := unfold eq_universe in *; destruct check_univs; [intros v Hv|trivial].

  Lemma sup_idem s : UniverseLevel.sup s s = s.
  Proof.
    apply eq_univ'; cbn.
    intro; rewrite !UnivExprSet.union_spec. intuition.
  Qed.

  Lemma level_of_product_idem s
    : UniverseLevel.level_of_product s s = s.
  Proof. apply sup_idem. Qed.

  Lemma sup_assoc s1 s2 s3 :
    UniverseLevel.sup s1 (UniverseLevel.sup s2 s3) = UniverseLevel.sup (UniverseLevel.sup s1 s2) s3.
  Proof.
    apply eq_univ'; cbn. symmetry; apply UnivExprSetProp.union_assoc.
  Qed.

  Instance universe_sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) UniverseLevel.sup.
  Proof.
    intros s1 s1' H1 s2 s2' H2.
    unfold_eq_universe. specialize (H1 v Hv). specialize (H2 v Hv).
    rewrite !val_sup.
    now rewrite -> H1, H2.
  Qed.

  Lemma sort_of_product_twice u s :
    UniverseLevel.level_of_product u (UniverseLevel.level_of_product u s)
    = UniverseLevel.level_of_product u s.
  Proof.
    destruct u,s;auto.
    unfold UniverseLevel.level_of_product;cbn.
    now rewrite -> sup_assoc, sup_idem.
  Qed.
End UniverseLevelLemmas.


Section no_prop_leq_type.
  Context {cf:checker_flags}.
  Context (ϕ : UnivConstraintSet.t).

  Lemma succ_inj x y : UnivExpr.succ x = UnivExpr.succ y -> x = y.
  Proof.
    unfold UnivExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x : 
    UnivExprSet.In x (UniverseLevel.map UnivExpr.succ l) <-> 
    exists x', UnivExprSet.In x' l /\ x = UnivExpr.succ x'.
  Proof.
    rewrite UniverseLevel.map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (UnivExpr.succ l) = val v l + 1.
  Proof.
    destruct l as []; simpl. cbn. lia. 
  Qed.

  Lemma val_map_succ v l : val v (UniverseLevel.map UnivExpr.succ l) = val v l + 1.
  Proof.
    remember (UniverseLevel.map UnivExpr.succ l) eqn:eq.
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
    leq_universe ϕ (UniverseLevel.super u) (UniverseLevel.super u').
  Proof.
    unfold leq_universe. destruct check_univs; [|trivial].
    intros H v Hv. specialize (H v Hv). simpl in *.
    rewrite !val_map_succ; red in H |- *; lia.
  Qed.

  (* Lemma leq_universe_props u1 u2 : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ u1 u2 -> *)
  (*   match u1, u2 with *)
  (*   | UniverseLevel.lProp, UniverseLevel.lProp => True *)
  (*   | UniverseLevel.lSProp, UniverseLevel.lSProp => True *)
  (*   | UniverseLevel.lProp, UniverseLevel.lSProp => False *)
  (*   | UniverseLevel.lSProp, UniverseLevel.lProp => False *)
  (*   | UniverseLevel.lProp, UniverseLevel.lType _ => prop_sub_type *)
  (*   | UniverseLevel.lSProp, UniverseLevel.lType _ => False *)
  (*   | UniverseLevel.lType l, UniverseLevel.lType l' => True *)
  (*   | UniverseLevel.lType _, _ => False *)
  (*   end. *)
  (* Proof. *)
  (*   intros cu [v Hv]. *)
  (*   unfold leq_universe. rewrite cu. *)
  (*   intros Hle. specialize (Hle _ Hv). *)
  (*   destruct u1, u2; simpl; auto. *)
  (*   simpl in Hle. now destruct prop_sub_type. *)
  (* Qed. *)

  (* Lemma leq_universe_prop_r u1 u2 : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ u1 u2 -> *)
  (*   UniverseLevel.is_prop u2 -> UniverseLevel.is_prop u1. *)
  (* Proof. *)
  (*   intros Hcf cu le. *)
  (*   apply leq_universe_props in le; auto. *)
  (*   destruct u1, u2; simpl in *; auto. *)
  (* Qed. *)

  (* Lemma leq_universe_sprop_r u1 u2 : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ u1 u2 -> *)
  (*   UniverseLevel.is_sprop u2 -> UniverseLevel.is_sprop u1. *)
  (* Proof. *)
  (*   intros Hcf cu le. *)
  (*   apply leq_universe_props in le; auto. *)
  (*   destruct u1, u2; simpl in *; auto. *)
  (* Qed. *)
  
  (* Lemma leq_universe_prop_no_prop_sub_type u1 u2 : *)
  (*   check_univs -> *)
  (*   prop_sub_type = false -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ u1 u2 -> *)
  (*   UniverseLevel.is_prop u1 -> UniverseLevel.is_prop u2. *)
  (* Proof. *)
  (*   intros Hcf cu ps le. *)
  (*   apply leq_universe_props in le; auto. *)
  (*   destruct u1, u2; simpl in *; auto. *)
  (*   cong. *)
  (* Qed. *)

  (* Lemma leq_universe_sprop_l u1 u2 : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ u1 u2 -> *)
  (*   UniverseLevel.is_sprop u1 -> UniverseLevel.is_sprop u2. *)
  (* Proof. *)
  (*   intros Hcf cu le. *)
  (*   apply leq_universe_props in le; auto. *)
  (*   destruct u1, u2; simpl in *; auto. *)
  (* Qed. *)

  (* Hint Resolve leq_universe_sprop_l leq_universe_sprop_r *)
  (*      leq_universe_prop_r *)
  (*      leq_universe_prop_no_prop_sub_type *)
  (*      : univ_lemmas. *)
  
  (* Lemma leq_prop_prop {l l'} : *)
  (*   UniverseLevel.is_prop l -> UniverseLevel.is_prop l' -> *)
  (*   leq_universe ϕ l l'. *)
  (* Proof. *)
  (*   red. destruct check_univs; [|trivial]. *)
  (*   intros H1 H2 v Hv. eapply is_prop_val in H1; eapply is_prop_val in H2. *)
  (*   rewrite H1, H2. lle; lia. *)
  (* Qed. *)

  (* Lemma leq_sprop_sprop {l l'} : *)
  (*   UniverseLevel.is_sprop l -> UniverseLevel.is_sprop l' -> *)
  (*   leq_universe ϕ l l'. *)
  (* Proof. *)
  (*   red. destruct check_univs; [|trivial]. *)
  (*   intros H1 H2 v Hv. eapply is_sprop_val in H1; eapply is_sprop_val in H2. *)
  (*   rewrite H1, H2. lle; lia. *)
  (* Qed. *)
  
  (* Lemma leq_prop_is_prop_sprop {x s} : *)
  (*   check_univs -> *)
  (*   prop_sub_type = false -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ x s -> *)
  (*   (UniverseLevel.is_prop s \/ UniverseLevel.is_sprop s <-> UniverseLevel.is_prop x \/ UniverseLevel.is_sprop x). *)
  (* Proof. *)
  (*   intros H H0 H1 H2; split;intros Hor; destruct Hor; eauto with univ_lemmas. *)
  (* Qed. *)

  (* Lemma is_prop_gt l l' : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ (UniverseLevel.super l) l' -> UniverseLevel.is_prop l' -> False. *)
  (* Proof. *)
  (*   intros Hcf [v Hv] H1 H2. unfold leq_universe in *; rewrite Hcf in *. *)
  (*   eapply is_prop_val with (v:=v) in H2. specialize (H1 _ Hv). *)
  (*   rewrite H2 in H1. destruct l as [| |]; destruct l'; lle; cbn -[Z.add] in *; lia. *)
  (* Qed. *)
  
  (* Lemma is_sprop_gt l l' : *)
  (*   check_univs -> *)
  (*   consistent ϕ -> *)
  (*   leq_universe ϕ (UniverseLevel.super l) l' -> UniverseLevel.is_sprop l' -> False. *)
  (* Proof. *)
  (*   intros Hcf [v Hv] H1 H2. unfold leq_universe in *; rewrite Hcf in *. *)
  (*   eapply is_sprop_val with (v:=v) in H2. specialize (H1 _ Hv). *)
  (*   rewrite H2 in H1. destruct l as [| |]; destruct l'; lle; cbn -[Z.add] in *; lia. *)
  (* Qed. *)

End no_prop_leq_type.
