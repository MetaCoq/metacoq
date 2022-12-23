(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils BasicAst Universes Primitive.
From MetaCoq.PCUIC Require Import Environment.
From Equations Require Import Equations.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition declared_constant_gen (lookup : kername -> option global_decl) (id : kername) decl : Prop :=
    lookup id = Some (ConstantDecl decl).

  Definition declared_constant (Σ : global_env) := declared_constant_gen (lookup_env Σ).

  Definition declared_minductive_gen (lookup : kername -> option global_decl) mind decl :=
    lookup mind = Some (InductiveDecl decl).

  Definition declared_minductive Σ := declared_minductive_gen (lookup_env Σ).

  Definition declared_inductive_gen lookup ind mdecl decl :=
    declared_minductive_gen lookup (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_inductive Σ := declared_inductive_gen (lookup_env Σ).

  Definition declared_constructor_gen lookup cstr mdecl idecl cdecl : Prop :=
    declared_inductive_gen lookup (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_constructor Σ := declared_constructor_gen (lookup_env Σ).

  Definition declared_projection_gen lookup (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor_gen lookup (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition declared_projection Σ := declared_projection_gen (lookup_env Σ).

  Definition lookup_constant_gen (lookup : kername -> option global_decl) kn :=
    match lookup kn with
    | Some (ConstantDecl d) => Some d
    | _ => None
    end.

  Definition lookup_constant Σ := lookup_constant_gen (lookup_env Σ).

  Definition lookup_minductive_gen (lookup : kername -> option global_decl) mind :=
    match lookup mind with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_minductive Σ := lookup_minductive_gen (lookup_env Σ).

  Definition lookup_inductive_gen lookup ind :=
    match lookup_minductive_gen lookup (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.

  Definition lookup_inductive Σ := lookup_inductive_gen (lookup_env Σ).

  Definition lookup_constructor_gen lookup ind k :=
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match nth_error idecl.(ind_ctors) k with
      | Some cdecl => Some (mdecl, idecl, cdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_constructor Σ := lookup_constructor_gen (lookup_env Σ).

  Definition lookup_projection_gen lookup p :=
    match lookup_constructor_gen lookup p.(proj_ind) 0 with
    | Some (mdecl, idecl, cdecl) =>
      match nth_error idecl.(ind_projs) p.(proj_arg) with
      | Some pdecl => Some (mdecl, idecl, cdecl, pdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_projection Σ := lookup_projection_gen (lookup_env Σ).

  Lemma declared_constant_lookup {lookup kn cdecl} :
    declared_constant_gen lookup kn cdecl ->
    lookup_constant_gen lookup kn = Some cdecl.
  Proof.
    unfold declared_constant_gen, lookup_constant_gen.
    now intros ->.
  Qed.

  Lemma lookup_constant_declared {lookup kn cdecl} :
    lookup_constant_gen lookup kn = Some cdecl ->
    declared_constant_gen lookup kn cdecl.
  Proof.
    unfold declared_constant_gen, lookup_constant_gen.
    destruct lookup as [[]|] => //. congruence.
  Qed.

  Lemma declared_minductive_lookup {lookup ind mdecl} :
    declared_minductive_gen lookup ind mdecl ->
    lookup_minductive_gen lookup ind = Some mdecl.
  Proof.
    rewrite /declared_minductive_gen /lookup_minductive_gen.
    now intros ->.
  Qed.

  Lemma lookup_minductive_declared {lookup ind mdecl} :
    lookup_minductive_gen lookup ind = Some mdecl ->
    declared_minductive_gen lookup ind mdecl.
  Proof.
    rewrite /declared_minductive_gen /lookup_minductive_gen.
    destruct lookup as [[]|] => //. congruence.
  Qed.

  Lemma declared_inductive_lookup {lookup ind mdecl idecl} :
    declared_inductive_gen lookup ind mdecl idecl ->
    lookup_inductive_gen lookup ind = Some (mdecl, idecl).
  Proof.
    rewrite /declared_inductive_gen /lookup_inductive_gen.
    intros []. now rewrite (declared_minductive_lookup H) H0.
  Qed.

  Lemma lookup_inductive_declared {lookup ind mdecl idecl} :
    lookup_inductive_gen lookup ind = Some (mdecl, idecl) ->
    declared_inductive_gen lookup ind mdecl idecl.
  Proof.
    rewrite /declared_inductive_gen /lookup_inductive_gen.
    destruct lookup_minductive_gen as [[]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    split => //.
    apply (lookup_minductive_declared hl).
  Qed.

  Lemma declared_constructor_lookup {lookup id mdecl idecl cdecl} :
    declared_constructor_gen lookup id mdecl idecl cdecl ->
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl).
  Proof.
    intros []. unfold lookup_constructor_gen.
    rewrite (declared_inductive_lookup (lookup := lookup) H) /= H0 //.
  Qed.

  Lemma lookup_constructor_declared {lookup id mdecl idecl cdecl} :
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl) ->
    declared_constructor_gen lookup id mdecl idecl cdecl.
  Proof.
    unfold lookup_constructor_gen.
    destruct lookup_inductive_gen as [[]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    split => //.
    apply (lookup_inductive_declared hl). congruence.
  Qed.

  Lemma declared_projection_lookup {lookup p mdecl idecl cdecl pdecl} :
    declared_projection_gen lookup p mdecl idecl cdecl pdecl ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl).
  Proof.
    intros [? []]. unfold lookup_projection_gen.
    rewrite (declared_constructor_lookup (lookup := lookup) H) /= H0 //.
  Qed.

  Lemma lookup_projection_declared {lookup p mdecl idecl cdecl pdecl} :
    ind_npars mdecl = p.(proj_npars) ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl) ->
    declared_projection_gen lookup p mdecl idecl cdecl pdecl.
  Proof.
    intros hp. unfold lookup_projection_gen.
    destruct lookup_constructor_gen as [[[] ?]|] eqn:hl => //=.
    destruct nth_error eqn:hnth => //. intros [= <- <-]. subst c p0.
    split => //.
    apply (lookup_constructor_declared (id:=(proj_ind p, 0)) hl).
  Qed.

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  (* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

  Definition global_levels (univs : ContextSet.t) : LevelSet.t :=
    LevelSet.union (ContextSet.levels univs) (LevelSet.singleton (Level.lzero)).

  Lemma global_levels_InSet Σ :
    LevelSet.In Level.lzero (global_levels Σ).
  Proof.
    apply LevelSet.union_spec; right.
    now apply LevelSet.singleton_spec.
  Qed.

  Lemma global_levels_memSet univs :
    LevelSet.mem Level.lzero (global_levels univs) = true.
  Proof.
    apply LevelSet.mem_spec, global_levels_InSet.
  Qed.

  (** One can compute the constraints associated to a global environment or its
      extension by folding over its constituent definitions.

      We make *only* the second of these computations an implicit coercion
      for more readability. Note that [fst_ctx] is also a coercion which goes
      from a [global_env_ext] to a [global_env]: coercion coherence would *not*
      be ensured if we added [global_constraints] as well as a coercion, as it
      would forget the extension's constraints. *)

  Definition global_constraints (Σ : global_env) : ConstraintSet.t :=
    snd Σ.(universes).

  Definition global_uctx (Σ : global_env) : ContextSet.t :=
    (global_levels Σ.(universes), global_constraints Σ).

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1.(universes)).

  Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t :=
    ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

  Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t :=
    (global_ext_levels Σ, global_ext_constraints Σ).


  Lemma global_ext_levels_InSet Σ :
    LevelSet.In Level.lzero (global_ext_levels Σ).
  Proof.
    apply LevelSet.union_spec; right.
    now apply global_levels_InSet.
  Qed.

  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx => List.length u = 0
    | Polymorphic_ctx c =>
      (* levels of the instance already declared *)
      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

  Lemma consistent_instance_length {cf : checker_flags} {Σ : global_env_ext} {univs u} :
    consistent_instance_ext Σ univs u ->
    #|u| = #|abstract_instance univs|.
  Proof.
    unfold consistent_instance_ext, consistent_instance.
    destruct univs; simpl; auto.
    intros [_ [H _]].
    destruct cst; simpl in *.
    now rewrite H; cbn; autorewrite with len.
  Qed.

  Definition wf_universe Σ s : Prop :=
    Universe.on_sort
      (fun u => forall l, LevelExprSet.In l u -> LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ))
      True s.

  Lemma declared_ind_declared_constructors `{cf : checker_flags} {Σ ind mib oib} :
    declared_inductive Σ ind mib oib ->
    Alli (fun i => declared_constructor Σ (ind, i) mib oib) 0 (ind_ctors oib).
  Proof using.
    move=> inddecl.
    apply: forall_nth_error_Alli=> /= i x eq.
    apply: lookup_constructor_declared=> /=.
    rewrite /lookup_constructor_gen (declared_inductive_lookup inddecl) eq //.
  Qed.

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).

  Import T E TU.

  Section TypeLocal.
    Context (typing : forall (Γ : context), term -> typ_or_sort -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ t Sort ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ t Sort ->
        typing Γ b (Typ t) ->
        All_local_env (Γ ,, vdef na b t).
  Derive Signature NoConfusion for All_local_env.
  End TypeLocal.

  Arguments localenv_nil {_}.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.
  Arguments localenv_cons_abs {_ _ _ _} _ _.

  Lemma All_local_env_fold P f Γ :
    All_local_env (fun Γ t T => P (fold_context_k f Γ) (f #|Γ| t) (typ_or_sort_map (f #|Γ|) T)) Γ <~>
    All_local_env P (fold_context_k f Γ).
  Proof.
    split.
    - induction 1; simpl; try unfold snoc; rewrite ?fold_context_k_snoc0; try constructor; auto.
    - induction Γ; simpl; try unfold snoc; rewrite ?fold_context_k_snoc0; intros H.
      * constructor.
      * destruct a as [na [b|] ty]; depelim H; specialize (IHΓ H); constructor; simpl; auto.
  Qed.

  Lemma All_local_env_impl (P Q : context -> term -> typ_or_sort -> Type) l :
    All_local_env P l ->
    (forall Γ t T, P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
  Proof.
    induction 1; intros; simpl; econstructor; eauto.
  Qed.

  Lemma All_local_env_impl_ind {P Q : context -> term -> typ_or_sort -> Type} {l} :
    All_local_env P l ->
    (forall Γ t T, All_local_env Q Γ -> P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
  Proof.
    induction 1; intros; simpl; econstructor; eauto.
  Qed.

  Lemma All_local_env_skipn P Γ : All_local_env P Γ -> forall n, All_local_env P (skipn n Γ).
  Proof.
    induction 1; simpl; intros; destruct n; simpl; try econstructor; eauto.
  Qed.
  #[global]
  Hint Resolve All_local_env_skipn : wf.

  Section All_local_env_rel.

    Definition All_local_rel P Γ Γ'
      := (All_local_env (fun Γ0 t T => P (Γ ,,, Γ0) t T) Γ').

    Definition All_local_rel_nil {P Γ} : All_local_rel P Γ []
      := localenv_nil.

    Definition All_local_rel_abs {P Γ Γ' A na} :
      All_local_rel P Γ Γ' -> P (Γ ,,, Γ') A Sort
      -> All_local_rel P Γ (Γ',, vass na A)
      := localenv_cons_abs.

    Definition All_local_rel_def {P Γ Γ' t A na} :
      All_local_rel P Γ Γ' ->
      P (Γ ,,, Γ') A Sort ->
      P (Γ ,,, Γ') t (Typ A) ->
      All_local_rel P Γ (Γ',, vdef na t A)
      := localenv_cons_def.

    Lemma All_local_rel_local :
      forall P Γ,
        All_local_env P Γ ->
        All_local_rel P [] Γ.
    Proof.
      intros P Γ h. eapply All_local_env_impl.
      - exact h.
      - intros Δ t [] h'.
        all: cbn.
        + rewrite app_context_nil_l. assumption.
        + rewrite app_context_nil_l. assumption.
    Defined.

    Lemma All_local_local_rel P Γ :
      All_local_rel P [] Γ -> All_local_env P Γ.
    Proof.
      intro X. eapply All_local_env_impl. exact X.
      intros Γ0 t [] XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
    Defined.

    Lemma All_local_app_rel {P Γ Γ'} :
      All_local_env P (Γ ,,, Γ') -> All_local_env P Γ × All_local_rel P Γ Γ'.
    Proof.
      induction Γ'.
      - intros hΓ.
        split.
        1: exact hΓ.
        constructor.
      - inversion 1 ; subst.
        all: edestruct IHΓ' ; auto.
        all: split ; auto.
        all: constructor ; auto.
    Defined.

    Lemma All_local_rel_app {P Γ Γ'} :
      All_local_env P Γ -> All_local_rel P Γ Γ' -> All_local_env P (Γ ,,, Γ').
    Proof.
      intros ? hΓ'.
      induction hΓ'.
      - assumption.
      - cbn.
        constructor ; auto.
      - cbn.
        constructor ; auto.
    Defined.

  End All_local_env_rel.

  (** Well-formedness of local environments embeds a sorting for each variable *)

  Definition on_local_decl (P : context -> term -> typ_or_sort -> Type) Γ d :=
    match d.(decl_body) with
    | Some b => P Γ b (Typ d.(decl_type))
    | None => P Γ d.(decl_type) Sort
    end.

  Definition on_def_type (P : context -> term -> typ_or_sort -> Type) Γ d :=
    P Γ d.(dtype) Sort.

  Definition on_def_body (P : context -> term -> typ_or_sort -> Type) types Γ d :=
    P (Γ ,,, types) d.(dbody) (Typ (lift0 #|types| d.(dtype))).

  Definition lift_judgment
    (check : global_env_ext -> context -> term -> term -> Type)
    (infer_sort : global_env_ext -> context -> term -> Type) :
    (global_env_ext -> context -> term -> typ_or_sort -> Type) :=
    fun Σ Γ t T =>
    match T with
    | Typ T => check Σ Γ t T
    | Sort => infer_sort Σ Γ t
    end.

  Lemma lift_judgment_impl {P Ps Q Qs Σ Σ' Γ Γ' t t' T} :
    lift_judgment P Ps Σ Γ t T ->
    (forall T, P Σ Γ t T -> Q Σ' Γ' t' T) ->
    (Ps Σ Γ t -> Qs Σ' Γ' t') ->
    lift_judgment Q Qs Σ' Γ' t' T.
  Proof.
    intros HT HPQ HPsQs.
    destruct T; simpl.
    * apply HPQ, HT.
    * apply HPsQs, HT.
  Qed.

  (* Common uses *)

  Definition lift_wf_term wf_term := (lift_judgment (fun Σ Γ t T => wf_term Σ Γ t × wf_term Σ Γ T) wf_term).

  Definition infer_sort (sorting : global_env_ext -> context -> term -> Universe.t -> Type) := (fun Σ Γ T => { s : Universe.t & sorting Σ Γ T s }).
  Notation typing_sort typing := (fun Σ Γ T s => typing Σ Γ T (tSort s)).

  Definition lift_typing typing := lift_judgment typing (infer_sort (typing_sort typing)).
  Definition lift_sorting checking sorting := lift_judgment checking (infer_sort sorting).

  Notation Prop_conj P Q := (fun Σ Γ t T => P Σ Γ t T × Q Σ Γ t T).

  Definition lift_typing2 P Q := lift_typing (Prop_conj P Q).

  Lemma infer_sort_impl {P Q} {Σ Σ' : global_env_ext} {Γ Γ' : context} {t t' : term} :
    forall f, forall tu: infer_sort P Σ Γ t,
    let s := tu.π1 in
    (P Σ Γ t s -> Q Σ' Γ' t' (f s)) ->
    infer_sort Q Σ' Γ' t'.
  Proof.
    intros ? (? & Hs) s HPQ. eexists. now apply HPQ.
  Qed.

  Lemma infer_typing_sort_impl {P Q} {Σ Σ' : global_env_ext} {Γ Γ' : context} {t t' : term} :
    forall f, forall tu: infer_sort (typing_sort P) Σ Γ t,
    let s := tu.π1 in
    (P Σ Γ t (tSort s) -> Q Σ' Γ' t' (tSort (f s))) ->
    infer_sort (typing_sort Q) Σ' Γ' t'.
  Proof.
    apply (infer_sort_impl (P := typing_sort P) (Q := typing_sort Q)).
  Qed.

  Lemma lift_typing_impl {P Q Σ Σ' Γ Γ' t t' T} :
    lift_typing P Σ Γ t T ->
    (forall T, P Σ Γ t T -> Q Σ' Γ' t' T) ->
    lift_typing Q Σ' Γ' t' T.
  Proof.
    intros HT HPQ.
    apply lift_judgment_impl with (1 := HT); tas.
    intro Hs; apply infer_typing_sort_impl with id Hs; apply HPQ.
  Qed.

  Section TypeLocalOver.
    Context (checking : global_env_ext -> context -> term -> term -> Type).
    Context (sorting : global_env_ext -> context -> term -> Type).
    Context (cproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_judgment checking sorting Σ) Γ ->
                forall (t T : term), checking Σ Γ t T -> Type).
    Context (sproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_judgment checking sorting Σ) Γ ->
                forall (t : term), sorting Σ Γ t -> Type).

    Inductive All_local_env_over_gen (Σ : global_env_ext) :
        forall (Γ : context), All_local_env (lift_judgment checking sorting Σ) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over_gen Σ [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_judgment checking sorting Σ) Γ) :
        All_local_env_over_gen Σ Γ all ->
        forall (tu : lift_judgment checking sorting Σ Γ t Sort)
          (Hs: sproperty Σ Γ all _ tu),
          All_local_env_over_gen Σ (Γ ,, vass na t)
                              (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_judgment checking sorting Σ) Γ) (tb : checking Σ Γ b t) :
        All_local_env_over_gen Σ Γ all ->
        forall (Hc: cproperty Σ Γ all _ _ tb),
        forall (tu : lift_judgment checking sorting Σ Γ t Sort)
          (Hs: sproperty Σ Γ all _ tu),
          All_local_env_over_gen Σ (Γ ,, vdef na b t)
                              (localenv_cons_def all tu tb).

  End TypeLocalOver.
  Derive Signature for All_local_env_over_gen.

  Definition All_local_env_over typing property :=
    (All_local_env_over_gen typing (infer_sort (typing_sort typing)) property (fun Σ Γ H t tu => property _ _ H _ _ tu.π2)).

  Definition All_local_env_over_sorting checking sorting cproperty (sproperty : forall Σ Γ _ t s, sorting Σ Γ t s -> Type) :=
    (All_local_env_over_gen checking (infer_sort sorting) cproperty (fun Σ Γ H t tu => sproperty Σ Γ H t tu.π1 tu.π2)).

  Section TypeCtxInst.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

    (* Γ |- s : Δ, where Δ is a telescope (reverse context) *)
    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ :
        typing Σ Γ i t ->
        ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
        ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
        ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
        ctx_inst Σ Γ inst (vdef na b t :: Δ).
    Derive Signature NoConfusion for ctx_inst.
  End TypeCtxInst.

  Lemma ctx_inst_impl P Q Σ Γ inst Δ :
    ctx_inst P Σ Γ inst Δ ->
    (forall t T, P Σ Γ t T -> Q Σ Γ t T) ->
    ctx_inst Q Σ Γ inst Δ.
  Proof.
    intros H HPQ. induction H; econstructor; auto.
  Qed.

  Section All_local_env_size.
    Context {P : forall (Σ : global_env_ext) (Γ : context), term -> typ_or_sort -> Type}.
    Context (Psize : forall (Σ : global_env_ext) Γ t T, P Σ Γ t T -> size).

    Fixpoint All_local_env_size_gen base Σ Γ (w : All_local_env (P Σ) Γ) : size :=
      match w with
      | localenv_nil => base
      | localenv_cons_abs Γ' na t w' p => Psize _ _ _ _ p + All_local_env_size_gen base _ _ w'
      | localenv_cons_def Γ' na b t w' pt pb => Psize _ _ _ _ pt + Psize _ _ _ _ pb + All_local_env_size_gen base _ _ w'
      end.

    Lemma All_local_env_size_pos base Σ Γ w : base <= All_local_env_size_gen base Σ Γ w.
    Proof using Type.
      induction w.
      all: simpl ; lia.
    Qed.
  End All_local_env_size.

  Notation All_local_rel_size_gen Psize base := (fun Σ Γ Δ (w : All_local_rel _ Γ Δ) =>
    All_local_env_size_gen (fun Σ Δ => Psize Σ (Γ ,,, Δ)) base Σ Δ w).

  Lemma All_local_env_size_app P Psize base Σ Γ Γ' (wfΓ : All_local_env (P Σ) Γ) (wfΓ' : All_local_rel (P Σ) Γ Γ') :
    All_local_env_size_gen Psize base _ _ (All_local_rel_app wfΓ wfΓ') + base = All_local_env_size_gen Psize base _ _ wfΓ + All_local_rel_size_gen Psize base _ _ _ wfΓ'.
  Proof.
    induction Γ'.
    - dependent inversion wfΓ'.
      reflexivity.
    - revert IHΓ'.
      dependent inversion wfΓ' ; subst ; intros.
      + cbn.
        etransitivity.
        2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
        reflexivity.
      + cbn.
        etransitivity.
        2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
        reflexivity.
  Qed.

  Section lift_judgment_size.
    Context {checking : global_env_ext -> context -> term -> term -> Type}.
    Context {sorting : global_env_ext -> context -> term -> Type}.
    Context (csize : forall (Σ : global_env_ext) (Γ : context) (t T : term), checking Σ Γ t T -> size).
    Context (ssize : forall (Σ : global_env_ext) (Γ : context) (t : term), sorting Σ Γ t -> size).

    Definition lift_judgment_size Σ Γ t T (w : lift_judgment checking sorting Σ Γ t T) : size :=
      match T return lift_judgment checking sorting Σ Γ t T -> size with
      | Typ T => csize _ _ _ _
      | Sort => ssize _ _ _
      end w.
  End lift_judgment_size.

  Implicit Types (Σ : global_env_ext) (Γ : context) (t : term).

  Notation infer_sort_size  typing_size := (fun Σ Γ t   (tu: infer_sort _ Σ Γ t) => let 'existT s d := tu in typing_size Σ Γ t s d).
  Notation typing_sort_size typing_size := (fun Σ Γ t s (tu: typing_sort _ Σ Γ t s) => typing_size Σ Γ t (tSort s) tu).

  Section Regular.
    Context {typing : global_env_ext -> context -> term -> term -> Type}.
    Context (typing_size : forall Σ Γ t T, typing Σ Γ t T -> size).

    Definition lift_typing_size := lift_judgment_size typing_size (infer_sort_size (typing_sort_size typing_size)).
    Definition All_local_env_size := All_local_env_size_gen lift_typing_size 0.
    Definition All_local_rel_size := All_local_rel_size_gen lift_typing_size 0.
  End Regular.

  Section Bidirectional.
    Context {checking : global_env_ext -> context -> term -> term -> Type} {sorting : global_env_ext -> context -> term -> Universe.t -> Type}.
    Context (checking_size : forall Σ Γ t T, checking Σ Γ t T -> size).
    Context (sorting_size : forall Σ Γ t s, sorting Σ Γ t s -> size).

    Definition lift_sorting_size := lift_judgment_size checking_size (infer_sort_size sorting_size).
    Definition All_local_env_sorting_size := All_local_env_size_gen lift_sorting_size 1.
    Definition All_local_rel_sorting_size := All_local_rel_size_gen lift_sorting_size 1.
  End Bidirectional.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
  Include EnvTyping T E TU.
End EnvTypingSig.

Module Conversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Import T E TU ET.

  Section Conversion.
  Context (cumul_gen : global_env_ext -> context -> conv_pb -> term -> term -> Type).

  Inductive All_decls_alpha_pb {pb} {P : conv_pb -> term -> term -> Type} :
    context_decl -> context_decl -> Type :=
  | all_decls_alpha_vass {na na' : binder_annot name} {t t' : term}
    (eqna : eq_binder_annot na na')
    (eqt : P pb t t') :
    All_decls_alpha_pb (vass na t) (vass na' t')

  | all_decls_alpha_vdef {na na' : binder_annot name} {b t b' t' : term}
    (eqna : eq_binder_annot na na')
    (eqb : P Conv b b') (* Note that definitions must be convertible, otherwise this notion
    of cumulativity is useless *)
    (eqt : P pb t t') :
    All_decls_alpha_pb (vdef na b t) (vdef na' b' t').

  Derive Signature NoConfusion for All_decls_alpha_pb.

  Arguments All_decls_alpha_pb pb P : clear implicits.

  Definition cumul_pb_decls pb (Σ : global_env_ext) (Γ Γ' : context) : forall (x y : context_decl), Type :=
    All_decls_alpha_pb pb (cumul_gen Σ Γ).

  Definition cumul_pb_context pb (Σ : global_env_ext) :=
    All2_fold (cumul_pb_decls pb Σ).

  Definition cumul_ctx_rel Σ Γ Δ Δ' :=
    All2_fold (fun Δ Δ' => cumul_pb_decls Cumul Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ'.
  End Conversion.

  Arguments All_decls_alpha_pb pb P : clear implicits.
  Notation conv cumul_gen Σ Γ := (cumul_gen Σ Γ Conv).
  Notation cumul cumul_gen Σ Γ := (cumul_gen Σ Γ Cumul).

  Notation conv_decls cumul_gen := (cumul_pb_decls cumul_gen Conv).
  Notation cumul_decls cumul_gen := (cumul_pb_decls cumul_gen Cumul).
  Notation conv_context cumul_gen Σ := (cumul_pb_context cumul_gen Conv Σ).
  Notation cumul_context cumul_gen Σ := (cumul_pb_context cumul_gen Cumul Σ).

End Conversion.

Module Type ConversionSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Include Conversion T E TU ET.
End ConversionSig.


Module GlobalMaps (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  (** *** Typing of inductive declarations *)
  Import T E TU ET C L.

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type).
    Context (P : global_env_ext -> context -> term -> typ_or_sort -> Type).
    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

    (** For well-formedness of inductive declarations we need a way to check that a assumptions
      of a given context is typable in a sort [u]. We also force well-typing of the let-ins
      in any universe to imply wf_local. *)
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : Universe.t) : Type :=
      match Δ with
      | [] => wf_universe Σ u
      | {| decl_body := None;   decl_type := t |} :: Δ => type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) t (Typ (tSort u))
      | {| decl_body := Some b; decl_type := t |} :: Δ => type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) t Sort × P Σ (Γ ,,, Δ) b (Typ t)
      end.

    Fixpoint sorts_local_ctx Σ (Γ Δ : context) (us : list Universe.t) : Type :=
      match Δ, us with
      | [], [] => unit
      | {| decl_body := None;   decl_type := t |} :: Δ, u :: us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) t (Typ (tSort u))
      | {| decl_body := Some b; decl_type := t |} :: Δ, us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) t Sort × P Σ (Γ ,,, Δ) b (Typ t)
      | _, _ => False
      end.

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body).

    Definition on_type Σ Γ T := P Σ Γ T Sort.

    Open Scope type_scope.

    Definition univs_ext_constraints univs φ :=
      ConstraintSet.union (constraints_of_udecl φ) univs.

    Definition satisfiable_udecl (univs : ContextSet.t) φ
      := consistent (univs_ext_constraints (ContextSet.constraints univs) φ).

    (* Constraints from udecl between *global* universes
       are implied by the constraints in univs *)
    Definition valid_on_mono_udecl (univs : ContextSet.t) ϕ :=
      consistent_extension_on univs (constraints_of_udecl ϕ).

    (* Check that: *)
    (*   - declared levels are fresh *)
    (*   - all levels used in constraints are declared *)
    Definition on_udecl (univs : ContextSet.t) (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels univs in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ ConstraintSet.For_all (declared_cstr_levels all_levels) (constraints_of_udecl udecl)
        /\ satisfiable_udecl univs udecl
        /\ valid_on_mono_udecl univs udecl.

    (** Positivity checking of the inductive, ensuring that the inductive itself
      can only appear at the right of an arrow in each argument's types. *)
    (*
    Definition positive_cstr_arg ninds npars narg (arg : term) : bool :=
      (* We decompose the constructor's arguments' type and verify the inductive references
        only appear in the conclusion, if any. *)
      let (ctx, concl) := decompose_prod_assum [] arg in
      (* Again, we smash the context, as Coq does *)
      let ctx := smash_context [] ctx in
      alli (fun i d => noccur_between (npars + narg + i) ninds d.(decl_type)) 0 (List.rev ctx) &&
      let (hd, args) := decompose_app concl in
      match hd with
      | tRel i =>
        if noccur_between (npars + narg + #|ctx|) ninds (tRel i) then
          (* Call to an unrelated variable *)
          true
        else (* Recursive call to the inductive *)
          (* Coq disallows the inductive to be applied to another inductive in the block *)
          forallb (noccur_between (npars + narg + #|ctx|) ninds) args
      | tInd ind u =>
        if forallb (noccur_between (npars + narg + #|ctx|) ninds) args then
          (* Unrelated inductive *)
          true
        else (* Nested inductive *)
          true
      end.

    Definition positive_cstr_args ninds npars (args : context) : bool :=
      alli (fun i decl => positive_cstr_arg nind npars i decl.(decl_type))
      (* We smash the context, just as Coq's kernel computes positivity on
        weak-head normalized types *)
      (List.rev (smash_context [] args))
    *)

    (** A constructor argument type [t] is positive w.r.t. an inductive block [mdecl]
      when it's zeta-normal form is of the shape Π Δ. concl and:
        - [t] does not refer to any inductive in the block.
          In that case [t] must be a closed type under the context of parameters and
          previous arguments.
        - None of the variable assumptions in Δ refer to any inductive in the block,
          but the conclusion [concl] is of the form [mkApps (tRel k) args] for k
          refering to an inductive in the block, and none of the arguments [args]
          refer to the inductive. #|args| must be the length of the full inductive application.

      Let-in assumptions in Δ are systematically unfolded, i.e. we really consider:
      the zeta-reduction of [t]. *)

    Definition ind_realargs (o : one_inductive_body) :=
      match destArity [] o.(ind_type) with
      | Some (ctx, _) => #|smash_context [] ctx|
      | _ => 0
      end.

    Inductive positive_cstr_arg mdecl ctx : term -> Type :=
    | positive_cstr_arg_closed t :
      closedn #|ctx| t ->
      positive_cstr_arg mdecl ctx t

    | positive_cstr_arg_concl l k i :
      (** Mutual inductive references in the conclusion are ok *)
      #|ctx| <= k -> k < #|ctx| + #|mdecl.(ind_bodies)| ->
      All (closedn #|ctx|) l ->
      nth_error (List.rev mdecl.(ind_bodies)) (k - #|ctx|) = Some i ->
      #|l| = ind_realargs i ->
      positive_cstr_arg mdecl ctx (mkApps (tRel k) l)

    | positive_cstr_arg_let na b ty t :
      positive_cstr_arg mdecl ctx (subst [b] 0 t) ->
      positive_cstr_arg mdecl ctx (tLetIn na b ty t)

    | positive_cstr_arg_ass na ty t :
      closedn #|ctx| ty ->
      positive_cstr_arg mdecl (vass na ty :: ctx) t ->
      positive_cstr_arg mdecl ctx (tProd na ty t).

    (** A constructor type [t] is positive w.r.t. an inductive block [mdecl]
      and inductive [i] when it's zeta normal-form is of the shape Π Δ. concl and:
        - All of the arguments in Δ are positive.
        - The conclusion is of the shape [mkApps (tRel k) indices]
          where [k] refers to the current inductive [i] and [indices] does not mention
          any of the inductive types in the block. I.e. [indices] are closed terms
          in [params ,,, args]. *)

    Inductive positive_cstr mdecl i (ctx : context) : term -> Type :=
    | positive_cstr_concl indices :
      let headrel : nat :=
        (#|mdecl.(ind_bodies)| - S i + #|ctx|)%nat in
      All (closedn #|ctx|) indices ->
      positive_cstr mdecl i ctx (mkApps (tRel headrel) indices)

    | positive_cstr_let na b ty t :
      positive_cstr mdecl i ctx (subst [b] 0 t) ->
      positive_cstr mdecl i ctx (tLetIn na b ty t)

    | positive_cstr_ass na ty t :
      positive_cstr_arg mdecl ctx ty ->
      positive_cstr mdecl i (vass na ty :: ctx) t ->
      positive_cstr mdecl i ctx (tProd na ty t).

    Definition lift_level n l :=
      match l with
      | Level.lzero | Level.Level _ => l
      | Level.Var k => Level.Var (n + k)
      end.

    Definition lift_instance n l :=
      map (lift_level n) l.

    Definition lift_constraint n (c : Level.t * ConstraintType.t * Level.t) :=
      let '((l, r), l') := c in
      ((lift_level n l, r), lift_level n l').

    Definition lift_constraints n cstrs :=
      ConstraintSet.fold (fun elt acc => ConstraintSet.add (lift_constraint n elt) acc)
        cstrs ConstraintSet.empty.

    Definition level_var_instance n (inst : list name) :=
      mapi_rec (fun i _ => Level.Var i) inst n.

    Fixpoint variance_cstrs (v : list Variance.t) (u u' : Instance.t) :=
      match v, u, u' with
      | _, [], [] => ConstraintSet.empty
      | v :: vs, u :: us, u' :: us' =>
        match v with
        | Variance.Irrelevant => variance_cstrs vs us us'
        | Variance.Covariant => ConstraintSet.add (u, ConstraintType.Le 0, u') (variance_cstrs vs us us')
        | Variance.Invariant => ConstraintSet.add (u, ConstraintType.Eq, u') (variance_cstrs vs us us')
        end
      | _, _, _ => (* Impossible due to on_variance invariant *) ConstraintSet.empty
      end.

    (** This constructs a duplication of the polymorphic universe context of the inductive,
      where the two instances are additionally related according to the variance information.
    *)

    Definition variance_universes univs v :=
      match univs with
      | Monomorphic_ctx => None
      | Polymorphic_ctx auctx =>
        let (inst, cstrs) := auctx in
        let u' := level_var_instance 0 inst in
        let u := lift_instance #|inst| u' in
        let cstrs := ConstraintSet.union cstrs (lift_constraints #|inst| cstrs) in
        let cstrv := variance_cstrs v u u' in
        let auctx' := (inst ++ inst, ConstraintSet.union cstrs cstrv) in
        Some (Polymorphic_ctx auctx', u, u')
      end.

    (** A constructor type respects the given variance [v] if each constructor
        argument respects it and each index (in the conclusion) does as well.
        We formalize this by asking for a cumulativity relation between the contexts
        of arguments and conversion of the lists of indices instanciated with [u] and
        [u'] where [u `v` u']. *)

    Definition ind_arities mdecl := arities_context (ind_bodies mdecl).

    Definition ind_respects_variance Σ mdecl v indices :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u']
      | None => False
      end.

    Definition cstr_respects_variance Σ mdecl v cs :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u'] *
        All2
          (Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cstr_args cs))@[u] Conv)
          (map (subst_instance u ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
          (map (subst_instance u' ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
      | None => False (* Monomorphic inductives have no variance attached *)
      end.

    (* Conclusion head: reference to the current inductive in the block *)
    Definition cstr_concl_head mdecl i cdecl :=
      tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|cstr_args cdecl|).

    (* Constructor conclusion shape: the inductives type applied to variables for
       the (non-let) parameters
       followed by the indices *)
    Definition cstr_concl mdecl i cdecl :=
      (mkApps (cstr_concl_head mdecl i cdecl)
        (to_extended_list_k mdecl.(ind_params) #|cstr_args cdecl|
          ++ cstr_indices cdecl)).

    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
      (* cdecl.1 fresh ?? *)
      cstr_args_length : context_assumptions (cstr_args cdecl) = cstr_arity cdecl;

      cstr_eq : cstr_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
        (it_mkProd_or_LetIn (cstr_args cdecl)
          (cstr_concl mdecl i cdecl));
      (* The type of the constructor canonically has this shape: parameters, real
        arguments ending with a reference to the inductive applied to the
        (non-lets) parameters and arguments *)

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cdecl.(cstr_args) cunivs;
      on_cindices :
        ctx_inst (fun Σ Γ t T => P Σ Γ t (Typ T)) Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
                      cdecl.(cstr_indices)
                      (List.rev (lift_context #|cdecl.(cstr_args)| 0 ind_indices));

      on_ctype_positive : (* The constructor type is positive *)
        positive_cstr mdecl i [] (cstr_type cdecl);

      on_ctype_variance : (* The constructor type respect the variance annotation
        on polymorphic universes, if any. *)
        forall v, ind_variance mdecl = Some v ->
        cstr_respects_variance Σ mdecl v cdecl;

      on_lets_in_type : if lets_in_constructor_types
                        then True else is_true (is_assumption_context (cstr_args cdecl))
    }.

    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_args_length {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_eq {Σ mdecl i idecl ind_indices cdecl cunivs}.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

    (** Each projection type corresponds to a non-let argument of the
        corresponding constructor. It is parameterized over the
        parameters of the inductive type and all the preceding arguments
        of the constructor. When computing the type of a projection for argument
        [n] at a given instance of the parameters and a given term [t] in the inductive
        type, we instantiate the argument context by corresponsping projections
        [t.π1 ... t.πn-1]. This is essential for subject reduction to hold: each
        projections type can only refer to the record object through projections.

      Projection types have their parameter and argument contexts smashed to avoid
      costly computations during type-checking and reduction: we can just substitute
      the instances of parameters and the inductive value without considering the
      presence of let bindings. *)

    Record on_proj mdecl mind i k (p : projection_body) decl :=
      { on_proj_name : (* All projections are be named after a constructor argument. *)
          binder_name (decl_name decl) = nNamed p.(proj_name);
        on_proj_type :
          (** The stored projection type already has the references to the inductive
              type substituted along with the previous arguments replaced by projections. *)
          let u := abstract_instance mdecl.(ind_universes) in
          let ind := {| inductive_mind := mind; inductive_ind := i |} in
          p.(proj_type) = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
            (subst (projs ind mdecl.(ind_npars) k) 0
              (lift 1 k (decl_type decl)));
        on_proj_relevance : p.(proj_relevance) = decl.(decl_name).(binder_relevance) }.

    Definition on_projection mdecl mind i cdecl (k : nat) (p : projection_body) :=
      let Γ := smash_context [] (cdecl.(cstr_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cdecl.(cstr_args) - S k) with
      | None => False
      | Some decl => on_proj mdecl mind i k p decl
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cdecl :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|ind_indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : idecl.(ind_kelim) = IntoAny;
        (** This ensures that all projections are definable *)

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cstr_args cdecl);
        (** There are as many projections as (non-let) constructor arguments *)

        on_projs : Alli (on_projection mdecl mind i cdecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cunivss ind_sort :=
      Forall (fun cunivs =>
        Forall (fun argsort => leq_universe φ argsort ind_sort) cunivs) cunivss.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Definition constructor_univs := list Universe.t.
    (* The sorts of the arguments context (without lets) *)

    Definition elim_sort_prop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) IntoAny
      | [ s ] =>
        if forallb Universes.is_propositional s then
          IntoAny (* Singleton elimination *)
        else
          IntoPropSProp (* Squashed: some arguments are higher than Prop, restrict to Prop *)
      | _ => (* Squashed: at least 2 constructors *) IntoPropSProp
      end.

    Definition elim_sort_sprop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive strict proposition: *) IntoAny
      | _ => (* All other inductives in SProp are squashed *) IntoSProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cdecls ind_sort : Type :=
      if Universe.is_prop ind_sort then
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_prop_ind cdecls) : Type)
      else if Universe.is_sprop ind_sort then
        (** The inductive is declared in the impredicative sort SProp *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_sprop_ind cdecls) : Type)
      else
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ cdecls ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort)));

        (** It must be well-typed in the empty context. *)
        onArity : on_type Σ [] idecl.(ind_type);

        (** The sorts of the arguments contexts of each constructor *)
        ind_cunivs : list constructor_univs;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl idecl.(ind_indices) idecl.(ind_ctors) ind_cunivs;

        (** Projections, if any, are well-typed *)
        onProjections :
          match idecl.(ind_projs), idecl.(ind_ctors) return Type with
          | [], _ => True
          | _, [ o ] =>
              on_projections mdecl mind i idecl idecl.(ind_indices) o
          | _, _ => False
          end;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          idecl.(ind_indices) ind_cunivs idecl.(ind_sort);

        onIndices :
          (* The inductive type respect the variance annotation on polymorphic universes, if any. *)
          match ind_variance mdecl with
          | Some v => ind_respects_variance Σ mdecl v idecl.(ind_indices)
          | None => True
          end
      }.

    Definition on_variance Σ univs (variances : option (list Variance.t)) :=
      match univs return Type with
      | Monomorphic_ctx => variances = None
      | Polymorphic_ctx auctx =>
        match variances with
        | None => unit
        | Some v =>
          ∑ univs' i i',
            [× (variance_universes univs v = Some (univs', i, i')),
              consistent_instance_ext (Σ, univs') univs i,
              consistent_instance_ext (Σ, univs') univs i' &
              List.length v = #|UContext.instance (AUContext.repr auctx)|]
        end
      end.

    (** We allow empty blocks for simplicity
        (no well-typed reference to them can be made). *)

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
        (** We check that the context of parameters is well-formed and that
            the size annotation counts assumptions only (no let-ins). *)
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        (** We check that the variance annotations are well-formed: i.e. they
          form a valid universe context. *)
        onVariance : on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance);
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Typ d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.

    (** *** Typing of global environment

        All declarations should be typeable and the global
        set of universe constraints should be consistent. *)

    (** Well-formed global environments have no name clash. *)

    Definition fresh_global (s : kername) (g : global_declarations) : Prop :=
      Forall (fun g => g.1 <> s) g.

    Record on_global_decls_data (univs : ContextSet.t) retro (Σ : global_declarations) (kn : kername) (d : global_decl) :=
        {
          kn_fresh :  fresh_global kn Σ ;
          udecl := universes_decl_of_decl d ;
          on_udecl_udecl : on_udecl univs udecl ;
          on_global_decl_d : on_global_decl (mk_global_env univs Σ retro, udecl) kn d
        }.

    Inductive on_global_decls (univs : ContextSet.t) (retro : Retroknowledge.t): global_declarations -> Type :=
    | globenv_nil : on_global_decls univs retro []
    | globenv_decl Σ kn d :
        on_global_decls univs retro Σ ->
        on_global_decls_data univs retro Σ kn d ->
        on_global_decls univs retro (Σ ,, (kn, d)).

    Derive Signature for on_global_decls.

    Lemma fresh_global_iff_not_In kn Σ
      : fresh_global kn Σ <-> ~ In kn (map fst Σ).
    Proof using Type.
      rewrite /fresh_global; split; [ induction 1 | induction Σ; constructor ]; cbn in *.
      all: tauto.
    Qed.

    Lemma fresh_global_iff_lookup_global_None kn Σ
      : fresh_global kn Σ <-> lookup_global Σ kn = None.
    Proof using Type. rewrite fresh_global_iff_not_In lookup_global_None //. Qed.

    Lemma NoDup_on_global_decls univs retro decls
      : on_global_decls univs retro decls -> NoDup (List.map fst decls).
    Proof using Type.
      induction 1; cbn in *; constructor => //.
      let H := match goal with H : on_global_decls_data _ _ _ _ _ |- _ => H end in
      move: H.
      case.
      rewrite fresh_global_iff_not_In; auto.
    Qed.

    Definition on_global_univs (c : ContextSet.t) :=
      let levels := global_levels c in
      let cstrs := ContextSet.constraints c in
      ConstraintSet.For_all (declared_cstr_levels levels) cstrs /\
      LS.For_all (negb ∘ Level.is_var) levels /\
      consistent cstrs.

    Definition on_global_env (g : global_env) : Type :=
      on_global_univs g.(universes) × on_global_decls g.(universes) g.(retroknowledge) g.(declarations).

    Definition on_global_env_ext (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.(universes) Σ.2.

  End GlobalMaps.

  Arguments cstr_args_length {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments cstr_eq {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cargs {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cindices {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_positive {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_variance {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.

  Arguments ind_arity_eq {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_cunivs {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onArity {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onConstructors {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onProjections {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_sorts {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onIndices {_ Pcmp P Σ mind mdecl i idecl}.

  Arguments onInductives {_ Pcmp P Σ mind mdecl}.
  Arguments onParams {_ Pcmp P Σ mind mdecl}.
  Arguments onNpars {_ Pcmp P Σ mind mdecl}.
  Arguments onVariance {_ Pcmp P Σ mind mdecl}.


  Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> term -> typ_or_sort -> Type) Σ Γ Δ u :
    type_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    type_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto. intuition auto.
  Qed.

  Lemma sorts_local_ctx_impl (P Q : global_env_ext -> context -> term -> typ_or_sort -> Type) Σ Γ Δ u :
    sorts_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    sorts_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ, u |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto. intuition auto.
    destruct u; auto. intuition eauto.
  Qed.

  Lemma on_global_env_impl {cf : checker_flags} Pcmp P Q :
    (forall Σ Γ t T,
        on_global_env Pcmp P Σ.1 ->
        on_global_env Pcmp Q Σ.1 ->
        P Σ Γ t T -> Q Σ Γ t T) ->
    forall Σ, on_global_env Pcmp P Σ -> on_global_env Pcmp Q Σ.
  Proof.
    intros X Σ [cu IH]. split; auto.
    revert cu IH; generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear Σ.
    induction g; intros; auto. constructor; auto.
    depelim IH. specialize (IHg cu IH). constructor; auto.
    pose proof (globenv_decl _ _ _ _ _ _ _ IH o).
    destruct o. constructor; auto.
    assert (X' := fun Γ t T => X ({| universes := univs; declarations := _ |}, udecl0) Γ t T
      (cu, IH) (cu, IHg)); clear X.
    rename X' into X.
    clear IH IHg. destruct d; simpl.
    - destruct c; simpl. destruct cst_body0; cbn in *; now eapply X.
    - destruct on_global_decl_d0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_impl; tea. intros.
        refine {| ind_arity_eq := X1.(ind_arity_eq);
                  ind_cunivs := X1.(ind_cunivs) |}.
        --- apply onArity in X1. unfold on_type in *; simpl in *.
            now eapply X.
        --- pose proof X1.(onConstructors) as X11. red in X11.
            eapply All2_impl; eauto.
            simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
            * apply X; eauto.
            * clear -X0 X on_cargs0. revert on_cargs0.
              generalize (cstr_args x0).
              induction c in y |- *; destruct y; simpl; auto;
                destruct a as [na [b|] ty]; simpl in *; auto;
            split; intuition eauto.
            * clear -X0 X on_cindices0.
              revert on_cindices0.
              generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
              generalize (cstr_indices x0).
              induction 1; simpl; constructor; auto.
        --- simpl; intros. pose (onProjections X1) as X2. simpl in *; auto.
        --- destruct X1. simpl. unfold check_ind_sorts in *.
            destruct Universe.is_prop; auto.
            destruct Universe.is_sprop; auto.
            split.
            * apply ind_sorts0.
            * destruct indices_matter; auto.
              eapply type_local_ctx_impl; eauto.
              eapply ind_sorts0.
        --- eapply X1.(onIndices).
      -- red in onP. red.
        eapply All_local_env_impl; tea.
  Qed.

End GlobalMaps.

Module Type GlobalMapsSig (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  Include GlobalMaps T E TU ET C L.
End GlobalMapsSig.

Module Type ConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

  Import T E TU ET.

  Parameter Inline cumul_gen : forall {cf : checker_flags}, global_env_ext -> context -> conv_pb -> term -> term -> Type.

End ConversionParSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET).

  Import T E TU ET CT CS.

  Parameter Inline typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type.

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Notation wf_local Σ Γ := (All_local_env (lift_typing Σ) Γ).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).

  Import T E L TU ET CT GM CS Ty.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    infer_sort (typing_sort typing) Σ Γ t.

  (** This predicate enforces that there exists typing derivations for every typable term in env. *)

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env cumul_gen (lift_typing P).

  (** *** Typing of local environments *)

  Definition type_local_decl `{checker_flags} Σ Γ d :=
    match d.(decl_body) with
    | None => isType Σ Γ d.(decl_type)
    | Some body => Σ ;;; Γ |- body : d.(decl_type)
    end.

  (** ** Induction principle for typing up-to a global environment *)

  Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
  Proof. now intros Ht ->. Qed.

  Definition wf_local_rel `{checker_flags} Σ := All_local_rel (lift_typing typing Σ).

  (** Functoriality of global environment typing derivations + folding of the well-formed
    environment assumption. *)
  Lemma on_wf_global_env_impl `{checker_flags} {Σ : global_env} {wfΣ : on_global_env cumul_gen (lift_typing typing) Σ} P Q :
    (forall Σ Γ t T, on_global_env cumul_gen (lift_typing typing) Σ.1 ->
        on_global_env cumul_gen P Σ.1 ->
        on_global_env cumul_gen Q Σ.1 ->
        P Σ Γ t T -> Q Σ Γ t T) ->
    on_global_env cumul_gen P Σ -> on_global_env cumul_gen Q Σ.
  Proof.
    unfold on_global_env in *.
    intros X [hu X0]. split; auto.
    simpl in *. destruct wfΣ as [cu wfΣ]. revert cu wfΣ.
    revert X0. generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear hu Σ.
    induction 1; constructor; try destruct o; try constructor; auto.
    { depelim wfΣ. eauto. }
    depelim wfΣ. specialize (IHX0 cu wfΣ). destruct o.
    assert (X' := fun Γ t T => X ({| universes := univs; declarations := Σ |}, udecl0) Γ t T
      (cu, wfΣ) (cu, X0) (cu, IHX0)); clear X.
    rename X' into X.
    clear IHX0. destruct d; simpl.
    - destruct c; simpl. destruct cst_body0; simpl in *; now eapply X.
    - simpl in *. destruct on_global_decl_d0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_impl; tea. intros.
        refine {| ind_arity_eq := X1.(ind_arity_eq);
                  ind_cunivs := X1.(ind_cunivs) |}.
        --- apply onArity in X1. unfold on_type in *; simpl in *.
            now eapply X.
        --- pose proof X1.(onConstructors) as X11. red in X11.
            eapply All2_impl; eauto.
            simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
            * apply X; eauto.
            * clear -X0 X on_cargs0. revert on_cargs0.
              generalize (cstr_args x0).
              induction c in y |- *; destruct y; simpl; auto;
                destruct a as [na [b|] ty]; simpl in *; auto;
            split; intuition eauto.
            * clear -X0 X on_cindices0.
              revert on_cindices0.
              generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
              generalize (cstr_indices x0).
              induction 1; simpl; constructor; auto.
        --- simpl; intros. pose (onProjections X1). simpl in *; auto.
        --- destruct X1. simpl. unfold check_ind_sorts in *.
            destruct Universe.is_prop; auto.
            destruct Universe.is_sprop; auto.
            split.
            * apply ind_sorts0.
            * destruct indices_matter; auto.
              eapply type_local_ctx_impl; eauto.
              eapply ind_sorts0.
        --- eapply X1.(onIndices).
      -- red in onP. red.
        eapply All_local_env_impl; tea.
  Qed.

End DeclarationTyping.

Module Type DeclarationTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
       (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
       (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
       (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).
  Include DeclarationTyping T E TU ET CT CS Ty L GM.
End DeclarationTypingSig.
