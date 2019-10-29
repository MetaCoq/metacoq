From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import config utils BasicAst AstUtils.
From MetaCoq.Template Require Import Universes Environment UnivSubst.
Import List.ListNotations.
Require Import ssreflect.

Set Asymmetric Patterns.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition global_decl_ident d :=
    match d with
    | ConstantDecl id _ => id
    | InductiveDecl id _ => id
    end.

  Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
    match Σ with
    | nil => None
    | hd :: tl =>
      if ident_eq id (global_decl_ident hd) then Some hd
      else lookup_env tl id
    end.

  Definition declared_constant (Σ : global_env) (id : ident) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl id decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl mind decl).

  Definition declared_inductive Σ mdecl ind decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
    declared_inductive Σ mdecl (fst cstr) idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ mdecl idecl (proj : projection) pdecl
  : Prop :=
    declared_inductive Σ mdecl (fst (fst proj)) idecl /\
    List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl /\
    mdecl.(ind_npars) = snd (fst proj).

  (* TODO fix lookup env *)
  Lemma lookup_env_cst_inv {Σ c k cst} :
    lookup_env Σ c = Some (ConstantDecl k cst) -> c = k.
  Proof.
    induction Σ. simpl. discriminate.
    simpl. destruct AstUtils.ident_eq eqn:Heq. intros [= ->]. simpl in Heq.
    now destruct (AstUtils.ident_eq_spec c k). auto.
  Qed.

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl  _ cb => F cb.(cst_universes)
  | InductiveDecl _ mb => F mb.(ind_universes)
  end.

  Definition monomorphic_udecl_decl := on_udecl_decl monomorphic_udecl.

  Definition monomorphic_levels_decl := fst ∘ monomorphic_udecl_decl.

  Definition monomorphic_constraints_decl := snd ∘ monomorphic_udecl_decl.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  (* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

  Definition global_levels (Σ : global_env) : LevelSet.t :=
    fold_right
      (fun decl lvls => LevelSet.union (monomorphic_levels_decl decl) lvls)
      (LevelSet_pair Level.lSet Level.lProp) Σ.

  Lemma global_levels_Set Σ :
    LevelSet.mem Level.lSet (global_levels Σ) = true.
  Proof.
    induction Σ; simpl. reflexivity.
    apply LevelSet.mem_spec, LevelSet.union_spec; right.
    now apply LevelSet.mem_spec in IHΣ.
  Qed.

  Lemma global_levels_Prop Σ :
    LevelSet.mem Level.lProp (global_levels Σ) = true.
  Proof.
    induction Σ; simpl. reflexivity.
    apply LevelSet.mem_spec, LevelSet.union_spec; right.
    now apply LevelSet.mem_spec in IHΣ.
  Qed.

  (** One can compute the constraints associated to a global environment or its
      extension by folding over its constituent definitions.

      We make *only* the second of these computations an implicit coercion
      for more readability. Note that [fst_ctx] is also a coercion which goes
      from a [global_env_ext] to a [global_env]: coercion coherence would *not*
      be ensured if we added [global_constraints] as well as a coercion, as it
      would forget the extension's constraints. *)

  Definition global_constraints (Σ : global_env) : constraints :=
    fold_right (fun decl ctrs =>
        ConstraintSet.union (monomorphic_constraints_decl decl) ctrs
      ) ConstraintSet.empty Σ.

  Definition global_uctx (Σ : global_env) : ContextSet.t :=
    (global_levels Σ, global_constraints Σ).

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1).

  Definition global_ext_constraints (Σ : global_env_ext) : constraints :=
    ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> constraints.

  Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t :=
    (global_ext_levels Σ, global_ext_constraints Σ).


  Lemma prop_global_ext_levels Σ : LevelSet.In Level.prop (global_ext_levels Σ).
  Proof.
    destruct Σ as [Σ φ]; cbn.
    apply LevelSetFact.union_3. cbn -[global_levels]; clear φ.
    induction Σ.
    - cbn. now apply LevelSetFact.add_1.
    - simpl. now apply LevelSetFact.union_3.
  Qed.

  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : constraints) uctx (u : universe_instance) :=
    match uctx with
    | Monomorphic_ctx c => List.length u = 0
    | Polymorphic_ctx c
    | Cumulative_ctx (c, _) => (* FIXME Cumulative *)
      (* no prop levels in instances *)
      forallb (negb ∘ Level.is_prop) u /\
      (* levels of the instance already declared *)
      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T).

  Import T E.

  Section TypeLocal.

    Context (typing : forall (Γ : context), term -> option term -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ t None ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ t None ->
        typing Γ b (Some t) ->
        All_local_env (Γ ,, vdef na b t).

  End TypeLocal.

  Arguments localenv_nil {_}.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.
  Arguments localenv_cons_abs {_ _ _ _} _ _.

  (** Well-formedness of local environments embeds a sorting for each variable *)

  Definition lift_typing (P : global_env_ext -> context -> term -> term -> Type) :
  (global_env_ext -> context -> term -> option term -> Type) :=
    fun Σ Γ t T =>
      match T with
      | Some T => P Σ Γ t T
      | None => { s : universe & P Σ Γ t (tSort s) }
      end.

  Definition on_local_decl (P : context -> term -> option term -> Type) Γ d :=
    match d.(decl_body) with
    | Some b => P Γ b (Some d.(decl_type))
    | None => P Γ d.(decl_type) None
    end.

  Section TypeLocalOver.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
    Context (property : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_typing typing Σ) Γ ->
                forall (t T : term), typing Σ Γ t T -> Type).

    Inductive All_local_env_over (Σ : global_env_ext) :
      forall (Γ : context), All_local_env (lift_typing typing Σ) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over Σ [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_typing typing Σ) Γ) :
        All_local_env_over Σ Γ all ->
        forall (tu : lift_typing typing Σ Γ t None),
          property Σ Γ all _ _ (projT2 tu) ->
          All_local_env_over Σ (Γ ,, vass na t)
                             (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_typing typing Σ) Γ) (tb : typing Σ Γ b t) :
        All_local_env_over Σ Γ all ->
        property Σ Γ all _ _ tb ->
        forall (tu : lift_typing typing Σ Γ t None),
          property Σ Γ all _ _ (projT2 tu) ->
          All_local_env_over Σ (Γ ,, vdef na b t)
                             (localenv_cons_def all tu tb).
  End TypeLocalOver.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T).
  Include EnvTyping T E.
End EnvTypingSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (ET : EnvTypingSig T E).

  Import T E ET.

  Parameter (ind_guard : mutual_inductive_body -> bool).

  Parameter (typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Parameter (smash_context : context -> context -> context).

  Notation wf_local Σ Γ := (All_local_env (lift_typing typing Σ) Γ).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T)
  (ET : EnvTypingSig T E) (Ty : Typing T E ET) (L : LookupSig T E).

  Import T E Ty L ET.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    { s : _ & Σ ;;; Γ |- t : tSort s }.

  (** *** Typing of inductive declarations *)

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (P : global_env_ext -> context -> term -> option term -> Type).

    (** For well-formedness of inductive declarations we need a way to check that a assumptions
        of a given context is typable in a sort [u]. *)
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : universe) : Type :=
      match Δ with
      | [] => True
      | {| decl_body := None ; decl_type := t |} :: Δ =>
        (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some _ |} :: Δ =>
        type_local_ctx Σ Γ Δ u
      end.

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

    Definition on_type Σ Γ T := P Σ Γ T None.

    Record constructor_shape mdecl i idecl ctype :=
      { cshape_args : context;
        (* Arguments (with lets) *)

        cshape_concl_head := tRel (#|mdecl.(ind_bodies)|
                                  - S i
                                  + #|mdecl.(ind_params)|
                                  + #|cshape_args|);
        (* Conclusion head: reference to the current inductive in the block *)

        cshape_indices : list term;
        (* Indices of the constructor, whose length should be the real arguments
        length of the inductive *)

        cshape_eq : ctype = it_mkProd_or_LetIn mdecl.(ind_params)
                              (it_mkProd_or_LetIn cshape_args
                                (mkApps cshape_concl_head
                                (to_extended_list_k mdecl.(ind_params) #|cshape_args|
                                  ++ cshape_indices)))
        (* The type of the constructor canonically has this shape: parameters, real
          arguments ending with a reference to the inductive applied to the
          (non-lets) parameters and arguments *)
      }.
    Arguments cshape_args {mdecl i idecl ctype}.

    Open Scope type_scope.

    Definition on_constructor Σ mdecl i idecl cdecl ind_ctor_sort :=
      (* cdecl.1 fresh ?? *)
      (* cdecl.2.2 ?? *)
      let ctype := cdecl.1.2 in
      (* FIXME: there is some redundancy with the type_local_ctx *)
      on_type Σ (arities_context mdecl.(ind_bodies)) ctype *
      { cs : constructor_shape mdecl i idecl ctype &
            type_local_ctx Σ
                      (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cs.(cshape_args) ind_ctor_sort }.

    Definition on_constructors Σ mdecl i idecl :=
      All2 (on_constructor Σ mdecl i idecl).

    (** Projections have their parameter context smashed to avoid costly computations
        during type-checking. *)

    Definition on_projection Σ mind mdecl i idecl
              (k : nat) (p : ident * term) :=
      let ctx := smash_context [] mdecl.(ind_params) in
      let Γ := ctx,, vass (nNamed idecl.(ind_name))
                  (mkApps (tInd (mkInd mind i) (polymorphic_instance mdecl.(ind_universes)))
                          (to_extended_list ctx))
      (* FIXME: more on p? *)
      in on_type Σ Γ (snd p).

    Record on_projections Σ mind mdecl i idecl (indices : context) :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : List.Exists (fun sf => sf = InType) idecl.(ind_kelim);
        (** This ensures that all projections are definable *)

        on_projs : Alli (on_projection Σ mind mdecl i idecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ ind_ctors_sort ind_sort :=
      Forall (fun s => leq_universe φ s ind_sort) ind_ctors_sort.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Fixpoint elim_sort_prop_ind ind_ctors_sort :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) InType
      | [ s ] => match universe_family s with
                | InProp => (* Not squashed: all arguments are in Prop  *)
                  (* This is singleton elimination *) InType
                | _ => (* Squashed: some arguments are higher than Prop,
                        restrict to Prop *) InProp
                end
      | _ => (* Squashed: at least 2 constructors *) InProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices ind_ctors_sort ind_sort : Type :=
      match universe_family ind_sort with
      | InProp =>
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        forall x, In x kelim -> leb_sort_family x (elim_sort_prop_ind ind_ctors_sort)
      | _ =>
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ ind_ctors_sort ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True
      end.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_indices : context;
        ind_sort : universe;
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn ind_indices (tSort ind_sort));

        (** It must be well-typed in the empty context. *)
        onArity : on_type Σ [] idecl.(ind_type);

        (** There is a sort bounding the indices and arguments for each constructor *)
        ind_ctors_sort : list universe;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl idecl.(ind_ctors) ind_ctors_sort;

        (** Projections, if any, are well-typed *)
        onProjections :
          idecl.(ind_projs) <> [] -> on_projections Σ mind mdecl i idecl ind_indices;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          ind_indices ind_ctors_sort ind_sort;
      }.

    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

    (** We allow empty blocks for simplicity
        (no well-typed reference to them can be made). *)

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
        (** We check that the context of parameters is well-formed and that
            the size annotation counts assumptions only (no let-ins). *)
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        onGuard : ind_guard mdecl
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Some d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ decl :=
      match decl with
      | ConstantDecl id d => on_constant_decl Σ d
      | InductiveDecl ind inds => on_inductive Σ ind inds
      end.

    (** *** Typing of global environment

        All declarations should be typeable and the global
        set of universe constraints should be consistent. *)

    (** Well-formed global environments have no name clash. *)

    Definition fresh_global (s : string) : global_env -> Prop :=
      Forall (fun g => global_decl_ident g <> s).

    Definition satisfiable_udecl `{checker_flags} Σ φ
      := consistent (global_ext_constraints (Σ, φ)).

    (* Check that: *)
    (*   - declared levels are fresh *)
    (*   - all levels used in constraints are declared *)
    (*   - level used in monomorphic contexts are only monomorphic *)
    Definition on_udecl `{checker_flags} Σ (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels Σ in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ ConstraintSet.For_all (fun '(l1,_,l2) => LevelSet.In l1 all_levels
                                                /\ LevelSet.In l2 all_levels)
                                (constraints_of_udecl udecl)
        /\ match udecl with
          | Monomorphic_ctx ctx =>  LevelSet.for_all (negb ∘ Level.is_var) ctx.1
          | _ => True
          end
        /\ satisfiable_udecl Σ udecl.


    Inductive on_global_env `{checker_flags} : global_env -> Type :=
    | globenv_nil : on_global_env []
    | globenv_decl Σ d :
        on_global_env Σ ->
        fresh_global (global_decl_ident d) Σ ->
        let udecl := universes_decl_of_decl d in
        on_udecl Σ udecl ->
        on_global_decl (Σ, udecl) d ->
        on_global_env (Σ ,, d).

    Definition on_global_env_ext `{checker_flags} (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.1 Σ.2.

  End GlobalMaps.

  Arguments cshape_args {mdecl i idecl ctype}.
  Arguments ind_indices {_ P Σ mind mdecl i idecl}.
  Arguments ind_sort {_ P Σ mind mdecl i idecl}.
  Arguments ind_arity_eq {_ P Σ mind mdecl i idecl}.
  Arguments onArity {_ P Σ mind mdecl i idecl}.
  Arguments ind_ctors_sort {_ P Σ mind mdecl i idecl}.
  Arguments onConstructors {_ P Σ mind mdecl i idecl}.
  Arguments onProjections {_ P Σ mind mdecl i idecl}.
  Arguments ind_sorts {_ P Σ mind mdecl i idecl}.

  Lemma All_local_env_impl (P Q : context -> term -> option term -> Type) l :
    All_local_env P l ->
    (forall Γ t T, P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
  Proof.
    induction 1; intros; simpl; econstructor; eauto.
  Qed.

  Lemma All_local_env_skipn P Γ : All_local_env P Γ -> forall n, All_local_env P (skipn n Γ).
  Proof.
    induction 1; simpl; intros; destruct n; simpl; try econstructor; eauto.
  Qed.
  Hint Resolve All_local_env_skipn : wf.

  Lemma Alli_impl_trans : forall (A : Type) (P Q : nat -> A -> Type) (l : list A) (n : nat),
  Alli P n l -> (forall (n0 : nat) (x : A), P n0 x -> Q n0 x) -> Alli Q n l.
  Proof.
    intros. induction X; simpl; constructor; auto.
  Defined.

  Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> term -> option term -> Type) Σ Γ Δ u :
    type_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    type_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto.
  Qed.

  (** This predicate enforces that there exists typing derivations for every typable term in env. *)

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env (lift_typing P).

  (** *** Typing of local environments *)

  Definition type_local_decl `{checker_flags} Σ Γ d :=
    match d.(decl_body) with
    | None => isType Σ Γ d.(decl_type)
    | Some body => Σ ;;; Γ |- body : d.(decl_type)
    end.

  (** ** Induction principle for typing up-to a global environment *)

  Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
  Proof. now intros Ht ->. Qed.

  Section wf_local.
    Context `{checker_flags}.

    Definition wf_local_rel Σ Γ Γ'
      := (All_local_env (lift_typing (fun Σ0 Γ0 t T => Σ0 ;;; Γ ,,, Γ0 |- t : T) Σ) Γ').

    Definition wf_local_rel_nil {Σ Γ} : wf_local_rel Σ Γ []
      := localenv_nil.

    Definition wf_local_rel_abs {Σ Γ Γ' A na} :
      wf_local_rel Σ Γ Γ' -> {u & Σ ;;; Γ ,,, Γ' |- A : tSort u }
      -> wf_local_rel Σ Γ (Γ',, vass na A)
      := localenv_cons_abs.

    Definition wf_local_rel_def {Σ Γ Γ' t A na} :
      wf_local_rel Σ Γ Γ' ->
      isType Σ (Γ ,,, Γ') A ->
      Σ ;;; Γ ,,, Γ' |- t : A ->
      wf_local_rel Σ Γ (Γ',, vdef na t A)
      := localenv_cons_def.

    Lemma wf_local_rel_local :
      forall Σ Γ,
        wf_local Σ Γ ->
        wf_local_rel Σ [] Γ.
    Proof.
      intros Σ Γ h. eapply All_local_env_impl.
      - exact h.
      - intros Δ t [] h'.
        all: cbn.
        + rewrite app_context_nil_l. assumption.
        + rewrite app_context_nil_l. assumption.
    Defined.

    Lemma wf_local_local_rel Σ Γ :
      wf_local_rel Σ [] Γ -> wf_local Σ Γ.
    Proof.
      intro X. eapply All_local_env_impl. exact X.
      intros Γ0 t [] XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
    Defined.

  End wf_local.

  Section wf_local_size.
    Context `{checker_flags} (Σ : global_env_ext).
    Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), typing Σ Γ t T -> size).

    Fixpoint wf_local_size Γ (w : wf_local Σ Γ) : size :=
      match w with
      | localenv_nil => 0

      | localenv_cons_abs Γ na t wfΓ tty =>
        (fn _ _ t _ (projT2 tty) + wf_local_size _ wfΓ)%nat

      | localenv_cons_def Γ na b t wfΓ tty tty' =>
        (fn _ _ t _ (projT2 tty) + fn _ _ b t tty' + wf_local_size _ wfΓ)%nat
      end.
  End wf_local_size.

End DeclarationTyping.