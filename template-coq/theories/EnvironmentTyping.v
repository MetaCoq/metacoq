From Coq Require Import Ascii String OrderedType.
From MetaCoq.Template Require Import config utils BasicAst AstUtils.
From MetaCoq.Template Require Import Universes Environment.
Import List.ListNotations.

Set Asymmetric Patterns.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition declared_constant (Σ : global_env) (id : kername) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl decl).

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

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition monomorphic_udecl_decl := on_udecl_decl monomorphic_udecl.

  Definition monomorphic_levels_decl := fst ∘ monomorphic_udecl_decl.

  Definition monomorphic_constraints_decl := snd ∘ monomorphic_udecl_decl.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  Definition abstract_instance decl :=
    match decl with
    | Monomorphic_ctx _ => Instance.empty
    | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
    end.

  (* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

  Definition global_levels (Σ : global_env) : LevelSet.t :=
    fold_right
      (fun decl lvls => LevelSet.union (monomorphic_levels_decl decl.2) lvls)
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

  Definition global_constraints (Σ : global_env) : ConstraintSet.t :=
    fold_right (fun decl ctrs =>
        ConstraintSet.union (monomorphic_constraints_decl decl.2) ctrs
      ) ConstraintSet.empty Σ.

  Definition global_uctx (Σ : global_env) : ContextSet.t :=
    (global_levels Σ, global_constraints Σ).

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1).

  Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t :=
    ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

  Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t :=
    (global_ext_levels Σ, global_ext_constraints Σ).


  Lemma prop_global_ext_levels Σ : LevelSet.In Level.lProp (global_ext_levels Σ).
  Proof.
    destruct Σ as [Σ φ]; cbn.
    apply LevelSetFact.union_3. cbn -[global_levels]; clear φ.
    induction Σ.
    - cbn. now apply LevelSetFact.add_1.
    - simpl. now apply LevelSetFact.union_3.
  Qed.

  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx c => List.length u = 0
    | Polymorphic_ctx c =>
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
      | None => { s : Universe.t & P Σ Γ t (tSort s) }
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

  Parameter Inline smash_context : context -> context -> context.
  Parameter Inline lift_context : nat -> nat -> context -> context.
  Parameter Inline subst_telescope : list term -> nat -> context -> context.
  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
  Parameter Inline inds : kername -> Instance.t -> list one_inductive_body -> list term. 
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

    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

    (** For well-formedness of inductive declarations we need a way to check that a assumptions
      of a given context is typable in a sort [u]. We also force well-typing of the let-ins
      in any universe to imply wf_local. *)
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : Universe.t) : Type :=
      match Δ with
      | [] => True
      | {| decl_body := None; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some b; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t None * P Σ (Γ ,,, Δ) b (Some t)))
      end.    

    (* Delta telescope *)
    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ : 
      P Σ Γ i (Some t) ->
      ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
      ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
      ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
      ctx_inst Σ Γ inst (vdef na b t :: Δ).

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

    Definition on_type Σ Γ T := P Σ Γ T None.

    Definition cdecl_type cdecl := cdecl.1.2.
    Definition cdecl_args cdecl := cdecl.2.

    (* A constructor shape is a decomposition of a constructor's type *)
    Record constructor_shape :=
      { cshape_args : context;
        (* Arguments (with lets) *)

        cshape_indices : list term;
        (* Indices of the constructor, whose length should be the real arguments
        length of the inductive *)

        cshape_sort : Universe.t;
        (* The sort bounding the arguments context (without lets) *)
      }.

    Open Scope type_scope.

    Record on_constructor Σ mdecl i idecl ind_indices cdecl (cshape : constructor_shape) := {
      (* cdecl.1 fresh ?? *)
      cstr_args_length : context_assumptions (cshape_args cshape) = cdecl_args cdecl;
      
      (* Real (non-let) arguments bound by the constructor *)
      cstr_concl_head := tRel (#|mdecl.(ind_bodies)|
      - S i
      + #|mdecl.(ind_params)|
      + #|cshape_args cshape|);
      (* Conclusion head: reference to the current inductive in the block *)

      cstr_eq : cdecl_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
                          (it_mkProd_or_LetIn (cshape_args cshape)
                              (mkApps cstr_concl_head
                              (to_extended_list_k mdecl.(ind_params) #|cshape_args cshape|
                                ++ cshape_indices cshape)));
      (* The type of the constructor canonically has this shape: parameters, real
        arguments ending with a reference to the inductive applied to the
        (non-lets) parameters and arguments *)

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cdecl_type cdecl);
      on_cargs : (* FIXME: there is some redundancy with the type_local_ctx *)
        type_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cshape.(cshape_args) cshape.(cshape_sort);
      on_cindices : 
        ctx_inst Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cshape.(cshape_args))
                      cshape.(cshape_indices)
                      (List.rev (lift_context #|cshape.(cshape_args)| 0 ind_indices))
        }.

    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl cshape}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl cshape}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl cshape}.
    Arguments cstr_args_length {Σ mdecl i idecl ind_indices cdecl cshape}.
    Arguments cstr_eq {Σ mdecl i idecl ind_indices cdecl cshape}.

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

    Fixpoint projs ind npars k :=
      match k with
      | 0 => []
      | S k' => (tProj ((ind, npars), k') (tRel 0)) :: projs ind npars k'
      end.

    Lemma projs_length ind npars k : #|projs ind npars k| = k.
    Proof. induction k; simpl; auto. Qed.

    Definition on_projection mdecl mind i cshape (k : nat) (p : ident * term) :=
      let Γ := smash_context [] (cshape.(cshape_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cshape.(cshape_args) - S k) with
      | None => False
      | Some decl => 
        let u := abstract_instance mdecl.(ind_universes) in
        let ind := {| inductive_mind := mind; inductive_ind := i |} in
        (** The stored projection type already has the references to the inductive
          type substituted along with the previous arguments replaced by projections.
          All projections must also be named.
          *)
        (decl_name decl = nNamed (fst p)) /\
        (snd p = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
              (subst (projs ind mdecl.(ind_npars) k) 0 
                (lift 1 k (decl_type decl))))
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cshape :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|ind_indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : idecl.(ind_kelim) = InType;
        (** This ensures that all projections are definable *)

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cshape_args cshape);
        (** There are as many projections as (non-let) constructor arguments *)

        on_projs : Alli (on_projection mdecl mind i cshape) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cshapes ind_sort :=
      Forall (fun s => leq_universe φ (cshape_sort s) ind_sort) cshapes.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Fixpoint elim_sort_prop_ind ind_ctors_sort :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) InType
      | [ s ] => match universe_family (cshape_sort s) with
                | InProp => (* Not squashed: all arguments are in Prop  *)
                  (* This is singleton elimination *) InType
                | _ => (* Squashed: some arguments are higher than Prop,
                        restrict to Prop *) InProp
                end
      | _ => (* Squashed: at least 2 constructors *) InProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cshapes ind_sort : Type :=
      match universe_family ind_sort with
      | InProp =>
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        leb_sort_family kelim (elim_sort_prop_ind cshapes)
      | _ =>
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ cshapes ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True
      end.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_indices : context;
        ind_sort : Universe.t;
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn ind_indices (tSort ind_sort));

        (** It must be well-typed in the empty context. *)
        onArity : on_type Σ [] idecl.(ind_type);

        (** The decompose shapes of each constructor *)
        ind_cshapes : list constructor_shape;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl ind_indices idecl.(ind_ctors) ind_cshapes;

        (** Projections, if any, are well-typed *)
        onProjections :
          idecl.(ind_projs) <> [] ->
          match ind_cshapes return Type with
          | [ o ] =>
            on_projections mdecl mind i idecl ind_indices o
          | _ => False
          end;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          ind_indices ind_cshapes ind_sort;
      }.

    Definition on_variance univs (variances : option (list Variance.t)) :=
      match univs with
      | Monomorphic_ctx _ => variances = None
      | Polymorphic_ctx auctx => 
        match variances with
        | None => True
        | Some v => List.length v = #|UContext.instance (AUContext.repr auctx)|
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
        onVariance : on_variance mdecl.(ind_universes) mdecl.(ind_variance);
        onGuard : ind_guard mdecl
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Some d.(cst_type))
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

    Definition fresh_global (s : kername) : global_env -> Prop :=
      Forall (fun g => g.1 <> s).

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
    | globenv_decl Σ kn d :
        on_global_env Σ ->
        fresh_global kn Σ ->
        let udecl := universes_decl_of_decl d in
        on_udecl Σ udecl ->
        on_global_decl (Σ, udecl) kn d ->
        on_global_env (Σ ,, (kn, d)).

    Definition on_global_env_ext `{checker_flags} (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.1 Σ.2.

  End GlobalMaps.

  Arguments cstr_args_length {P Σ mdecl i idecl ind_indices cdecl cshape}.
  Arguments cstr_eq {P Σ mdecl i idecl ind_indices cdecl cshape}.
  Arguments on_ctype {P Σ mdecl i idecl ind_indices cdecl cshape}.
  Arguments on_cargs {P Σ mdecl i idecl ind_indices cdecl cshape}.
  Arguments on_cindices {P Σ mdecl i idecl ind_indices cdecl cshape}.

  Arguments ind_indices {_ P Σ mind mdecl i idecl}.
  Arguments ind_sort {_ P Σ mind mdecl i idecl}.
  Arguments ind_arity_eq {_ P Σ mind mdecl i idecl}.
  Arguments ind_cshapes {_ P Σ mind mdecl i idecl}.
  Arguments onArity {_ P Σ mind mdecl i idecl}.
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
    intros. intuition auto. intuition auto.
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
