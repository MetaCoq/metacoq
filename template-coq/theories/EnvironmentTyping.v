(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils BasicAst AstUtils
     Universes Environment.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition declared_constant (Σ : global_env) (id : kername) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl decl).

  Definition declared_inductive Σ ind mdecl decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
    declared_inductive Σ (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ (proj : projection) mdecl idecl pdecl
  : Prop :=
    declared_inductive Σ (fst (fst proj)) mdecl idecl /\
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
      (LevelSet.singleton (Level.lSet)) Σ.

  Lemma global_levels_Set Σ :
    LevelSet.mem Level.lSet (global_levels Σ) = true.
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


  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx c => List.length u = 0
    | Polymorphic_ctx c =>
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
  Derive Signature for All_local_env.
  End TypeLocal.

  Arguments localenv_nil {_}.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.
  Arguments localenv_cons_abs {_ _ _ _} _ _.

  Inductive context_relation (P : context -> context -> context_decl -> context_decl -> Type)
            : forall (Γ Γ' : context), Type :=
  | ctx_rel_nil : context_relation P nil nil
  | ctx_rel_vass na na' T U Γ Γ' :
      context_relation P Γ Γ' ->
      P Γ Γ' (vass na T) (vass na' U) ->
      context_relation P (vass na T :: Γ) (vass na' U :: Γ')
  | ctx_rel_def na na' t T u U Γ Γ' :
      context_relation P Γ Γ' ->
      P Γ Γ' (vdef na t T) (vdef na' u U) ->
      context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').

  Derive Signature for context_relation.
  Arguments context_relation P Γ Γ' : clear implicits.

  Lemma context_relation_length {P Γ Γ'} :
    context_relation P Γ Γ' -> #|Γ| = #|Γ'|.
  Proof.
    induction 1; cbn; congruence.
  Qed.

  Lemma context_relation_impl {P Q Γ Γ'} :
    context_relation P Γ Γ' -> (forall Γ Γ' d d', P Γ Γ' d d' -> Q Γ Γ' d d') ->
    context_relation Q Γ Γ'.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Section All2_local_env.

  Definition on_decl (P : context -> context -> term -> term -> Type)
             (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => (P Γ Γ' b b' * P Γ Γ' t t')%type
    | None => P Γ Γ' t t'
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na na' t t' :
        All2_local_env Γ Γ' ->
        eq_binder_annot na na' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na' t')
    | localenv2_cons_def Γ Γ' na na' b b' t t' :
        All2_local_env Γ Γ' ->
        eq_binder_annot na na' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na' b' t').
  End All_local_2.

  Definition on_decl_over (P : context -> context -> term -> term -> Type) Γ Γ' :=
    fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ').

  Definition All2_local_env_over P Γ Γ' := All2_local_env (on_decl (on_decl_over P Γ Γ')).

  Lemma All2_local_env_length {P l l'} : @All2_local_env P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto. Qed.


  Lemma All2_local_env_impl {P Q : context -> context -> term -> term -> Type} {par par'} :
    All2_local_env (on_decl P) par par' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    All2_local_env (on_decl Q) par par'.
  Proof.
    intros H aux.
    induction H; constructor. auto. red in p. assumption. apply aux, p.
    apply IHAll2_local_env. assumption. red. split.
    apply aux. apply p. apply aux. apply p.
  Defined.

  Lemma All2_local_env_app_inv :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) Γ Γl ->
      All2_local_env (on_decl (on_decl_over P Γ Γl)) Γ' Γr ->
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto.
    - simpl. constructor; auto.
    - simpl. constructor; auto.
  Qed.

  End All2_local_env.

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
  End TypeCtxInst.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T).
  Include EnvTyping T E.
End EnvTypingSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (ET : EnvTypingSig T E).

  Import T E ET.

  Parameter (conv : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).
  Parameter (cumul : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).

  Parameter (typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).

  Parameter (wf_universe : global_env_ext -> Universe.t -> Prop).

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Parameter Inline inds : kername -> Instance.t -> list one_inductive_body -> list term.
  Parameter destArity : term -> option (context * Universe.t).

  Notation wf_local Σ Γ := (All_local_env (lift_typing typing Σ) Γ).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T)
  (ET : EnvTypingSig T E) (Ty : Typing T E ET) (L : LookupSig T E).

  Import T E Ty L ET.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    { s : _ & Σ ;;; Γ |- t : tSort s }.

  Derive Signature NoConfusion for ctx_inst.
  
  Section ContextConversion.
    Context {cf : checker_flags}.
    Context (Σ : global_env_ext).
  
    Inductive conv_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
    | conv_vass na na' T T' :
        eq_binder_annot na na' ->
        conv Σ Γ T T' ->
        conv_decls Γ Γ' (vass na T) (vass na' T')
  
    | conv_vdef_body na na' b b' T T' :
        eq_binder_annot na na' ->
        conv Σ Γ b b' ->
        conv Σ Γ T T' ->
        conv_decls Γ Γ' (vdef na b T) (vdef na' b' T').
    Derive Signature NoConfusion for conv_decls.
  
    Inductive cumul_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
    | cumul_vass na na' T T' :
        eq_binder_annot na na' ->
        cumul Σ Γ T T' ->
        cumul_decls Γ Γ' (vass na T) (vass na' T')
  
    | cumul_vdef_body na na' b b' T T' :
        eq_binder_annot na na' ->
        conv Σ Γ b b' -> (* Not that definiens must be convertible, otherwise this notion 
                            of cumulativity is useless *)
        cumul Σ Γ T T' ->
        cumul_decls Γ Γ' (vdef na b T) (vdef na' b' T').
  
    Derive Signature NoConfusion for cumul_decls.
  End ContextConversion.

  Definition cumul_ctx_rel {cf:checker_flags} Σ Γ Δ Δ' :=
    context_relation (fun Δ Δ' => cumul_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ'.

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
      | [] => wf_universe Σ u
      | {| decl_body := None; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some b; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t None * P Σ (Γ ,,, Δ) b (Some t)))
      end.

    Fixpoint sorts_local_ctx Σ (Γ Δ : context) (us : list Universe.t) : Type :=
      match Δ, us with
      | [], [] => unit
      | {| decl_body := None; decl_type := t |} :: Δ, u :: us => 
        (sorts_local_ctx Σ Γ Δ us * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some b; decl_type := t |} :: Δ, us => 
        (sorts_local_ctx Σ Γ Δ us * (P Σ (Γ ,,, Δ) t None * P Σ (Γ ,,, Δ) b (Some t)))
      | _, _ => False
      end.

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body).

    Definition on_type Σ Γ T := P Σ Γ T None.

    Open Scope type_scope.

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
      match destArity o.(ind_type) with
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
      | Level.lSet | Level.Level _ => l
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
      | Monomorphic_ctx ctx => None
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
        cumul_ctx_rel (Σ, univs) (subst_instance_context u (smash_context [] (ind_params mdecl)))
          (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
          (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
      | None => False
      end.

    Definition cstr_respects_variance Σ mdecl v cs :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel (Σ, univs) (subst_instance_context u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl)))
          (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs))))
          (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))) *
        All2 
          (conv (Σ, univs) (subst_instance_context u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cstr_args cs))))
          (map (subst_instance_constr u ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
          (map (subst_instance_constr u' ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
      | None => False (* Monomorphic inductives have no variance attached *)
      end.

    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
      (* cdecl.1 fresh ?? *)
      cstr_args_length : context_assumptions (cstr_args cdecl) = cstr_arity cdecl;
      
      (* Real (non-let) arguments bound by the constructor *)
      cstr_concl_head := tRel (#|mdecl.(ind_bodies)|
      - S i
      + #|mdecl.(ind_params)|
      + #|cstr_args cdecl|);
      (* Conclusion head: reference to the current inductive in the block *)

      cstr_eq : cstr_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
                          (it_mkProd_or_LetIn (cstr_args cdecl)
                              (mkApps cstr_concl_head
                              (to_extended_list_k mdecl.(ind_params) #|cstr_args cdecl|
                                ++ cstr_indices cdecl)));
      (* The type of the constructor canonically has this shape: parameters, real
        arguments ending with a reference to the inductive applied to the
        (non-lets) parameters and arguments *)

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cdecl.(cstr_args) cunivs;
      on_cindices : 
        ctx_inst (fun Σ Γ t T => P Σ Γ t (Some T)) Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
                      cdecl.(cstr_indices)
                      (List.rev (lift_context #|cdecl.(cstr_args)| 0 ind_indices));

      on_ctype_positive : (* The constructor type is positive *)
        positive_cstr mdecl i [] (cstr_type cdecl);

      on_ctype_variance : (* The constructor type respect the variance annotation 
        on polymorphic universes, if any. *)
        forall v, ind_variance mdecl = Some v -> 
        cstr_respects_variance Σ mdecl v cdecl
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

    Fixpoint projs ind npars k :=
      match k with
      | 0 => []
      | S k' => (tProj ((ind, npars), k') (tRel 0)) :: projs ind npars k'
      end.

    Lemma projs_length ind npars k : #|projs ind npars k| = k.
    Proof. induction k; simpl; auto. Qed.

    Definition on_projection mdecl mind i cdecl (k : nat) (p : ident * term) :=
      let Γ := smash_context [] (cdecl.(cstr_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cdecl.(cstr_args) - S k) with
      | None => False
      | Some decl => 
        let u := abstract_instance mdecl.(ind_universes) in
        let ind := {| inductive_mind := mind; inductive_ind := i |} in
        (** The stored projection type already has the references to the inductive
          type substituted along with the previous arguments replaced by projections.
          All projections must also be named.
          *)
        (binder_name (decl_name decl) = nNamed (fst p)) /\
        (snd p = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
              (subst (projs ind mdecl.(ind_npars) k) 0 
                (lift 1 k (decl_type decl))))
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
      
    Fixpoint elim_sort_sprop_ind (ind_ctors_sort : list constructor_univs) :=
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
        allowed_eliminations_subset kelim (elim_sort_prop_ind cdecls)
      else if Universe.is_sprop ind_sort then
        (** The inductive is declared in the impredicative sort SProp *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        allowed_eliminations_subset kelim (elim_sort_sprop_ind cdecls)
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
          idecl.(ind_projs) <> [] ->
          match idecl.(ind_ctors) return Type with
          | [ o ] =>
            on_projections mdecl mind i idecl idecl.(ind_indices) o
          | _ => False
          end;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          idecl.(ind_indices) ind_cunivs idecl.(ind_sort);

        onIndices : 
          (* The inductive type respect the variance annotation  on polymorphic universes, if any. *)
          forall v, ind_variance mdecl = Some v -> 
          ind_respects_variance Σ mdecl v idecl.(ind_indices)
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

  Arguments cstr_args_length {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments cstr_eq {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cargs {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cindices {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_positive {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_variance {_ P Σ mdecl i idecl ind_indices cdecl cunivs}.

  Arguments ind_arity_eq {_ P Σ mind mdecl i idecl}.
  Arguments ind_cunivs {_ P Σ mind mdecl i idecl}.
  Arguments onArity {_ P Σ mind mdecl i idecl}.
  Arguments onConstructors {_ P Σ mind mdecl i idecl}.
  Arguments onProjections {_ P Σ mind mdecl i idecl}.
  Arguments ind_sorts {_ P Σ mind mdecl i idecl}.
  Arguments onIndices {_ P Σ mind mdecl i idecl}.

  Arguments onInductives {_ P Σ mind mdecl}.
  Arguments onParams {_ P Σ mind mdecl}.
  Arguments onNpars {_ P Σ mind mdecl}.
  Arguments onVariance {_ P Σ mind mdecl}.

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

  Lemma sorts_local_ctx_impl (P Q : global_env_ext -> context -> term -> option term -> Type) Σ Γ Δ u :
    sorts_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    sorts_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ, u |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto. intuition auto.
    destruct u; auto. intuition eauto.
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
