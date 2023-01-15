(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaCoq.Template Require Import utils BasicAst Primitive.
From MetaCoq.Template Require Import Universes.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.
  Parameter Inline tSort : Universe.t -> term.
  Parameter Inline tProd : aname -> term -> term -> term.
  Parameter Inline tLambda : aname -> term -> term -> term.
  Parameter Inline tLetIn : aname -> term -> term -> term -> term.
  Parameter Inline tInd : inductive -> Instance.t -> term.
  Parameter Inline tProj : projection -> term -> term.
  Parameter Inline mkApps : term -> list term -> term.

  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
  Parameter Inline closedn : nat -> term -> bool.
  Parameter Inline noccur_between : nat -> nat -> term -> bool.
  Parameter Inline subst_instance_constr : UnivSubst term.

  Notation lift0 n := (lift n 0).
End Term.

Module Retroknowledge.

  Record t := mk_retroknowledge {
    retro_int63 : option kername;
    retro_float64 : option kername;
  }.

  Definition empty := {| retro_int63 := None; retro_float64 := None |}.

  Definition extends (x y : t) :=
    option_extends x.(retro_int63) y.(retro_int63) /\
    option_extends x.(retro_float64) y.(retro_float64).
  Existing Class extends.

  #[global] Instance extends_refl x : extends x x.
  Proof.
    split; apply option_extends_refl.
  Qed.

  #[global] Instance extends_trans : RelationClasses.Transitive Retroknowledge.extends.
  Proof.
    intros x y z [] []; split; cbn; now etransitivity; tea.
  Qed.

End Retroknowledge.

Module Environment (T : Term).

  Import T.
  #[global] Existing Instance subst_instance_constr.

  Definition typ_or_sort := typ_or_sort_ term.

  (** ** Declarations *)
  Notation context_decl := (context_decl term).

  (** Local (de Bruijn) variable binding *)

  Definition vass x A : context_decl :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdef x t A : context_decl :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.

  (** Last declaration first *)

  Definition lift_decl n k d := (map_decl (lift n k) d).

  Definition lift_context n k (Γ : context) : context :=
    fold_context_k (fun k' => lift n (k' + k)) Γ.

  Lemma lift_context_alt n k Γ :
    lift_context n k Γ =
    mapi (fun k' d => lift_decl n (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold lift_context. apply: fold_context_k_alt.
  Qed.

  Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
  Proof. now rewrite /lift_context; len. Qed.
  #[global] Hint Rewrite lift_context_length : len.

  Definition subst_context s k (Γ : context) : context :=
    fold_context_k (fun k' => subst s (k' + k)) Γ.

  Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

  Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
  Proof. now rewrite /subst_context; len. Qed.
  #[global] Hint Rewrite subst_context_length : len.

  Lemma subst_context_nil s n : subst_context s n [] = [].
  Proof. reflexivity. Qed.

  Lemma subst_context_alt s k Γ :
    subst_context s k Γ =
    mapi (fun k' d => subst_decl s (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold subst_context, fold_context_k. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
  Qed.

  Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
  Proof.
    now rewrite /subst_context fold_context_k_snoc0.
  Qed.

  Definition subst_telescope s k (Γ : context) : context :=
    mapi (fun k' decl => map_decl (subst s (k' + k)) decl) Γ.

  Global Instance subst_instance_decl : UnivSubst context_decl
    := map_decl ∘ subst_instance.

  Global Instance subst_instance_context : UnivSubst context
    := map_context ∘ subst_instance.

  Lemma subst_instance_length u (ctx : context)
    : #|subst_instance u ctx| = #|ctx|.
  Proof. unfold subst_instance, subst_instance_context, map_context. now rewrite map_length. Qed.
  #[global] Hint Rewrite subst_instance_length : len.

  Definition set_binder_name (na : aname) (x : context_decl) : context_decl :=
    {| decl_name := na;
       decl_body := decl_body x;
       decl_type := decl_type x |}.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  Fixpoint is_assumption_context (Γ : context) :=
    match Γ with
    | [] => true
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => false
      | None => is_assumption_context Γ
      end
    end.

  (** Smashing a context produces an assumption context. *)

  Fixpoint smash_context (Γ Γ' : context) : context :=
    match Γ' with
    | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
    | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d]) Γ'
    | [] => Γ
    end.

  Lemma smash_context_length Γ Γ' : #|smash_context Γ Γ'| = #|Γ| + context_assumptions Γ'.
  Proof.
    induction Γ' as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
    - now rewrite IHtl subst_context_length.
    - rewrite IHtl app_length. simpl. lia.
  Qed.
  #[global] Hint Rewrite smash_context_length : len.

  (* Smashing a context Γ with Δ depending on it is the same as smashing Γ
    and substituting all references to Γ in Δ by the expansions of let bindings. *)

  Lemma smash_context_app Δ Γ Γ' :
    smash_context Δ (Γ ++ Γ') = smash_context (smash_context Δ Γ) Γ'.
  Proof.
    revert Δ; induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  Qed.

  Fixpoint extended_subst (Γ : context) (n : nat)
  (* Δ, smash_context Γ, n |- extended_subst Γ n : Γ *) :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>
      (* Δ , vs |- b *)
      let s := extended_subst vs n in
      (* Δ , smash_context vs , n |- s : vs *)
      let b' := lift (context_assumptions vs + n) #|s| b in
      (* Δ, smash_context vs, n , vs |- b' *)
      let b' := subst s 0 b' in
      (* Δ, smash_context vs , n |- b' *)
      b' :: s
    | None => tRel n :: extended_subst vs (S n)
    end
  end.

  Lemma extended_subst_length Γ n : #|extended_subst Γ n| = #|Γ|.
  Proof.
    induction Γ in n |- *; simpl; auto.
    now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ.
  Qed.
  #[global] Hint Rewrite extended_subst_length : len.

  Definition expand_lets_k Γ k t :=
    (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

  Definition expand_lets Γ t := expand_lets_k Γ 0 t.

  Definition expand_lets_k_ctx Γ k Δ :=
    (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

  Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.

  Lemma expand_lets_k_ctx_length Γ k Δ : #|expand_lets_k_ctx Γ k Δ| = #|Δ|.
  Proof. now rewrite /expand_lets_k_ctx; len. Qed.
  #[global] Hint Rewrite expand_lets_k_ctx_length : len.

  Lemma expand_lets_ctx_length Γ Δ : #|expand_lets_ctx Γ Δ| = #|Δ|.
  Proof. now rewrite /expand_lets_ctx; len. Qed.
  #[global] Hint Rewrite expand_lets_ctx_length : len.

  Definition fix_context (m : mfixpoint term) : context :=
    List.rev (mapi (fun i d => vass d.(dname) (lift i 0 d.(dtype))) m).

  (** *** Environments *)

  Record constructor_body := {
    cstr_name : ident;
    (* The arguments and indices are typeable under the context of
      arities of the mutual inductive + parameters *)
    cstr_args : context;
    cstr_indices : list term;
    cstr_type : term;
    (* Closed type: on well-formed constructors: forall params, cstr_args, I params cstr_indices *)
    cstr_arity : nat; (* arity, w/o lets, w/o parameters *)
  }.

  Record projection_body := {
    proj_name : ident;
    (* The arguments and indices are typeable under the context of
      arities of the mutual inductive + parameters *)
    proj_relevance : relevance;
    proj_type : term; (* Type under context of params and inductive object *)
  }.

  Definition map_constructor_body npars arities f c :=
    {| cstr_name := c.(cstr_name);
       cstr_args := fold_context_k (fun x => f (x + npars + arities)) c.(cstr_args);
       cstr_indices := map (f (npars + arities + #|c.(cstr_args)|)) c.(cstr_indices);
        (* Note only after positivity checking we can ensure that the indices do not mention the
           inductive type.. beware of lets! *)
       cstr_type := f arities c.(cstr_type);
       cstr_arity := c.(cstr_arity) |}.

  (* Here npars should be the [context_assumptions] of the parameters context. *)
  Definition map_projection_body npars f c :=
    {| proj_name := c.(proj_name);
       proj_relevance := c.(proj_relevance);
       proj_type := f (S npars) c.(proj_type)
    |}.

  (** See [one_inductive_body] from [declarations.ml]. *)
  Record one_inductive_body := {
    ind_name : ident;
    ind_indices : context; (* Indices of the inductive types, under params *)
    ind_sort : Universe.t; (* Sort of the inductive. *)
    ind_type : term; (* Closed arity = forall mind_params, ind_indices, tSort ind_sort *)
    ind_kelim : allowed_eliminations; (* Allowed eliminations *)
    ind_ctors : list constructor_body;
    ind_projs : list projection_body; (* names and types of projections, if any. *)
    ind_relevance : relevance (* relevance of the inductive definition *) }.

  Definition map_one_inductive_body npars arities f m :=
    match m with
    | Build_one_inductive_body ind_name ind_indices ind_sort
        ind_type ind_kelim ind_ctors ind_projs ind_relevance =>
      Build_one_inductive_body
         ind_name (fold_context_k (fun x => f (npars + x)) ind_indices) ind_sort
                  (f 0 ind_type) ind_kelim (map (map_constructor_body npars arities f) ind_ctors)
                  (map (map_projection_body npars f) ind_projs) ind_relevance
    end.

  (** See [mutual_inductive_body] from [declarations.ml]. *)
  Record mutual_inductive_body := {
    ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body ;
    ind_universes : universes_decl;
    ind_variance : option (list Universes.Variance.t) }.

  (** See [constant_body] from [declarations.ml] *)
  Record constant_body := {
    cst_type : term;
    cst_body : option term;
    cst_universes : universes_decl;
    cst_relevance : relevance }.

  Definition map_constant_body f decl :=
    {| cst_type := f decl.(cst_type);
       cst_body := option_map f decl.(cst_body);
       cst_universes := decl.(cst_universes);
       cst_relevance := decl.(cst_relevance) |}.

  Lemma map_cst_type f decl :
    f (cst_type decl) = cst_type (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  Lemma map_cst_body f decl :
    option_map f (cst_body decl) = cst_body (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  (** See [generic_module_body] from [declarations.ml]. We do not include the modpath
    in the body since it is already included in [global_declarations]. *)
  (** implementation -> module type -> algebraic (colon-annotated) module type (TODO) *)
  Inductive structure_field :=
  | sfconst : constant_body -> structure_field
  | sfmind : mutual_inductive_body -> structure_field
  | sfmod : module_implementation -> structure_body -> structure_field
  | sfmodtype : structure_body -> structure_field
  with module_implementation :=
  | mi_abstract : module_implementation (** Declare Module M: T. *)
  | mi_algebraic : kername -> module_implementation (** Module M [:T] := N. *)
  | mi_struct : structure_body -> module_implementation (** Module M:T. ... End M.*)
  | mi_fullstruct : module_implementation (** Module M. ... End M.*)
  with structure_body :=
  | sb_nil
  | sb_cons : ident -> structure_field -> structure_body -> structure_body.

  Scheme structureField_rect := Induction for structure_field Sort Type
  with moduleImpl_rect := Induction for module_implementation Sort Type
  with structureBody_rect := Induction for structure_body Sort Type.

  Combined Scheme sf_mi_sb_mutind from structureField_rect, moduleImpl_rect, structureBody_rect.

  Definition module_type_decl := structure_body.
  Definition module_decl := module_implementation × module_type_decl.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl
  | ModuleDecl : module_decl -> global_decl
  | ModuleTypeDecl : module_type_decl -> global_decl.
  Derive NoConfusion for global_decl.

  Definition global_declarations := list (kername * global_decl).

  Record global_env := mk_global_env
    { universes : ContextSet.t;
      declarations : global_declarations;
      retroknowledge : Retroknowledge.t }.

  Coercion universes : global_env >-> ContextSet.t.

  Definition empty_global_env :=
    {| universes := ContextSet.empty;
       declarations := [];
       retroknowledge := Retroknowledge.empty |}.

  Definition add_global_decl Σ decl :=
    {| universes := Σ.(universes);
       declarations := decl :: Σ.(declarations);
       retroknowledge := Σ.(retroknowledge) |}.

  Lemma eta_global_env Σ : Σ = {| universes := Σ.(universes); declarations := Σ.(declarations);
    retroknowledge := Σ.(retroknowledge) |}.
  Proof. now destruct Σ. Qed.

  Definition set_declarations Σ decls :=
    {| universes := Σ.(universes);
       declarations := decls;
       retroknowledge := Σ.(retroknowledge) |}.

  Fixpoint lookup_global (Σ : global_declarations) (kn : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if kn == d.1 then Some d.2
      else lookup_global tl kn
    end.

  Definition lookup_env (Σ : global_env) (kn : kername) := lookup_global Σ.(declarations) kn.

  Definition extends (Σ Σ' : global_env) :=
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      ∑ Σ'', Σ'.(declarations) = Σ'' ++ Σ.(declarations) &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
       ∑ Σ'', Σ'.(declarations) = Σ'' ++ Σ.(declarations) &
       Σ.(retroknowledge) = Σ'.(retroknowledge)].

  Existing Class extends.
  Existing Class extends_decls.

  Lemma lookup_global_None Σ kn : ~In kn (List.map fst Σ) <-> lookup_global Σ kn = None.
  Proof.
    move: Σ; elim => //=; try tauto.
    move => ??; case: eqb_spec; intuition congruence.
  Qed.

  Lemma lookup_global_Some_iff_In_NoDup Σ kn decl (H : NoDup (List.map fst Σ))
    : In (kn, decl) Σ <-> lookup_global Σ kn = Some decl.
  Proof.
    move: Σ H; elim => //=; try tauto.
    move => [??]?; case: eqb_spec => ? IH; inversion 1; subst; try rewrite <- IH by assumption.
    all: intuition try congruence; subst.
    all: cbn in *.
    all: repeat match goal with H : (_, _) = (_, _) |- _ => inversion H; clear H end.
    all: repeat match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    all: subst => //=; auto.
    all: try now epose proof (@in_map _ _ fst _ (_, _)); cbn in *; exfalso; eauto.
  Qed.

  #[global] Instance extends_decls_extends Σ Σ' : extends_decls Σ Σ' -> extends Σ Σ'.
  Proof.
    destruct Σ, Σ'; intros []. cbn in *; subst. split => //=.
    split; [lsets|csets]. apply Retroknowledge.extends_refl.
  Qed.

  #[global] Instance extends_decls_refl : CRelationClasses.Reflexive extends_decls.
  Proof. red. intros x. split => //; try exists [] => //. Qed.

  Lemma extends_refl : CRelationClasses.Reflexive extends.
  Proof. red. intros x. split; [apply incl_cs_refl | now exists [] | apply Retroknowledge.extends_refl]. Qed.

  (* easy prefers this to the local hypotheses, which is annoying
  #[global] Instance extends_refl : CRelationClasses.Reflexive extends.
  Proof. apply extends_refl. Qed.
  *)

  Local Ltac extends_trans_t :=
    intros [?] [?] [?] [?] [?]; red; cbn in *; split;
    try solve [ etransitivity; eassumption | eapply incl_cs_trans; eassumption ];
    repeat first [ progress subst
                 | match goal with
                   | [ H : ∑ x : _, _ |- _ ] => destruct H
                   | [ H : forall c : kername, _, kn : kername |- _ ] => specialize (H kn)
                   | [ H : ?x = _ |- context[?x] ] => rewrite H
                   end
                 | split
                 | intro
                 | now eexists; rewrite app_assoc ].
  #[global] Instance extends_decls_trans : CRelationClasses.Transitive extends_decls.
  Proof. extends_trans_t. Qed.
  #[global] Instance extends_trans : CRelationClasses.Transitive extends.
  Proof. extends_trans_t. Qed.

  Definition primitive_constant (Σ : global_env) (p : prim_tag) : option kername :=
    match p with
    | primInt => Σ.(retroknowledge).(Retroknowledge.retro_int63)
    | primFloat => Σ.(retroknowledge).(Retroknowledge.retro_float64)
    end.

  Definition primitive_invariants (cdecl : constant_body) :=
    ∑ s, [/\ cdecl.(cst_type) = tSort s, cdecl.(cst_body) = None &
             cdecl.(cst_universes) = Monomorphic_ctx].


  (** A context of global declarations + global universe constraints,
      i.e. a global environment *)

  Definition global_env_ext : Type := global_env * universes_decl.

  (** Use a coercion for this common projection of the global context. *)
  Definition fst_ctx : global_env_ext -> global_env := fst.
  Coercion fst_ctx : global_env_ext >-> global_env.

  Definition empty_ext (Σ : global_env) : global_env_ext
    := (Σ, Monomorphic_ctx).

  (** *** Programs

    A set of declarations and a term, as produced by [MetaCoq Quote Recursively]. *)

  Definition program : Type := global_env * term.

  (* TODO MOVE AstUtils factorisation *)

  Definition app_context (Γ Γ' : context) : context := Γ' ++ Γ.
  Notation "Γ ,,, Γ'" :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

  (** Make a lambda/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkLambda_or_LetIn d t :=
    match d.(decl_body) with
    | None => tLambda d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkLambda_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkLambda_or_LetIn d acc) l t.

  (** Make a prod/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkProd_or_LetIn d t :=
    match d.(decl_body) with
    | None => tProd d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkProd_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkProd_or_LetIn d acc) l t.

  Lemma it_mkProd_or_LetIn_app l l' t :
    it_mkProd_or_LetIn (l ++ l') t = it_mkProd_or_LetIn l' (it_mkProd_or_LetIn l t).
  Proof. induction l in l', t |- *; simpl; auto. Qed.

  Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
    match Γ0 with
    | [] => l
    | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
    | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
    end.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

  Lemma reln_fold f ctx n acc :
    reln acc n (fold_context_k f ctx) =
    reln acc n ctx.
  Proof.
    induction ctx as [|[na [b|] ty] ctx] in n, acc |- *; simpl; auto;
      rewrite fold_context_k_snoc0 /=; apply IHctx.
  Qed.

  Lemma reln_list_lift_above l p Γ :
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
  Proof.
    generalize (Nat.le_refl p).
    generalize p at 1 3 5.
    induction Γ in p, l |- *. simpl. auto.
    intros. destruct a. destruct decl_body. simpl.
    assert(p0 <= S p) by lia.
    specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
    simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
    simpl in *.
    specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)).
    rewrite <- Nat.add_succ_comm, Nat.add_1_r.
    eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
    simpl in *.
    constructor. exists p. intuition lia. auto.
  Qed.

  Lemma to_extended_list_k_spec Γ k :
    Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ)
           (to_extended_list_k Γ k).
  Proof.
    pose (reln_list_lift_above [] k Γ).
    unfold to_extended_list_k.
    forward f. constructor. apply f.
  Qed.

  Lemma to_extended_list_lift_above Γ :
    Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
  Proof.
    pose (reln_list_lift_above [] 0 Γ).
    unfold to_extended_list.
    forward f. constructor. eapply Forall_impl; eauto. intros.
    destruct H; eexists; intuition eauto.
  Qed.

  Fixpoint reln_alt p (Γ : context) :=
    match Γ with
    | [] => []
    | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
    | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
    end.

  Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
  Proof.
    induction Γ in l, k |- *; simpl; auto.
    destruct a as [na [body|] ty]; simpl.
    now rewrite IHΓ.
    now rewrite IHΓ -app_assoc.
  Qed.

  Lemma to_extended_list_k_cons d Γ k :
    to_extended_list_k (d :: Γ) k =
    match d.(decl_body) with
    | None => to_extended_list_k Γ (S k) ++ [tRel k]
    | Some b => to_extended_list_k Γ (S k)
    end.
  Proof.
    unfold to_extended_list_k.
    rewrite reln_alt_eq. simpl.
    destruct d as [na [body|] ty]. simpl.
    now rewrite reln_alt_eq Nat.add_1_r.
    simpl. rewrite reln_alt_eq.
    now rewrite <- app_assoc, !app_nil_r, Nat.add_1_r.
  Qed.


  Definition arities_context (l : list one_inductive_body) :=
    rev_map (fun ind => vass (mkBindAnn (nNamed ind.(ind_name))
                            (ind.(ind_relevance))) ind.(ind_type)) l.

  Lemma arities_context_length l : #|arities_context l| = #|l|.
  Proof. unfold arities_context. now rewrite rev_map_length. Qed.
  #[global] Hint Rewrite arities_context_length : len.

  Lemma app_context_nil_l Γ : [] ,,, Γ = Γ.
  Proof.
    unfold app_context. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma app_context_assoc Γ Γ' Γ'' : Γ ,,, (Γ' ,,, Γ'') = Γ ,,, Γ' ,,, Γ''.
  Proof. unfold app_context; now rewrite app_assoc. Qed.

  Lemma app_context_cons Γ Γ' A : Γ ,,, (Γ' ,, A) = (Γ ,,, Γ') ,, A.
  Proof. exact (app_context_assoc _ _ [A]). Qed.

  Lemma app_context_length Γ Γ' : #|Γ ,,, Γ'| = #|Γ'| + #|Γ|.
  Proof. unfold app_context. now rewrite app_length. Qed.
  #[global] Hint Rewrite app_context_length : len.

  Lemma nth_error_app_context_ge v Γ Γ' :
    #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
  Proof. apply nth_error_app_ge. Qed.

  Lemma nth_error_app_context_lt v Γ Γ' :
    v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
  Proof. apply nth_error_app_lt. Qed.


  Definition map_mutual_inductive_body f m :=
    match m with
    | Build_mutual_inductive_body finite ind_npars ind_pars ind_bodies ind_universes ind_variance =>
      let arities := arities_context ind_bodies in
      let pars := fold_context_k f ind_pars in
      Build_mutual_inductive_body finite ind_npars pars
                                  (map (map_one_inductive_body (context_assumptions pars) (length arities) f) ind_bodies)
                                  ind_universes ind_variance
    end.

  Lemma ind_type_map f npars_ass arities oib :
    ind_type (map_one_inductive_body npars_ass arities f oib) = f 0 (ind_type oib).
  Proof. destruct oib. reflexivity. Qed.

  Lemma ind_ctors_map f npars_ass arities oib :
    ind_ctors (map_one_inductive_body npars_ass arities f oib) =
    map (map_constructor_body npars_ass arities f) (ind_ctors oib).
  Proof. destruct oib; simpl; reflexivity. Qed.

  Lemma ind_pars_map f m :
    ind_params (map_mutual_inductive_body f m) =
    fold_context_k f (ind_params m).
  Proof. destruct m; simpl; reflexivity. Qed.

  Lemma ind_projs_map f npars_ass arities oib :
    ind_projs (map_one_inductive_body npars_ass arities f oib) =
    map (map_projection_body npars_ass f) (ind_projs oib).
  Proof. destruct oib; simpl. reflexivity. Qed.

  Fixpoint projs ind npars k :=
    match k with
    | 0 => []
    | S k' => (tProj (mkProjection ind npars k') (tRel 0)) :: projs ind npars k'
    end.

  Lemma projs_length ind npars k : #|projs ind npars k| = k.
  Proof. induction k; simpl; auto. Qed.

  Lemma context_assumptions_fold Γ f : context_assumptions (fold_context_k f Γ) = context_assumptions Γ.
  Proof.
    rewrite fold_context_k_alt.
    unfold mapi. generalize 0 (Nat.pred #|Γ|).
    induction Γ as [|[na [body|] ty] tl]; cbn; intros; eauto.
  Qed.
  #[global] Hint Rewrite context_assumptions_fold : len.

  Lemma nth_error_fold_context_k (f : nat -> term -> term):
    forall (Γ' Γ'' : context) (v : nat),
      v < length Γ' -> forall nth,
        nth_error Γ' v = Some nth ->
        nth_error (fold_context_k f Γ') v = Some (map_decl (f (length Γ' - S v)) nth).
  Proof.
    induction Γ'; intros.
    - easy.
    - simpl. destruct v; rewrite fold_context_k_snoc0.
      + simpl. repeat f_equal; try lia. simpl in *. congruence.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_fold_context_k_eq:
    forall (Γ' : context) (v : nat) (f : nat -> term -> term),
      nth_error (fold_context_k f Γ') v =
      option_map (map_decl (f (length Γ' - S v))) (nth_error Γ' v).
  Proof.
    induction Γ'; intros.
    - simpl. unfold fold_context_k; simpl. now rewrite nth_error_nil.
    - simpl. destruct v; rewrite fold_context_k_snoc0.
      + simpl. repeat f_equal; try lia.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_ge {Γ Γ' v Γ''} (f : nat -> term -> term) :
    length Γ' <= v ->
    nth_error (Γ' ++ Γ) v =
    nth_error (fold_context_k f Γ' ++ Γ'' ++ Γ) (length Γ'' + v).
  Proof.
    intros Hv.
    rewrite -> !nth_error_app_ge, ?fold_context_k_length. f_equal. lia.
    rewrite fold_context_k_length. lia.
    rewrite fold_context_k_length. lia. auto.
  Qed.

  Lemma nth_error_lt {Γ Γ' Γ'' v} (f : nat -> term -> term) :
    v < length Γ' ->
    nth_error (fold_context_k f Γ' ++ Γ'' ++ Γ) v =
    option_map (map_decl (f (length Γ' - S v))) (nth_error (Γ' ++ Γ) v).
  Proof.
    simpl. intros Hv.
    rewrite -> !nth_error_app_lt.
    rewrite nth_error_fold_context_k_eq.
    do 2 f_equal. lia. now rewrite fold_context_k_length.
  Qed.

  Lemma context_assumptions_length_bound Γ : context_assumptions Γ <= #|Γ|.
  Proof.
    induction Γ; simpl; auto. destruct a as [? [?|] ?]; simpl; auto.
    lia.
  Qed.

  Lemma context_assumptions_map f Γ : context_assumptions (map_context f Γ) = context_assumptions Γ.
  Proof.
    induction Γ as [|[? [?|] ?] ?]; simpl; auto.
  Qed.

  Lemma context_assumptions_app Γ Δ : context_assumptions (Γ ++ Δ) =
    context_assumptions Γ + context_assumptions Δ.
  Proof.
    induction Γ as [|[? [] ?] ?]; simpl; auto.
  Qed.

  Lemma context_assumptions_rev Γ : context_assumptions (List.rev Γ) = context_assumptions Γ.
  Proof using Type.
    induction Γ; simpl; auto. rewrite context_assumptions_app IHΓ /=.
    destruct (decl_body a); simpl; lia.
  Qed.


  Lemma context_assumptions_mapi f Γ : context_assumptions (mapi (fun i => map_decl (f i)) Γ) =
    context_assumptions Γ.
  Proof.
    rewrite /mapi; generalize 0.
    induction Γ; simpl; intros; eauto.
    destruct a as [? [b|] ?]; simpl; auto.
  Qed.

  #[global] Hint Rewrite context_assumptions_map context_assumptions_mapi context_assumptions_app : len.

  Lemma context_assumptions_subst_instance u Γ :
    context_assumptions (subst_instance u Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_map. Qed.

  Lemma context_assumptions_subst_context s k Γ :
    context_assumptions (subst_context s k Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_fold. Qed.

  Lemma context_assumptions_lift_context n k Γ :
    context_assumptions (lift_context n k Γ) =
    context_assumptions Γ.
  Proof. apply context_assumptions_fold. Qed.

  #[global] Hint Rewrite context_assumptions_subst_instance
     context_assumptions_subst_context context_assumptions_lift_context : len.

  (** Lifting a relation to declarations, without alpha renaming. *)
  Inductive All_decls (P : term -> term -> Type) : context_decl -> context_decl -> Type :=
  | on_vass na t t' :
    P t t' ->
    All_decls P (vass na t) (vass na t')

  | on_vdef na b t b' t' :
    P b b' ->
    P t t' ->
    All_decls P (vdef na b t) (vdef na b' t').
  Derive Signature NoConfusion for All_decls.

  (** Allow alpha-renaming of binders *)
  Inductive All_decls_alpha (P : term -> term -> Type) : context_decl -> context_decl -> Type :=
  | on_vass_alpha na na' t t' :
    eq_binder_annot na na' ->
    P t t' ->
    All_decls_alpha P (vass na t) (vass na' t')

  | on_vdef_alpha na na' b t b' t' :
    eq_binder_annot na na' ->
    P b b' ->
    P t t' ->
    All_decls_alpha P (vdef na b t) (vdef na' b' t').
  Derive Signature NoConfusion for All_decls_alpha.

  Lemma All_decls_impl (P Q : term -> term -> Type) d d' :
    All_decls P d d' ->
    (forall t t', P t t' -> Q t t') ->
    All_decls Q d d'.
  Proof.
    intros ond H; destruct ond; constructor; auto.
  Qed.

  Lemma All_decls_alpha_impl (P Q : term -> term -> Type) d d' :
    All_decls_alpha P d d' ->
    (forall t t', P t t' -> Q t t') ->
    All_decls_alpha Q d d'.
  Proof.
    intros ond H; destruct ond; constructor; auto.
  Qed.

  Lemma All_decls_to_alpha (P : term -> term -> Type) d d' :
    All_decls P d d' ->
    All_decls_alpha P d d'.
  Proof.
    intros []; constructor; auto; reflexivity.
  Qed.

  Definition All2_fold_over (P : context -> context -> context_decl -> context_decl -> Type) Γ Γ' :=
    All2_fold (All_over P Γ Γ').

  Notation on_decls P := (fun Γ Γ' => All_decls (P Γ Γ')).
  Notation on_contexts P := (All2_fold (on_decls P)).
  Notation on_contexts_over P Γ Γ' := (All2_fold (All_over (on_decls P) Γ Γ')).

End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.

Module Type TermUtils (T: Term) (E: EnvironmentSig T).
  Import T E.

  Parameter Inline destArity : context -> term -> option (context × Universe.t).
  Parameter Inline inds : kername -> Instance.t -> list one_inductive_body -> list term.

End TermUtils.
