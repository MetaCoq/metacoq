(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Template Require Import Universes.
From Coq Require Import ssreflect ssrfun Morphisms.

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
  
End Term.

Module Environment (T : Term).

  Import T.

  (** ** Declarations *)

  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.

  (** Local (de Bruijn) variable binding *)

  Definition vass x A :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdef x t A :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.

  (** Last declaration first *)

  Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

  Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

  Definition map_decl f (d : context_decl) :=
    {| decl_name := d.(decl_name);
       decl_body := option_map f d.(decl_body);
       decl_type := f d.(decl_type) |}.       

  Lemma map_decl_type f decl : f (decl_type decl) = decl_type (map_decl f decl).
  Proof. destruct decl; reflexivity. Qed.

  Lemma map_decl_body f decl : option_map f (decl_body decl) = decl_body (map_decl f decl).
  Proof. destruct decl; reflexivity. Qed.

  Lemma option_map_decl_body_map_decl f x :
    option_map decl_body (option_map (map_decl f) x) =
    option_map (option_map f) (option_map decl_body x).
  Proof. destruct x; reflexivity. Qed.

  Lemma option_map_decl_type_map_decl f x :
    option_map decl_type (option_map (map_decl f) x) =
    option_map f (option_map decl_type x).
  Proof. destruct x; reflexivity. Qed.

  Definition map_context f c :=
    List.map (map_decl f) c.
    
  Lemma map_context_length f l : #|map_context f l| = #|l|.
  Proof. now unfold map_context; rewrite map_length. Qed.
  Hint Rewrite map_context_length : len.

  Definition fold_context f (Γ : context) : context :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Arguments fold_context f Γ%list_scope.

  Lemma fold_context_alt f Γ :
    fold_context f Γ =
    mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
  Proof.
    unfold fold_context. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
  Qed.

  Lemma fold_context_length f Γ : length (fold_context f Γ) = length Γ.
  Proof.
    unfold fold_context. now rewrite !List.rev_length mapi_length List.rev_length.
  Qed.
  Hint Rewrite fold_context_length : len.

  Lemma fold_context_snoc0 f Γ d :
    fold_context f (d :: Γ) = fold_context f Γ ,, map_decl (f (length Γ)) d.
  Proof.
    unfold fold_context.
    rewrite !rev_mapi !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
    unfold snoc. f_equal. now rewrite Nat.sub_0_r List.rev_length.
    rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
    rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
  Qed.

  Lemma fold_context_app f Γ Δ :
    fold_context f (Δ ++ Γ)
    = fold_context (fun k => f (length Γ + k)) Δ ++ fold_context f Γ.
  Proof.
    unfold fold_context.
    rewrite List.rev_app_distr.
    rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
    apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal.
  Qed. 
  
  Lemma compose_map_decl f g x : map_decl f (map_decl g x) = map_decl (f ∘ g) x.
  Proof.
    destruct x as [? [?|] ?]; reflexivity.
  Qed.
  
  Lemma map_decl_ext f g x : (forall x, f x = g x) -> map_decl f x = map_decl g x.
  Proof.
    intros H; destruct x as [? [?|] ?]; rewrite /map_decl /=; f_equal; auto.
    now rewrite (H t).
  Qed.

  Instance map_decl_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) map_decl.
  Proof.
    intros f g Hfg x y ->. now apply map_decl_ext.
  Qed.

  Lemma fold_context_compose f g Γ : 
    fold_context f (fold_context g Γ) = 
    fold_context (fun i => f i ∘ g i) Γ.
  Proof.
    rewrite !fold_context_alt mapi_mapi.
    apply mapi_ext => i d.
    rewrite compose_map_decl. apply map_decl_ext => t.
    now len.
  Qed.

  Definition lift_decl n k d := (map_decl (lift n k) d).

  Definition lift_context n k (Γ : context) : context :=
    fold_context (fun k' => lift n (k' + k)) Γ.
  
  Lemma lift_context_alt n k Γ :
    lift_context n k Γ =
    mapi (fun k' d => lift_decl n (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold lift_context. apply fold_context_alt.
  Qed.

  Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
  Proof. now rewrite /lift_context; len. Qed.
  Hint Rewrite lift_context_length : len.

  Definition subst_context s k (Γ : context) : context :=
    fold_context (fun k' => subst s (k' + k)) Γ.
  
  Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.
  
  Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
  Proof. now rewrite /subst_context; len. Qed.
  Hint Rewrite subst_context_length : len.

  Lemma subst_context_nil s n : subst_context s n [] = [].
  Proof. reflexivity. Qed.
  
  Lemma subst_context_alt s k Γ :
    subst_context s k Γ =
    mapi (fun k' d => subst_decl s (Nat.pred #|Γ| - k' + k) d) Γ.
  Proof.
    unfold subst_context, fold_context. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
  Qed.
  
  Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
  Proof.
    now rewrite /subst_context fold_context_snoc0.
  Qed.
  
  Definition subst_telescope s k (Γ : context) : context :=
    mapi (fun k' decl => map_decl (subst s (k' + k)) decl) Γ.

  Instance subst_instance_decl : UnivSubst context_decl
    := map_decl ∘ subst_instance_constr.
  
  Instance subst_instance_context : UnivSubst context
    := map_context ∘ subst_instance_constr.

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
  Hint Rewrite smash_context_length : len.
  
  (* Smashing a context Γ with Δ depending on it is the same as smashing Γ
    and substituting all references to Γ in Δ by the expansions of let bindings. *)
  
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

  Definition expand_lets_k Γ k t := 
    (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

  Definition expand_lets Γ t := expand_lets_k Γ 0 t.

  Definition expand_lets_k_ctx Γ k Δ := 
    (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

  Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.

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

  Definition map_constructor_body npars arities f c :=
    {| cstr_name := c.(cstr_name);
       cstr_args := fold_context (fun x => f (x + npars + arities)) c.(cstr_args);
       cstr_indices := map (f (npars + arities + #|c.(cstr_args)|)) c.(cstr_indices);
        (* Note only after positivity checking we can ensure that the indices do not mention the 
           inductive type.. beware of lets! *)
       cstr_type := f arities c.(cstr_type);
       cstr_arity := c.(cstr_arity) |}.

  (** See [one_inductive_body] from [declarations.ml]. *)
  Record one_inductive_body := {
    ind_name : ident;
    ind_indices : context; (* Indices of the inductive types, under params *)
    ind_sort : Universe.t; (* Sort of the inductive. *)
    ind_type : term; (* Closed arity = forall mind_params, ind_indices, tSort ind_sort *)
    ind_kelim : allowed_eliminations; (* Allowed eliminations *)
    ind_ctors : list constructor_body;
    ind_projs : list (ident * term); (* names and types of projections, if any.
                                      Type under context of params and inductive object *)
    ind_relevance : relevance (* relevance of the inductive definition *) }.

  Definition map_one_inductive_body npars arities f m :=
    match m with
    | Build_one_inductive_body ind_name ind_indices ind_sort 
        ind_type ind_kelim ind_ctors ind_projs ind_relevance =>
      Build_one_inductive_body
         ind_name (fold_context (fun x => f (npars + x)) ind_indices) ind_sort
                  (f 0 ind_type) ind_kelim (map (map_constructor_body npars arities f) ind_ctors)
                  (map (on_snd (f (S npars))) ind_projs) ind_relevance
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
      cst_universes : universes_decl }.

  Definition map_constant_body f decl :=
    {| cst_type := f decl.(cst_type);
       cst_body := option_map f decl.(cst_body);
       cst_universes := decl.(cst_universes) |}.

  Lemma map_cst_type f decl :
    f (cst_type decl) = cst_type (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  Lemma map_cst_body f decl :
    option_map f (cst_body decl) = cst_body (map_constant_body f decl).
  Proof. destruct decl; reflexivity. Qed.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  Definition global_env := list (kername * global_decl).

  (** A context of global declarations + global universe constraints,
      i.e. a global environment *)

  Definition global_env_ext : Type := global_env * universes_decl.

  (** Use a coercion for this common projection of the global context. *)
  Definition fst_ctx : global_env_ext -> global_env := fst.
  Coercion fst_ctx : global_env_ext >-> global_env.

  Definition empty_ext (Σ : global_env) : global_env_ext
    := (Σ, Monomorphic_ctx ContextSet.empty).

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

  Lemma reln_list_lift_above l p Γ :
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
    Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
  Proof.
    generalize (le_refl p).
    generalize p at 1 3 5.
    induction Γ in p, l |- *. simpl. auto.
    intros. destruct a. destruct decl_body0. simpl.
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

  Fixpoint reln_alt p Γ :=
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
  Hint Rewrite arities_context_length : len.
  
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
  Hint Rewrite app_context_length : len.

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
      let pars := fold_context f ind_pars in
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
    fold_context f (ind_params m).
  Proof. destruct m; simpl; reflexivity. Qed.

  Lemma ind_projs_map f npars_ass arities oib :
    ind_projs (map_one_inductive_body npars_ass arities f oib) =
    map (on_snd (f (S npars_ass))) (ind_projs oib).
  Proof. destruct oib; simpl. reflexivity. Qed.

  Fixpoint lookup_env (Σ : global_env) (kn : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if eq_kername kn d.1 then Some d.2
      else lookup_env tl kn
    end.

  Lemma context_assumptions_fold Γ f : context_assumptions (fold_context f Γ) = context_assumptions Γ.
  Proof.
    rewrite fold_context_alt.
    unfold mapi. generalize 0 (Nat.pred #|Γ|).
    induction Γ as [|[na [body|] ty] tl]; cbn; intros; eauto.
  Qed.
  Hint Rewrite context_assumptions_fold : len.

  Lemma nth_error_fold_context (f : nat -> term -> term):
    forall (Γ' Γ'' : context) (v : nat),
      v < length Γ' -> forall nth,
        nth_error Γ' v = Some nth ->
        nth_error (fold_context f Γ') v = Some (map_decl (f (length Γ' - S v)) nth).
  Proof.
    induction Γ'; intros.
    - easy.
    - simpl. destruct v; rewrite fold_context_snoc0.
      + simpl. repeat f_equal; try lia. simpl in *. congruence.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_fold_context_eq:
    forall (Γ' : context) (v : nat) f,
      nth_error (fold_context f Γ') v =
      option_map (map_decl (f (length Γ' - S v))) (nth_error Γ' v).
  Proof.
    induction Γ'; intros.
    - simpl. unfold fold_context, fold_context; simpl. now rewrite nth_error_nil.
    - simpl. destruct v; rewrite fold_context_snoc0.
      + simpl. repeat f_equal; try lia.
      + simpl. apply IHΓ'; simpl in *; (lia || congruence).
  Qed.

  Lemma nth_error_ge {Γ Γ' v Γ''} f :
    length Γ' <= v ->
    nth_error (Γ' ++ Γ) v =
    nth_error (fold_context (f 0) Γ' ++ Γ'' ++ Γ) (length Γ'' + v).
  Proof.
    intros Hv.
    rewrite -> !nth_error_app_ge, ?fold_context_length. f_equal. lia.
    rewrite fold_context_length. lia.
    rewrite fold_context_length. lia. auto.
  Qed.

  Lemma nth_error_lt {Γ Γ' Γ'' v} (f : nat -> term -> term) :
    v < length Γ' ->
    nth_error (fold_context f Γ' ++ Γ'' ++ Γ) v =
    option_map (map_decl (f (length Γ' - S v))) (nth_error (Γ' ++ Γ) v).
  Proof.
    simpl. intros Hv.
    rewrite -> !nth_error_app_lt.
    rewrite nth_error_fold_context_eq.
    do 2 f_equal. lia. now rewrite fold_context_length.
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
  
  Lemma context_assumptions_mapi f Γ : context_assumptions (mapi (fun i => map_decl (f i)) Γ) = 
    context_assumptions Γ.
  Proof.
    rewrite /mapi; generalize 0.
    induction Γ; simpl; intros; eauto.
    destruct a as [? [b|] ?]; simpl; auto.
  Qed.
  
  Hint Rewrite context_assumptions_map context_assumptions_mapi context_assumptions_app : len.

  Lemma context_assumptions_subst_instance_context u Γ : 
    context_assumptions (subst_instance_context u Γ) = 
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
  
  Hint Rewrite context_assumptions_subst_instance_context
     context_assumptions_subst_context context_assumptions_lift_context : len.

  Lemma fold_context_ext f g c : 
    (forall i, f i =1 g i) ->
    fold_context f c = fold_context g c.
  Proof.
    intros Hfg.
    rewrite !fold_context_alt.
    eapply mapi_ext => i d.
    eapply map_decl_ext => t.
    now rewrite Hfg.
  Qed.

  Lemma fold_context_map f g Γ : 
    (forall i x, f i (g x) = g (f i x)) ->
    fold_context f (map_context g Γ) = map_context g (fold_context f Γ).
  Proof.
    intros Hfg.
    rewrite !fold_context_alt mapi_map.
    rewrite /map_context map_mapi.
    apply mapi_ext => i x.
    rewrite !compose_map_decl.
    apply map_decl_ext => t.
    rewrite Hfg.
    now len.
  Qed.
End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.

(* Defined here since BasicAst does not have access to universe instances.
   Parameterized by term types as they are not yet defined. *)
Record predicate {term} := mkpredicate {
  pparams : list term; (* The parameters *)
  puinst : Instance.t; (* The universe instance *)
  pcontext : list aname; (* Names of binders of indices and inductive application,
                          in same order as context (i.e. name of "inductive application"
                          binder is first). Types are obtained from inductive declaration.
                          Also used for lifting/substitution for the return type. *)
  preturn : term; (* The return type *) }.

Arguments predicate : clear implicits.
Arguments mkpredicate {_}.

Derive NoConfusion for predicate.
Global Instance predicate_eq_dec term :
  Classes.EqDec term ->
  Classes.EqDec (predicate term).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_predicate {term} (f : term -> string) (p : predicate term) :=
  "(" ^ "(" ^ String.concat "," (map f (pparams p)) ^ ")" 
  ^ "," ^ string_of_universe_instance (puinst p)
  ^ ",(" ^ String.concat "," (map (string_of_name ∘ binder_name) (pcontext p)) ^ ")"
  ^ "," ^ f (preturn p) ^ ")".

Definition test_predicate {term}
           (instf : Instance.t -> bool) (paramf preturnf : term -> bool) (p : predicate term) :=
  instf p.(puinst) && forallb paramf p.(pparams) && preturnf p.(preturn).

Definition eqb_predicate {term} (eqb_univ_instance : Instance.t -> Instance.t -> bool) (eqterm : term -> term -> bool) (p p' : predicate term) :=
  forallb2 eqterm p.(pparams) p'.(pparams) &&
  eqb_univ_instance p.(puinst) p'.(puinst) &&
  forallb2 eqb_binder_annot p.(pcontext) p'.(pcontext) &&
  eqterm p.(preturn) p'.(preturn).
  
Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').
  
  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
       puinst := uf p.(puinst);
       pcontext := p.(pcontext);
       preturn := preturnf p.(preturn) |}.

  Lemma map_pparams (p : predicate term) :
    map paramf (pparams p) = pparams (map_predicate p).
  Proof. reflexivity. Qed.

  Lemma map_preturn (p : predicate term) :
    preturnf (preturn p) = preturn (map_predicate p).
  Proof. reflexivity. Qed.

  Lemma map_puints (p : predicate term) :
    uf (puinst p) = puinst (map_predicate p).
  Proof. reflexivity. Qed.

End map_predicate.

Lemma map_predicate_map_predicate
      {term term' term''}
      (finst finst' : Instance.t -> Instance.t)
      (f g : term' -> term'')
      (f' g' : term -> term')
      (p : predicate term) :
  map_predicate finst f g (map_predicate finst' f' g' p) =
  map_predicate (finst ∘ finst') (f ∘ f') (g ∘ g') p.
Proof.
  destruct p; cbv.
  f_equal.
  apply map_map.
Qed.

Lemma map_predicate_id {t} x : map_predicate (@id _) (@id t) (@id t) x = id x.
Proof.
  destruct x; cbv.
  f_equal.
  apply map_id.
Qed.
Hint Rewrite @map_predicate_id : map.

Definition tCasePredProp {term}
           (Pparams Preturn : term -> Type)
           (p : predicate term) :=
  All Pparams p.(pparams) × Preturn p.(preturn).
(*
Lemma map_predicate_spec
      {term term'}
      (f : term' -> term'')
      (g : uinst' -> uinst'')
      (h : term' -> term'')
      (f' : term -> term')
      (g' : uinst -> uinst')
      (h' : term -> term')
      (p : predicate term uinst) :

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  now rewrite !H, !H0.
Qed.
*)

Lemma map_predicate_eq_spec {A B} (finst finst' : Instance.t -> Instance.t) (f f' g g' : A -> B) (p : predicate A) :
  finst (puinst p) = finst' (puinst p) ->
  map f (pparams p) = map g (pparams p) ->
  f' (preturn p) = g' (preturn p) ->
  map_predicate finst f f' p = map_predicate finst' g g' p.
Proof.
  intros. unfold map_predicate; f_equal; auto.
Qed.
Hint Resolve map_predicate_eq_spec : all.

Lemma map_predicate_id_spec {A} finst (f f' : A -> A) (p : predicate A) :
  finst (puinst p) = puinst p ->
  map f (pparams p) = pparams p ->
  f' (preturn p) = preturn p ->
  map_predicate finst f f' p = p.
Proof.
  unfold map_predicate.
  intros -> -> ->; destruct p; auto.
Qed.
Hint Resolve map_predicate_id_spec : all.

Instance id_proper_proxy {A} : ProperProxy (`=1`) (@id A).
Proof.
  intros x; reflexivity.
Qed.

Instance map_predicate_proper {term} : Proper (`=1` ==> `=1` ==> Logic.eq ==> Logic.eq) (@map_predicate term term id).
Proof.
  intros eqf0 eqf1 eqf.
  intros eqf'0 eqf'1 eqf'.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
  now apply map_ext => x.
Qed.

Instance map_predicate_proper' {term} f : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_predicate term term id f).
Proof.
  intros eqf0 eqf1 eqf.
  intros x y ->.
  apply map_predicate_eq_spec; auto.
Qed.

Instance map_branch_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_branch term term).
Proof.
  intros eqf0 eqf1 eqf.
  intros x y ->.
  apply map_branch_eq_spec; auto.
Qed.    
  