From Coq Require Import Ascii OrderedType Arith Lia.
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Template Require Import Universes.
Import List.ListNotations.

Set Asymmetric Patterns.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.
  Parameter Inline tSort : Universe.t -> term.
  Parameter Inline tProd : name -> term -> term -> term.
  Parameter Inline tLambda : name -> term -> term -> term.
  Parameter Inline tLetIn : name -> term -> term -> term -> term.
  Parameter Inline tInd : inductive -> Instance.t -> term.
  Parameter Inline tProj : projection -> term -> term.
  Parameter Inline mkApps : term -> list term -> term.

End Term.

Module Environment (T : Term).

  Import T.

  (** ** Declarations *)

  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : name ;
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

  Definition fold_context f (Γ : context) : context :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Lemma fold_context_alt f Γ :
    fold_context f Γ =
    mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
  Proof.
    unfold fold_context. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
  Qed.

  Lemma fold_context_length f Γ : length (fold_context f Γ) = length Γ.
  Proof.
    unfold fold_context. now rewrite !List.rev_length, mapi_length, List.rev_length.
  Qed.

  Lemma fold_context_snoc0 f Γ d :
    fold_context f (d :: Γ) = fold_context f Γ ,, map_decl (f (length Γ)) d.
  Proof.
    unfold fold_context.
    rewrite !rev_mapi, !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
    unfold snoc. f_equal. now rewrite Nat.sub_0_r, List.rev_length.
    rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
    rewrite app_length, !List.rev_length. simpl. f_equal. f_equal. lia.
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


  (** *** Environments *)

  (** See [one_inductive_body] from [declarations.ml]. *)
  Record one_inductive_body := {
    ind_name : ident;
    ind_type : term; (* Closed arity *)
    ind_kelim : sort_family; (* Top allowed elimination sort *)
    ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                      * nat (* arity, w/o lets, w/o parameters *));
    ind_projs : list (ident * term) (* names and types of projections, if any.
                                      Type under context of params and inductive object *) }.

  Definition map_one_inductive_body npars arities f (n : nat) m :=
    match m with
    | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
      Build_one_inductive_body ind_name
                               (f 0 ind_type)
                               ind_kelim
                               (map (on_pi2 (f arities)) ind_ctors)
                               (map (on_snd (f (S npars))) ind_projs)
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

  Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
  Notation " Γ  ,,, Γ' " :=
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
    now rewrite IHΓ, <- app_assoc.
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
    now rewrite reln_alt_eq, Nat.add_1_r.
    simpl. rewrite reln_alt_eq.
    now rewrite <- app_assoc, !app_nil_r, Nat.add_1_r.
  Qed.


  Definition arities_context (l : list one_inductive_body) :=
    rev_map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

  Lemma arities_context_length l : #|arities_context l| = #|l|.
  Proof. unfold arities_context. now rewrite rev_map_length. Qed.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

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
                                  (mapi (map_one_inductive_body (context_assumptions pars) (length arities) f) ind_bodies)
                                  ind_universes ind_variance
    end.

  Lemma ind_type_map f npars_ass arities n oib :
    ind_type (map_one_inductive_body npars_ass arities f n oib) = f 0 (ind_type oib).
  Proof. destruct oib. reflexivity. Qed.

  Lemma ind_ctors_map f npars_ass arities n oib :
    ind_ctors (map_one_inductive_body npars_ass arities f n oib) =
    map (on_pi2 (f arities)) (ind_ctors oib).
  Proof. destruct oib; simpl; reflexivity. Qed.

  Lemma ind_pars_map f m :
    ind_params (map_mutual_inductive_body f m) =
    fold_context f (ind_params m).
  Proof. destruct m; simpl; reflexivity. Qed.

  Lemma ind_projs_map f npars_ass arities n oib :
    ind_projs (map_one_inductive_body npars_ass arities f n oib) =
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

  Lemma nth_error_ge {Γ Γ' v Γ''} f : length Γ' <= v ->
                                      nth_error (Γ' ++ Γ) v =
                                      nth_error (fold_context (f 0) Γ' ++ Γ'' ++ Γ) (length Γ'' + v).
  Proof.
    intros Hv.
    rewrite -> !nth_error_app_ge, ?fold_context_length. f_equal. lia.
    rewrite fold_context_length. lia.
    rewrite fold_context_length. lia. auto.
  Qed.

  Lemma nth_error_lt {Γ Γ' Γ'' v} (f : nat -> term -> term) : v < length Γ' ->
                                                          nth_error (fold_context f Γ' ++ Γ'' ++ Γ) v =
                                                          option_map (map_decl (f (length Γ' - S v))) (nth_error (Γ' ++ Γ) v).
  Proof.
    simpl. intros Hv.
    rewrite -> !nth_error_app_lt.
    rewrite nth_error_fold_context_eq.
    do 2 f_equal. lia. now rewrite fold_context_length.
  Qed.
End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.
