From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import BasicAst Ast utils.
Import List.ListNotations.
Require Import ssreflect.

Set Asymmetric Patterns.

(** Raw term printing *)

Local Open Scope string_scope.

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f "," l ++ "]".

Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lProp => "Prop"
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ++ string_of_nat n
  end.

Definition string_of_level_expr (l : Level.t * bool) : string :=
  let '(l, b) := l in
  string_of_level l ++ (if b then "+1" else "").

Definition string_of_sort (u : universe) :=
  string_of_list string_of_level_expr u.
Definition string_of_name (na : name) :=
  match na with
  | nAnon => "Anonymous"
  | nNamed n => n
  end.
Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dtype def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Definition string_of_inductive (i : inductive) :=
  (inductive_mind i) ++ "," ++ string_of_nat (inductive_ind i).

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ++ string_of_nat n ++ ")"
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "," ++ string_of_list string_of_term args ++ ")"
  | tSort s => "Sort(" ++ string_of_sort s ++ ")"
  | tCast c k t => "Cast(" ++ string_of_term c ++ (* TODO *) ","
                           ++ string_of_term t ++ ")"
  | tProd na b t => "Prod(" ++ string_of_name na ++ "," ++
                            string_of_term b ++ "," ++ string_of_term t ++ ")"
  | tLambda na b t => "Lambda(" ++ string_of_name na ++ "," ++ string_of_term b
                                ++ "," ++ string_of_term t ++ ")"
  | tLetIn na b t' t => "LetIn(" ++ string_of_name na ++ "," ++ string_of_term b
                                 ++ "," ++ string_of_term t' ++ "," ++ string_of_term t ++ ")"
  | tApp f l => "App(" ++ string_of_term f ++ "," ++ string_of_list string_of_term l ++ ")"
  | tConst c u => "Const(" ++ c ++ "," ++ string_of_universe_instance u ++ ")"
  | tInd i u => "Ind(" ++ string_of_inductive i ++ "," ++ string_of_universe_instance u ++ ")"
  | tConstruct i n u => "Construct(" ++ string_of_inductive i ++ "," ++ string_of_nat n ++ ","
                                    ++ string_of_universe_instance u ++ ")"
  | tCase (ind, i) t p brs =>
    "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
            ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
            ++ string_of_term c ++ ")"
  | tFix l n => "Fix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  | tCoFix l n => "CoFix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  end.
Local Close Scope string_scope.

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

Definition map_constant_body f decl :=
  {| cst_type := f decl.(cst_type);
     cst_body := option_map f decl.(cst_body);
     cst_universes := decl.(cst_universes) |}.

Lemma map_cst_type f decl : f (cst_type decl) = cst_type (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma map_cst_body f decl : option_map f (cst_body decl) = cst_body (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Definition map_def {A B : Set} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

Lemma app_context_assoc Γ Γ' Γ'' : Γ ,,, (Γ' ,,, Γ'') = Γ ,,, Γ' ,,, Γ''.
Proof. unfold app_context; now rewrite app_assoc. Qed.

Lemma app_context_length Γ Γ' : #|Γ ,,, Γ'| = #|Γ'| + #|Γ|.
Proof. unfold app_context. now rewrite app_length. Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. lia.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_context_ge v Γ Γ' : #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
Proof. apply nth_error_app_ge. Qed.

Lemma nth_error_app_context_lt v Γ Γ' : v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
Proof. apply nth_error_app_lt. Qed.

Lemma app_context_nil_l Γ : [] ,,, Γ = Γ.
Proof. unfold app_context; now rewrite app_nil_r. Qed.

Definition string_of_gref gr : string :=
  match gr with
  | VarRef s => "Variable " ++ s
  | ConstRef s => s
  | IndRef (mkInd s n) =>
    "Inductive " ++ s ++ " " ++ (string_of_nat n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ++ s ++ " " ++ (string_of_nat n) ++ " " ++ (string_of_nat k)
  end.

Definition gref_eq_dec
: forall gr gr' : global_reference, {gr = gr'} + {~ gr = gr'}.
Proof.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
Defined.

Definition ident_eq (x y : ident) :=
  match string_compare x y with
  | Eq => true
  | _ => false
  end.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct (string_compare_eq x y).
  destruct string_compare; constructor; auto.
  intro Heq; specialize (H0 Heq). discriminate.
  intro Heq; specialize (H0 Heq). discriminate.
Qed.

Definition eq_string s s' :=
  if string_compare s s' is Eq then true else false.

Definition eq_ind i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eq_string i i' && Nat.eqb n n'.

Definition eq_constant := eq_string.

Definition eq_nat := Nat.eqb.
Definition eq_evar := eq_nat.
Definition eq_projection p p' :=
  let '(ind, pars, arg) := p in
  let '(ind', pars', arg') := p' in
  eq_ind ind ind' && eq_nat pars pars' && eq_nat arg arg'.

Lemma eq_string_refl x : eq_string x x.
Proof.
  unfold eq_string.
  now rewrite (proj2 (string_compare_eq x x) eq_refl).
Qed.

Lemma eq_ind_refl i : eq_ind i i.
Proof.
  destruct i as [mind k].
  unfold eq_ind. now rewrite eq_string_refl Nat.eqb_refl.
Qed.

Lemma eq_nat_refl n : eq_nat n n.
Proof. by rewrite /eq_nat Nat.eqb_refl. Qed.

Lemma eq_projection_refl i : eq_projection i i.
Proof.
  destruct i as [[mind k] p].
  unfold eq_projection.
  now rewrite eq_ind_refl !eq_nat_refl.
Qed.

Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros.
  destruct l; simpl;
    destruct f; simpl; try (discriminate || reflexivity).
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l; destruct f; destruct l'; simpl; rewrite ?app_nil_r; auto.
  f_equal. now rewrite <- app_assoc.
Qed.

Lemma mkApp_mkApps f a l : mkApp (mkApps f l) a = mkApps f (l ++ [a]).
Proof.
  destruct l. simpl. reflexivity.
  rewrite <- mkApps_nested. reflexivity.
Qed.

Lemma mkApp_tApp f u : isApp f = false -> mkApp f u = tApp f [u].
Proof. intros. destruct f; (discriminate || reflexivity). Qed.

Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Definition get_ident (n : name) : string :=
  match n with
  | nAnon => "XX"
  | nNamed i => i
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

Fixpoint lookup_mind_decl (id : ident) (decls : global_env)
 := match decls with
    | nil => None
    | InductiveDecl kn d :: tl =>
      if string_compare kn id is Eq then Some d else lookup_mind_decl id tl
    | _ :: tl => lookup_mind_decl id tl
    end.

(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => List.rev _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.combine _ _).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.

Definition arities_context (l : list one_inductive_body) :=
  rev_map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

Lemma arities_context_length l : #|arities_context l| = #|l|.
Proof. unfold arities_context. now rewrite rev_map_length. Qed.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | tCast t _ _ => decompose_prod_assum Γ t
  | _ => (Γ, t)
  end.

Fixpoint strip_outer_cast t :=
  match t with
  | tCast t _ _ => strip_outer_cast t
  | _ => t
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Lemma it_mkProd_or_LetIn_app l l' t :
  it_mkProd_or_LetIn (l ++ l') t = it_mkProd_or_LetIn l' (it_mkProd_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

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
  intros. destruct a. destruct decl_body. simpl.
  assert(p0 <= S p) by lia.
  specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
  simpl in *.
  specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
  simpl in *.
  constructor. exists p. intuition lia. auto.
Qed.

Lemma to_extended_list_k_spec Γ k :
  Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ) (to_extended_list_k Γ k).
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
  rewrite /to_extended_list_k reln_alt_eq. simpl.
  destruct d as [na [body|] ty]. simpl.
  now rewrite reln_alt_eq Nat.add_1_r.
  simpl. rewrite reln_alt_eq.
  now rewrite -app_assoc !app_nil_r Nat.add_1_r.
Qed.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx c => Instance.empty
  | Polymorphic_ctx c
  | Cumulative_ctx (c, _) => fst (AUContext.repr c)
  end.

Fixpoint context_assumptions (Γ : context) :=
  match Γ with
  | [] => 0
  | d :: Γ =>
    match d.(decl_body) with
    | Some _ => context_assumptions Γ
    | None => S (context_assumptions Γ)
    end
  end.

Definition map_one_inductive_body npars arities f (n : nat) m :=
  match m with
  | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
    Build_one_inductive_body ind_name
                             (f 0 ind_type)
                             ind_kelim
                             (map (on_pi2 (f arities)) ind_ctors)
                             (map (on_snd (f (S npars))) ind_projs)
  end.

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
  unfold fold_context. now rewrite !List.rev_length mapi_length List.rev_length.
Qed.

Lemma fold_context_snoc0 f Γ d : fold_context f (d :: Γ) = fold_context f Γ ,, map_decl (f (length Γ)) d.
Proof.
  unfold fold_context.
  rewrite !rev_mapi !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
  unfold snoc. f_equal. now rewrite Nat.sub_0_r List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
Qed.

Lemma fold_context_app f Γ Δ :
  fold_context f (Δ ++ Γ) = fold_context (fun k => f (length Γ + k)) Δ ++ fold_context f Γ.
Proof.
  unfold fold_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal.
Qed.

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

Definition map_mutual_inductive_body f m :=
  match m with
  | Build_mutual_inductive_body finite ind_npars ind_pars ind_bodies ind_universes =>
    let arities := arities_context ind_bodies in
    let pars := fold_context f ind_pars in
    Build_mutual_inductive_body finite ind_npars pars
      (mapi (map_one_inductive_body (context_assumptions pars) (length arities) f) ind_bodies)
      ind_universes
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

Definition test_def {A : Set} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tCaseBrsProp {A} (P : A -> Prop) (l : list (nat * A)) :=
  Forall (fun x => P (snd x)) l.

Definition tFixProp {A : Set} (P P' : A -> Prop) (m : mfixpoint A) :=
  Forall (fun x : def A => P x.(dtype) /\ P' x.(dbody)) m.


Ltac merge_All :=
  unfold tFixProp, tCaseBrsProp in *;
  repeat toAll.


Lemma map_def_map_def {A B C : Set} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (fun x => f (g x)) (fun x => f' (g' x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C : Set} (f f' : B -> C) (g g' : A -> B) :
  compose (A:=def A) (map_def f f') (map_def g g') = map_def (compose f g) (compose f' g').
Proof. reflexivity. Qed.

Lemma map_def_id {t : Set} x : map_def (@id t) (@id t) x = id x.
Proof. now destruct x. Qed.
Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B : Set} (P P' : A -> Prop) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  rewrite !H1 // !H2 //.
Qed.

Lemma case_brs_map_spec {A B : Set} {P : A -> Prop} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros. red in H.
  eapply forall_map_spec. eapply Forall_impl; eauto. simpl; intros.
  apply on_snd_eq_spec; eauto.
Qed.

Lemma tfix_map_spec {A B : Set} {P P' : A -> Prop} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply forall_map_spec. red in H. eapply Forall_impl; eauto. simpl.
  intros. destruct H2;
  eapply map_def_spec; eauto.
Qed.


Lemma map_def_test_spec {A B : Set}
      (P P' : A -> Prop) (p p' : pred A) (f f' g g' : A -> B) (x : def A) :
  P x.(dtype) -> P' x.(dbody) -> (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  test_def p p' x ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  unfold test_def in H3; simpl in H3. rewrite -> andb_and in H3. intuition.
  rewrite !H1 // !H2 //; intuition auto.
Qed.

Lemma case_brs_forallb_map_spec {A B : Set} {P : A -> Prop} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_snd p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros.
  eapply on_snd_test_spec; eauto.
Qed.

Lemma tfix_forallb_map_spec {A B : Set} {P P' : A -> Prop} {p p'} {l} {f f' g g' : A -> B} :
  tFixProp P P' l ->
  forallb (test_def p p') l ->
  (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros. destruct H3.
  eapply map_def_test_spec; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : Forall _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (forall_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : Forall _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (forall_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : Forall _ _ |- map _ _ = map _ _ =>
    eapply (forall_map_spec H)
  | H : Forall _ _ |- map _ _ = _ =>
    eapply (forall_map_id_spec H)
  | H : Forall _ _ |- is_true (forallb _ _) =>
    eapply (Forall_forallb _ _ _ H); clear H
  end.

(** Use a coercion for this common projection of the global context. *)
Definition fst_ctx : global_env_ext -> global_env := fst.
Coercion fst_ctx : global_env_ext >-> global_env.

Definition empty_ext (Σ : global_env) : global_env_ext
  := (Σ, Monomorphic_ctx ContextSet.empty).
