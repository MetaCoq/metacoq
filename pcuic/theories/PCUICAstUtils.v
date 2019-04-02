From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From Template Require Import utils.
From Template Require Import BasicAst.
From PCUIC Require Import PCUICAst.
Import List.ListNotations.
Require Import FunctionalExtensionality.
Require Import ssreflect.

Set Asymmetric Patterns.

Open Scope pcuic.

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
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity) : pcuic.

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

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Lemma decompose_app_rec_mkApps f l l' : decompose_app_rec (mkApps f l) l' =
                                    decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl ?app_nil_r; auto.
Qed.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. rewrite /decompose_app decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l in f, l' |- *; destruct l'; simpl; rewrite ?app_nil_r; auto.
  rewrite <- IHl. simpl. reflexivity.
Qed.

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

Fixpoint lookup_mind_decl (id : ident) (decls : global_declarations)
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
            | Some i0 => _
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
  | _ => (Γ, t)
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match t with
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
  let (f, l) := decompose_app t in
  match f with
  | tInd _ _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof.
  unfold is_ind_app_head.
  unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl; trivial.
Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; unfold is_ind_app_head; simpl; try (congruence || reflexivity).
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
  | Polymorphic_ctx c => fst (UContext.dest c)
  | Cumulative_ctx c => fst (UContext.dest (fst c))
  end.

Definition map_one_inductive_body mind u arities f n m :=
  match m with
  | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
    let '(ctx, _) := decompose_prod_assum [] (f 0 ind_type) in
    let indty := mkApps (tInd (mkInd mind n) u) (to_extended_list ctx) in
    Build_one_inductive_body ind_name
                             (f 0 ind_type)
                             ind_kelim
                             (map (on_pi2 (f arities)) ind_ctors)
                             (map (on_snd (f (S (length ctx)))) ind_projs)
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

Definition map_mutual_inductive_body mind f m :=
  match m with
  | Build_mutual_inductive_body ind_npars ind_pars ind_bodies ind_universes =>
    let arities := arities_context ind_bodies in
    let u := polymorphic_instance ind_universes in
    Build_mutual_inductive_body ind_npars (fold_context f ind_pars)
      (mapi (map_one_inductive_body mind u (length arities) f) ind_bodies)
      ind_universes
  end.

Lemma ind_type_map f arities mind u n oib :
  ind_type (map_one_inductive_body mind u arities f n oib) = f 0 (ind_type oib).
Proof. destruct oib. simpl. destruct decompose_prod_assum. reflexivity. Qed.

Lemma ind_ctors_map f arities mind u n oib :
  ind_ctors (map_one_inductive_body mind u arities f n oib) =
  map (on_pi2 (f arities)) (ind_ctors oib).
Proof. destruct oib; simpl; destruct decompose_prod_assum; reflexivity. Qed.

Lemma ind_pars_map mind f m :
  ind_params (map_mutual_inductive_body mind f m) =
  fold_context f (ind_params m).
Proof. destruct m; simpl; reflexivity. Qed.

Lemma ind_projs_map f mind u arities n oib :
  ind_projs (map_one_inductive_body mind u arities f n oib) =
  let '(ctx, _) := decompose_prod_assum [] (f 0 oib.(ind_type)) in
  map (on_snd (f (S (length ctx)))) (ind_projs oib).
Proof. destruct oib; simpl. destruct decompose_prod_assum. simpl. reflexivity. Qed.

Definition test_def {A : Set} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (nat * A)) :=
  All (fun x => P (snd x)) l.

Definition tFixProp {A : Set} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.


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

Lemma map_def_id {t : Set} : map_def (@id t) (@id t) = id.
Proof. extensionality p. now destruct p. Qed.
Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B : Set} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  rewrite !H // !H0 //.
Qed.

Lemma case_brs_map_spec {A B : Set} {P : A -> Type} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply on_snd_eq_spec; eauto.
Qed.

Lemma tfix_map_spec {A B : Set} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq. red in X. eapply All_impl; eauto. simpl.
  intros. destruct X0;
  eapply map_def_spec; eauto.
Qed.


Lemma map_def_test_spec {A B : Set}
      (P P' : A -> Type) (p p' : pred A) (f f' g g' : A -> B) (x : def A) :
  P x.(dtype) -> P' x.(dbody) -> (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  test_def p p' x ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  unfold test_def in H1; simpl in H1. rewrite -> andb_and in H1. intuition.
  rewrite !H // !H0 //; intuition auto.
Qed.

Lemma All_All2 {A} {P : A -> A -> Type} {Q} {l : list A} :
  All Q l ->
  (forall x, Q x -> P x x) ->
  All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_nth_error {A} {P : A -> A -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Qed.

Lemma All2_nth_error_Some {A} {P : A -> A -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l n = Some t ->
  { t' : A & (nth_error l' n = Some t') * P t t'}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_None {A} {P : A -> A -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_length {A} {P : A -> A -> Type} l l' : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma All_forallb_map_spec {A B : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Qed.

Lemma All_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x) -> forallb f l.
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.

Lemma on_snd_test_spec {A B C} (P : B -> Type) (p : B -> bool) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> p x -> f x = g x) ->
  test_snd p x ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H; auto.
Qed.

Lemma case_brs_forallb_map_spec {A B : Set} {P : A -> Type} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_snd p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply All_map_eq. red in X. apply forallb_All in H.
  merge_All. eapply All_impl; eauto. simpl. intros. intuition.
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
  eapply All_map_eq; red in X. apply forallb_All in H.
  merge_All. eapply All_impl; eauto. simpl; intros; intuition.
  eapply map_def_test_spec; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : All _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : All _ _ |- map _ _ = map _ _ =>
    eapply (All_map_eq H)
  | H : All _ _ |- map _ _ = _ =>
    eapply (All_map_id H)
  | H : All _ _ |- is_true (forallb _ _) =>
    eapply (All_forallb _ _ H); clear H
  end.

Ltac close_All :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : All _ _ |- All2 _ _ _ =>
    apply (All_All2 H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.
