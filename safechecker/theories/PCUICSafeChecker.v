(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils BasicAst AstUtils
     UnivSubst.
From MetaCoq.Template Require Pretty.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.
Open Scope type_scope.
Open Scope list_scope.
Local Set Keyed Unification.


(* todo: move this *)
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.

Lemma All_sq {A} {P : A -> Type} {l}
  : All (fun x => ∥ P x ∥) l -> ∥ All P l ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All2_sq {A B} {R : A -> B -> Type} {l1 l2}
  : All2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.


Lemma weakening_sq `{cf : checker_flags} {Σ Γ} Γ' {t T} :
  ∥ wf Σ.1 ∥ -> ∥ wf_local Σ (Γ ,,, Γ') ∥ ->
  ∥ Σ ;;; Γ |- t : T ∥ ->
  ∥ Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T ∥.
Proof.
  intros; sq; now eapply weakening.
Defined.

Definition wf_local_rel_abs_sq `{cf : checker_flags} {Σ Γ Γ' A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> {u & ∥ Σ ;;; Γ ,,, Γ' |- A : tSort u ∥ }
  -> ∥ wf_local_rel Σ Γ (Γ',, vass na A) ∥.
Proof.
  intros H [u Hu]; sq. now eapply wf_local_rel_abs.
Qed.

Definition wf_local_rel_def_sq `{cf : checker_flags} {Σ Γ Γ' t A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> ∥ isType Σ (Γ ,,, Γ') A ∥ -> ∥ Σ ;;; Γ ,,, Γ' |- t : A ∥
  -> ∥ wf_local_rel Σ Γ (Γ',, vdef na t A) ∥.
Proof.
  intros; sq. now eapply wf_local_rel_def.
Qed.

Definition wf_local_rel_app_inv_sq `{cf : checker_flags} {Σ Γ1 Γ2 Γ3} :
  ∥ wf_local_rel Σ Γ1 Γ2 ∥ -> ∥ wf_local_rel Σ (Γ1 ,,, Γ2) Γ3 ∥
  -> ∥ wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ∥.
Proof.
  intros; sq; now eapply wf_local_rel_app_inv.
Qed.

Fixpoint monad_All {T} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l)
  := match l with
     | [] => ret All_nil
     | a :: l => X <- f a ;;
                Y <- monad_All f l ;;
                ret (All_cons X Y)
     end.

Fixpoint monad_All2 {T E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
         {A B R} (f : forall x y, T (R x y)) l1 l2
  : T (@All2 A B R l1 l2)
  := match l1, l2 with
     | [], [] => ret (All2_nil R)
     | a :: l1, b :: l2 => X <- f a b ;;
                          Y <- monad_All2 wrong_sizes f l1 l2 ;;
                          ret (All2_cons R a b l1 l2 X Y)
     | _, _ => raise wrong_sizes
     end.


Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)
  := X <- x ;; Y <- y ;; ret (X, Y).

Definition check_dec {T E} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
           (H : {P} + {~ P})
  : T P
  := match H with
     | left x => ret x
     | right _ => raise e
     end.

Definition check_eq_true {T E} {M : Monad T} {M' : MonadExc E T} b (e : E)
  : T (b = true)
  := if b return T (b = true) then ret eq_refl else raise e.

Program Definition check_eq_nat {T E} {M : Monad T} {M' : MonadExc E T} n m (e : E)
  : T (n = m)
  := match Nat.eq_dec n m with
     | left p => ret p
     | right p => raise e
     end.


Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].


Derive EqDec for sort_family.
Next Obligation.
  unfold Classes.dec_eq. decide equality.
Defined.


Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : string)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotCumulSmaller (G : universes_graph) (Γ : context) (t u t' u' : term) (e : ConversionError)
| NotConvertible (G : universes_graph) (Γ : context) (t u : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Lemma lookup_env_id Σ id decl
  : lookup_env Σ id = Some decl -> id = global_decl_ident decl.
Proof.
  induction Σ; cbn. inversion 1.
  destruct (ident_eq_spec id (global_decl_ident a)).
  - inversion 1. now destruct H1.
  - easy.
Qed.



Local Open Scope string_scope.
Definition string_of_list_aux {A} (f : A -> string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ "," ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f l ++ "]".

Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lProp => "Prop"
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var " ++ string_of_nat n
  end.

Definition string_of_level_expr (l : Level.t * bool) : string :=
  let '(l, b) := l in
  string_of_level l ++ (if b then "+1" else "").

Definition string_of_sort (u : universe) :=
  string_of_list string_of_level_expr u.

Definition string_of_name (na : name) :=
  match na with
  | nAnon => "_"
  | nNamed n => n
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dtype def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Definition string_of_inductive (i : inductive) :=
  (inductive_mind i) ++ "," ++ string_of_nat (inductive_ind i).

Definition print_no_prop_level := string_of_level ∘ level_of_no_prop.

Definition print_edge '(l1, n, l2)
  := "(" ++ print_no_prop_level l1 ++ ", " ++ string_of_nat n ++ ", "
         ++ print_no_prop_level l2 ++ ")".

Definition print_universes_graph (G : universes_graph) :=
  let levels := wGraph.VSet.elements G.1.1 in
  let edges := wGraph.EdgeSet.elements G.1.2 in
  string_of_list print_no_prop_level levels
  ++ "\n" ++ string_of_list print_edge edges.

Definition string_of_conv_pb (c : conv_pb) : string :=
  match c with
  | Conv => "conversion"
  | Cumul => "cumulativity"
  end.
Definition string_of_context_decl (d : context_decl) :=
  match d.(decl_body) with
  | Some body =>
    string_of_name d.(decl_name)
      ++ " := " ++ string_of_term body
      ++ " : " ++ string_of_term d.(decl_type)
  | None =>
    string_of_name d.(decl_name)
      ++ " : " ++ string_of_term d.(decl_type)
  end.

Definition print_term Σ Γ t :=
  print_term Σ Γ true false t.

Fixpoint string_of_conv_error Σ (e : ConversionError) : string :=
  match e with
  | NotFoundConstants c1 c2 =>
      "Both constants " ++ c1 ++ " and " ++ c2 ++
      " are not found in the environment."
  | NotFoundConstant c =>
      "Constant " ++ c ++
      " common in both terms is not found in the environment."
  | LambdaNotConvertibleTypes Γ1 na A1 t1 Γ2 na' A2 t2 e =>
      "When comparing\n" ++ print_term Σ Γ1 (tLambda na A1 t1) ++
      "\nand\n" ++ print_term Σ Γ2 (tLambda na' A2 t2) ++
      "\ntypes are not convertible:\n" ++
      string_of_conv_error Σ e
  | ProdNotConvertibleDomains Γ1 na A1 B1 Γ2 na' A2 B2 e =>
      "When comparing\n" ++ print_term Σ Γ1 (tProd na A1 B1) ++
      "\nand\n" ++ print_term Σ Γ2 (tProd na' A2 B2) ++
      "\ndomains are not convertible:\n" ++
      string_of_conv_error Σ e
  | DistinctStuckCase Γ ind par p c brs Γ' ind' par' p' c' brs' =>
      "The two pattern-matching\n" ++
      print_term Σ Γ (tCase (ind, par) p c brs) ++
      "\nand\n" ++ print_term Σ Γ' (tCase (ind', par') p' c' brs') ++
      "\ncorrespond to syntactically distinct stuck terms."
  | DistinctStuckProj Γ p c Γ' p' c' =>
      "The two projections\n" ++
      print_term Σ Γ (tProj p c) ++
      "\nand\n" ++ print_term Σ Γ' (tProj p' c') ++
      "\ncorrespond to syntactically distinct stuck terms."
  | CannotUnfoldFix Γ mfix idx Γ' mfix' idx' =>
      "The two fixed-points\n" ++
      print_term Σ Γ (tFix mfix idx) ++
      "\nand\n" ++ print_term Σ Γ' (tFix mfix' idx') ++
      "\ncorrespond to syntactically distinct terms that can't be unfolded."
  | DistinctCoFix Γ mfix idx Γ' mfix' idx' =>
      "The two cofixed-points\n" ++
      print_term Σ Γ (tCoFix mfix idx) ++
      "\nand\n" ++ print_term Σ Γ' (tCoFix mfix' idx') ++
      "\ncorrespond to syntactically distinct terms."
  | StackHeadError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stackheaderror\n" ++
      string_of_conv_error Σ e
  | StackTailError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stacktailerror\n" ++
      string_of_conv_error Σ e
  | StackMismatch Γ1 t1 args1 l1 Γ2 t2 l2 =>
      "Convertible terms\n" ++
      print_term Σ Γ1 t1 ++
      "\nand\n" ++ print_term Σ Γ2 t2 ++
      "are convertible/convertible (TODO) but applied to a different number" ++
      " of arguments."
  | HeadMistmatch leq Γ1 t1 Γ2 t2 =>
      "Terms\n" ++
      print_term Σ Γ1 t1 ++
      "\nand\n" ++ print_term Σ Γ2 t2 ++
      "\ndo not have the same head when comparing for " ++
      string_of_conv_pb leq
  end.


Definition string_of_context (Γ : context) :=
  string_of_list string_of_context_decl Γ.

Definition string_of_type_error Σ (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unbound rel " ++ string_of_nat n
  | UnboundVar id => "Unbound var " ++ id
  | UnboundEvar ev => "Unbound evar " ++ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ++ c
  | UndeclaredInductive c => "Undeclared inductive " ++ (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ++ (inductive_mind c)
  | NotCumulSmaller G Γ t u t' u' e => "Terms are not <= for cumulativity:\n" ++
      print_term Σ Γ t ++ "\nand:\n" ++ print_term Σ Γ u ++
      "\nafter reduction:\n" ++
      print_term Σ Γ t' ++ "\nand:\n" ++ print_term Σ Γ u' ++
      "\nerror:\n" ++ string_of_conv_error Σ e ++
      "\nin universe graph:\n" ++ print_universes_graph G
  | NotConvertible G Γ t u => "Terms are not convertible:\n" ++
      print_term Σ Γ t ++ "\nand:\n" ++ print_term Σ Γ u ++
      "\nin universe graph:\n" ++ print_universes_graph G
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg: " ++ s
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.


Lemma wf_local_rel_inv `{checker_flags} {Σ Γ1 Γ2} (w : wf_local_rel Σ Γ1 Γ2) :
  forall d Γ2', Γ2 = Γ2' ,, d ->
  wf_local_rel Σ Γ1 Γ2' × (∑ u, Σ ;;; Γ1 ,,, Γ2' |- d.(decl_type) : tSort u) ×
               match d.(decl_body) with
               | Some b => Σ ;;; Γ1 ,,, Γ2' |- b : d.(decl_type)
               | None => True
               end.
Proof.
  intros d Γ.
  destruct w; inversion 1; subst; cbn in *.
  split; [assumption|]. split; [assumption| trivial].
  split; [assumption|]. split; [assumption| trivial].
Defined.

Definition strengthening_wf_local_rel `{cf : checker_flags} Σ Γ1 Γ2 Γ3 Γ4 :
  wf Σ.1 -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3 ,,, lift_context #|Γ3| 0 Γ4)
  -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ4).
Proof.
  intros HΣ H.
  eapply wf_local_rel_app in H; destruct H as [H1 H2].
  eapply wf_local_rel_app in H1; destruct H1 as [H1 H1'].
  eapply wf_local_rel_app_inv. assumption.
  revert H2. clear -HΣ. induction Γ4. intros; constructor.
  intro H. rewrite lift_context_snoc0 in H.
  destruct a as [na [b|] ty].
  - unfold lift_decl, map_decl in H; cbn in H.
    destruct (wf_local_rel_inv H _ _ eq_refl) as [H1 [H2 H3]]; cbn in *.
    rewrite Nat.add_0_r in *.
    rewrite app_context_assoc in *.
    econstructor.
    + easy.
    + cbn. exists H2.π1. eapply strengthening. assumption. exact H2.π2.
    + cbn. eapply strengthening; eassumption.
  - unfold lift_decl, map_decl in H; cbn in H.
    destruct (wf_local_rel_inv H _ _ eq_refl) as [H1 [[u H2] _]]; cbn in *.
    rewrite Nat.add_0_r in H2.
    rewrite app_context_assoc in H2.
    econstructor. easy.
    exists u. eapply strengthening; eassumption.
Qed.


Definition wf_local_app_inv `{cf : checker_flags} {Σ Γ1 Γ2} :
  wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
  -> wf_local Σ (Γ1 ,,, Γ2).
Proof.
  intros H1 H2.
  apply wf_local_local_rel, wf_local_rel_app_inv.
  now apply wf_local_rel_local.
  now rewrite app_context_nil_l.
Defined.

Definition fix_context_i i mfix :=
  List.rev (mapi_rec (fun i (d : BasicAst.def term)
                      => vass (dname d) ((lift0 i) (dtype d))) mfix i).

Lemma lift_fix_context mfix : forall k k' j, j <= k ->
    fix_context_i (k + k') mfix = lift_context k' j (fix_context_i k mfix).
Proof.
  induction mfix. reflexivity.
  intros k k' j Hj.
  change ([vass (dname a) ((lift0 (k + k')) (dtype a))] ,,, fix_context_i (S (k + k')) mfix = lift_context k' j ([vass (dname a) ((lift0 k) (dtype a))] ,,, fix_context_i (S k) mfix)).
  erewrite lift_context_app, (IHmfix (S k) k' (S j)); cbn.
  unfold map_decl, vass; cbn. now rewrite simpl_lift.
  now apply le_n_S.
Qed.


Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
Proof.
  pose proof (global_ext_uctx_consistent _ HΣ) as HC.
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
  eexists; reflexivity.
  contradiction HC.
Qed.

Lemma wf_ext_is_graph {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
Proof.
  destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Lemma map_squash {A B} (f : A -> B) : ∥ A ∥ -> ∥ B ∥.
Proof.
  intros []; constructor; auto.
Qed.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Definition isType_wellformed {Γ t}
    : isType Σ Γ t -> wellformed Σ Γ t.
  Proof.
    intros []. left; now econstructor.
  Qed.

  (* Definition typ_to_wf {Γ t} *)
  (*   : { A : term | ∥ Σ ;;; Γ |- t : A ∥ } -> wellformed Σ Γ t. *)
  (* Proof. *)
  (*   intros [A h]. sq. left. now exists A. *)
  (* Defined. *)

  Lemma validity_wf {Γ t T} :
    ∥ wf_local Σ Γ ∥ -> ∥ Σ ;;; Γ |- t : T ∥ -> wellformed Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [wΓ] [X].
    intros. eapply validity_term in X; try assumption.
    destruct X. now right.
    left; destruct i. now exists (tSort x).
  Defined.

  Lemma wat_wellformed {Γ T} :
    ∥ isWfArity_or_Type Σ Γ T ∥ -> wellformed Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [[X|X]].
    right; now constructor.
    now apply isType_wellformed.
  Defined.

  Definition hnf := reduce_term RedFlags.default Σ HΣ.

  Theorem hnf_sound {Γ t h} : ∥ red (fst Σ) Γ t (hnf Γ t h) ∥.
  Proof.
    apply reduce_term_sound.
  Defined.

  Program Definition reduce_to_sort Γ t (h : wellformed Σ Γ t)
    : typing_result (∑ u, ∥ red (fst Σ) Γ t (tSort u) ∥) :=
    match t with
    | tSort s => ret (s; sq (refl_red _ _ _))
    | _ =>
      match hnf Γ t h with
      | tSort s => ret (s; _)
      | _ => raise (NotASort t)
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in H0.
  Defined.

  Program Definition reduce_to_prod Γ t (h : wellformed Σ Γ t)
       : typing_result (∑ na a b, ∥ red (fst Σ) Γ t (tProd na a b) ∥) :=
    match t with
    | tProd na a b => ret (na; a; b; sq (refl_red _ _ _))
    | _ =>
      match hnf Γ t h with
      | tProd na a b => ret (na; a; b; _)
      | t' => raise (NotAProduct t t')
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in H0.
  Defined.

  Fixpoint stack_to_apps π : typing_result (list term) :=
    match π with
    | Empty => ret []
    | App t π => l <- stack_to_apps π ;; ret (t :: l)
    | _ => raise (Msg "not some applications")
    end.

  Lemma zip_stack_to_apps t π l :
    stack_to_apps π = Checked l -> zipc t π = mkApps t l.
  Proof.
    revert t l. induction π; cbn; try inversion 1.
    reflexivity.
    destruct (stack_to_apps π); inversion H1.
    erewrite IHπ; reflexivity.
  Qed.


  Program Definition reduce_to_ind Γ t (h : wellformed Σ Γ t)
    : typing_result (∑ i u l, ∥ red (fst Σ) Γ t (mkApps (tInd i u) l) ∥) :=
    match decompose_app t with
    | (tInd i u, l) => ret (i; u; l; sq _)
    | _ =>
      match reduce_stack RedFlags.default Σ HΣ Γ t Empty h with
      | (tInd i u, π) => match stack_to_apps π with
                        | Checked l => ret (i; u; l; _)
                        | TypeError e => raise e
                        end
      | _ => raise (NotAnInductive t)
      end
    end.
  Next Obligation.
    assert (X : mkApps (tInd i u) l = t); [|rewrite X; apply refl_red].
    etransitivity. 2: symmetry; eapply mkApps_decompose_app.
    pose proof (f_equal fst Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    pose proof (f_equal snd Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    reflexivity.
  Defined.
  Next Obligation.
    pose proof (reduce_stack_sound RedFlags.default Σ HΣ _ _ Empty h).
    rewrite <- Heq_anonymous1 in H0.
    now erewrite <- zip_stack_to_apps.
  Defined.


  Definition iscumul Γ := isconv_term RedFlags.default Σ HΣ Hφ G HG Γ Cumul.

  Program Definition convert_leq Γ t u
          (ht : wellformed Σ Γ t) (hu : wellformed Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
    match leqb_term G t u with true => ret _ | false =>
    match iscumul Γ t ht u hu with
    | Success _ => ret _
    | Error e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller G Γ t u t' u' e)
      (* end *)
    end end.
  Next Obligation.
    symmetry in Heq_anonymous; eapply leqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  Section InferAux.
    Variable (infer : forall Γ (HΓ : ∥ wf_local Σ Γ ∥) (t : term),
                 typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

    Program Definition infer_type Γ HΓ t
      : typing_result ({u : universe & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      destruct HΣ, HΓ, X, X0.
      now constructor; eapply type_reduction.
    Defined.

    Program Definition infer_cumul Γ HΓ t A (hA : ∥ isWfArity_or_Type Σ Γ A ∥)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.π1 A _ _ ;;
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation. destruct hA; now apply wat_wellformed. Qed.
    Next Obligation.
      destruct HΣ, HΓ, hA, X, X0. constructor. econstructor; eassumption.
    Qed.
  End InferAux.


  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl _ decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption.
      erewrite (lookup_env_id _ _ _ Heq_anonymous0); reflexivity.
    - now symmetry.
  Defined.

  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
  Proof.
    pose proof HΣ'.
    intros HH.
    refine (check_constraints_spec G (global_ext_uctx Σ) _ _ HG _ HH).
    now apply wf_ext_global_uctx_invariants.
    now apply global_ext_uctx_consistent.
  Qed.

  Lemma is_graph_of_uctx_levels l :
    wGraph.VSet.mem l (uGraph.wGraph.V G) ->
    LevelSet.mem l (global_ext_levels Σ).
  Proof.
    unfold is_graph_of_uctx in HG.
    case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
      rewrite XX in *; simpl in *; [|contradiction].
    unfold gc_of_uctx in XX; simpl in XX.
    destruct (gc_of_constraints Σ); [|discriminate].
    inversion XX; subst. generalize (global_ext_levels Σ); intros lvs; cbn.
    clear. intro H. apply LevelSet.mem_spec. apply wGraph.VSet.mem_spec in H.
    apply LevelSetProp.FM.elements_2.
    unfold no_prop_levels in H.
    rewrite LevelSet.fold_spec in H.
    cut (SetoidList.InA eq (level_of_no_prop l) (LevelSet.elements lvs)
         \/ wGraph.VSet.In l wGraph.VSet.empty). {
      intros [|H0]; [trivial|].
      now apply wGraph.VSet.empty_spec in H0. }
    revert H. generalize (LevelSet.elements lvs), wGraph.VSet.empty; clear.
    intros lvs; induction lvs; cbn; [intuition|].
    intros S H. apply IHlvs in H. destruct H as [H|H].
    - left. now constructor 2.
    - destruct a; cbn in *. now right.
      all: apply wGraph.VSet.add_spec in H; destruct H as [H|H]; [left|now right].
      all: rewrite H; now constructor.
  Qed.


  Program Definition check_consistent_instance uctx u
    : typing_result (consistent_instance_ext Σ uctx u)
    := match uctx with
       | Monomorphic_ctx _ =>
         check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0")
       | Polymorphic_ctx (inst, cstrs)
       | Cumulative_ctx ((inst, cstrs), _) =>
         let '(inst, cstrs) := AUContext.repr (inst, cstrs) in
         check_eq_true (forallb (fun l => match no_prop_of_level l with
                                       | Some l => wGraph.VSet.mem l (uGraph.wGraph.V G)
                                       | None => false
                                       end) u)
                       (Msg "instance does not have the right length") ;;
         (* check_eq_true (forallb (fun l => LevelSet.mem l lvs) u) ;; *)
         X <- check_eq_nat #|u| #|inst|
                          (Msg "instance does not have the right length");;
         match check_constraints G (subst_instance_cstrs u cstrs) with
         | true => ret (conj _ _)
         | false => raise (Msg "ctrs not satisfiable")
         end
         (* #|u| = #|inst| /\ valid_constraints φ (subst_instance_cstrs u cstrs) *)
       end.
  Next Obligation.
    eapply forallb_All in H. eapply All_forallb'; tea.
    clear. intros []; cbnr; trivial.
  Qed.
  Next Obligation.
    repeat split.
    - eapply forallb_All in H. eapply All_forallb'; tea.
      intros []; simpl. discriminate.
      all: apply is_graph_of_uctx_levels.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.
  Next Obligation.
    eapply forallb_All in H. eapply All_forallb'; tea.
    clear. intros []; cbnr; trivial.
  Qed.
  Next Obligation.
    repeat split.
    - eapply forallb_All in H. eapply All_forallb'; tea.
      intros []; simpl. discriminate.
      all: apply is_graph_of_uctx_levels.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.

  Definition map2_option {A} (R : A -> A -> bool) : option A -> option A -> bool :=
    fun t u => match t, u with
            | Some t, Some u => R t u
            | None, None => true
            | _, _ => false
            end.

  Definition eqb_opt_term := map2_option (eqb_term G).

  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn.
    apply eqb_term_spec; tea. trivial.
  Qed.

  Definition map2_decl (R : term -> term -> bool) : context_decl -> context_decl -> bool :=
    fun d d' => map2_option R d.(decl_body) d'.(decl_body)
             && R d.(decl_type) d'.(decl_type).

  Definition eqb_decl := map2_decl (eqb_term G).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. unfold map2_decl in H. utils.toProp. apply eqb_opt_term_spec in H.
    eapply eqb_term_spec in H0; tea. now split.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

  Definition isconv Γ := isconv_term RedFlags.default Σ HΣ Hφ G HG Γ Conv.

  Fixpoint bcontext_relation
           (P : context -> context -> context_decl -> context_decl -> bool)
           (Γ Γ' : context) : bool :=
    match Γ, Γ' with
    | [], [] => true
    | {| decl_name := na ; decl_body := None; decl_type := T |} :: Γ,
      {| decl_name := na'; decl_body := None; decl_type := U |} :: Γ' =>
      P Γ Γ' (vass na T) (vass na' U) &&  bcontext_relation P Γ Γ'
    | {| decl_name := na ; decl_body := Some t; decl_type := T |} :: Γ,
      {| decl_name := na'; decl_body := Some u; decl_type := U |} :: Γ' =>
      P Γ Γ' (vdef na t T) (vdef na' u U) &&  bcontext_relation P Γ Γ'
    | _, _ => false
    end.

  Require Import PCUICContextConversion.

  Lemma reflect_context_relation P p
        (HP : forall Γ Γ' d d', reflect (P Γ Γ' d d') (p Γ Γ' d d')) Γ Γ'
    : reflectT (context_relation P Γ Γ') (bcontext_relation p Γ Γ').
  Proof.
    induction Γ as [|d Γ] in Γ' |- *.
    - destruct Γ'; repeat constructor. inversion 1.
    - destruct Γ' as [|[na' [bd'|] ty'] Γ'], d as [na [bd|] ty]; simpl.
      all: try (constructor; inversion 1).
      + destruct (HP Γ Γ' (vdef na bd ty) (vdef na' bd' ty')); cbn.
        * destruct (IHΓ Γ'); constructor. now constructor.
          now inversion 1.
        * constructor. now inversion 1.
      + destruct (HP Γ Γ' (vass na ty) (vass na' ty')); cbn.
        * destruct (IHΓ Γ'); constructor. now constructor.
          now inversion 1.
        * constructor. now inversion 1.
  Qed.

  (* Equations bconv_context (Γ Γ' : context) *)
  (*   : typing_result (∥ conv_context Σ Γ Γ' ∥) := *)
  (*   bconv_context [] [] := ret _ ; *)
  (*   bconv_context ({| decl_name := na ; decl_body := None; decl_type := T |} :: Γ ) *)
  (*                 ({| decl_name := na'; decl_body := None; decl_type := U |} :: Γ') *)
  (*     := match isconv Γ T _ U _ with *)
  (*        | true => bconv_context Γ Γ' ;; ret _ *)
  (*        | false => raise (Msg "not conv in conv_ctx") *)
  (*        end; *)
  (*   bconv_context _ _ := raise (Msg "not same length in conv_ctx"). *)
  (* Next Obligation. *)
  (*   repeat constructor. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Abort. *)


  Definition isconv0 Γ t1 t2 : bool
    := if isconv_term RedFlags.default Σ HΣ Hφ G HG Γ Conv
                   t1 (todo "ee") t2 (todo "rr")
      then true else false.

  Definition bconv_decl Γ := map2_decl (isconv0 Γ).

  Definition bconv_context Γ := bcontext_relation (fun Δ _ => bconv_decl (Γ ,,, Δ)).

  Definition check_correct_arity Γ decl ind u ctx pars pctx :=
    let inddecl :=
        {| decl_name := nNamed decl.(ind_name);
           decl_body := None;
           decl_type := mkApps (tInd ind u) (map (lift0 #|ctx|) pars ++ to_extended_list ctx) |}
    in bconv_context Γ (inddecl :: ctx) pctx.

  Lemma check_correct_arity_spec Γ decl ind u ctx pars pctx
    : check_correct_arity Γ decl ind u ctx pars pctx
      -> PCUICTyping.check_correct_arity (global_ext_constraints Σ) decl ind u ctx pars pctx.
  Proof.
  (*   apply eqb_context_spec. *)
  (* Qed. *)
  Admitted.

  Ltac sq :=
    repeat match goal with
           | H : ∥ _ ∥ |- _ => case H; clear H; intro H
           end; try eapply sq.

  Open Scope nat.

  Program Fixpoint infer (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) {struct t}
    : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }) :=
    match t with
    | tRel n =>
          match nth_error Γ n with
          | Some c => ret ((lift0 (S n)) (decl_type c); _)
          | None   => raise (UnboundRel n)
          end

    | tVar n  => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort u =>
          match u with
          | NEL.sing (l, false) =>
            check_eq_true (LevelSet.mem l (global_ext_levels Σ)) (Msg ("undeclared level " ++ string_of_level l));;
            ret (tSort (Universe.super l); _)
          | _ => raise (Msg (string_of_sort u ++ " is not a level"))
          end

    | tProd na A B =>
          s1 <- infer_type infer Γ HΓ A ;;
          s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
          ret (tSort (Universe.sort_of_product s1.π1 s2.π1); _)

    | tLambda na A t =>
          s1 <- infer_type infer Γ HΓ A ;;
          B <- infer (Γ ,, vass na A) _ t ;;
          ret (tProd na A B.π1; _)

    | tLetIn n b b_ty b' =>
          infer_type infer Γ HΓ b_ty ;;
          infer_cumul infer Γ HΓ b b_ty _ ;;
          b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
          ret (tLetIn n b b_ty b'_ty.π1; _)

    | tApp t u =>
          ty <- infer Γ HΓ t ;;
          pi <- reduce_to_prod Γ ty.π1 _ ;;
          infer_cumul infer Γ HΓ u pi.π2.π1 _ ;;
          ret (subst10 u pi.π2.π2.π1; _)

    | tConst cst u =>
          match lookup_env (fst Σ) cst with
          | Some (ConstantDecl _ d) =>
            check_consistent_instance d.(cst_universes) u ;;
            let ty := subst_instance_constr u d.(cst_type) in
            ret (ty; _)
          |  _ => raise (UndeclaredConstant cst)
          end

    | tInd ind u =>
          d <- lookup_ind_decl ind ;;
          check_consistent_instance d.π1.(ind_universes) u ;;
          let ty := subst_instance_constr u d.π2.π1.(ind_type) in
          ret (ty; _)

    | tConstruct ind k u =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_ctors) k with
          | Some cdecl =>
            check_consistent_instance d.π1.(ind_universes) u ;;
            ret (type_of_constructor d.π1 cdecl (ind, k) u; _)
          | None => raise (UndeclaredConstructor ind k)
          end

    | tCase (ind, par) p c brs =>
      cty <- infer Γ HΓ c ;;
      I <- reduce_to_ind Γ cty.π1 _ ;;
      let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ind ind')
                    (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      pty <- infer Γ HΓ p ;;
      match types_of_case ind decl body (firstn par args) u p pty.π1 with
      | None => raise (Msg "not the type of a case")
      | Some (indctx, pctx, ps, btys) =>
        check_eq_true
          (check_correct_arity Γ body ind u indctx (firstn par args) pctx)
          (let inddecl := {|
                 decl_name := nNamed (ind_name body);
                 decl_body := None;
                 decl_type := mkApps (tInd ind u)
                                     (map (lift0 #|indctx|) (firstn par args)
                                          ++ to_extended_list indctx) |} in
           Msg ("not correct arity. indctx:\n"
                                 ++ string_of_context (inddecl :: indctx)
                                 ++ "\npctx:\n" ++ string_of_context pctx)) ;;
        check_eq_true
          (existsb (leb_sort_family (universe_family ps)) (ind_kelim body))
          (Msg "cannot eliminate over this sort") ;;
        (fix check_branches (brs btys : list (nat * term))
          (HH : Forall (squash ∘ (isType Σ Γ) ∘ snd) btys) {struct brs}
            : typing_result
              (All2 (fun x y => fst x = fst y /\ ∥ Σ ;;; Γ |- snd x : snd y ∥) brs btys)
                    := match brs, btys with
                       | [], [] => ret (All2_nil _)
                       | (n, t) :: brs , (m, A) :: btys =>
                         W <- check_dec (Msg "not nat eq")
                                       (EqDecInstances.nat_eqdec n m) ;;
                         Z <- infer_cumul infer Γ HΓ t A _ ;;
                         X <- check_branches brs btys _ ;;
                         ret (All2_cons _ _ _ _ _ (conj _ _) X)
                       | [], _ :: _
                       | _ :: _, [] => raise (Msg "wrong number of branches")
                       end) brs btys _ ;;
          ret (mkApps p (List.skipn par args ++ [c]); _)
      end

    | tProj (ind, n, k) c =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_projs) k with
          | Some pdecl =>
            c_ty <- infer Γ HΓ c ;;
            I <- reduce_to_ind Γ c_ty.π1 _ ;;
            let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
            check_eq_true (eqb ind ind')
                          (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
            check_eq_true (ind_npars d.π1 =? n)
                          (Msg "not the right number of parameters") ;;
            check_eq_true (#|args| =? ind_npars d.π1) (* probably redundant *)
                          (Msg "not the right number of parameters") ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev args) (subst_instance_constr u ty);
                   _)
          | None => raise (Msg "projection not found")
          end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix}
              : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥)
              := match mfix with
                 | [] => ret (sq wf_local_rel_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening_sq acc _ _ W.π2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (wf_local_rel_abs_sq Hacc (W.π1; W')) ;;
                   ret (wf_local_rel_app_inv_sq
                          (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)
                 end)
           mfix [] (sq wf_local_rel_nil);;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
                  (XX' : ∥ wf_local_rel Σ Γ (fix_context mfix') ∥) {struct mfix'}
 : typing_result (All (fun d =>
 ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥
   /\ isLambda (dbody d) = true) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   W2 <- check_eq_true (isLambda (dbody def))
                                      (Msg "not a lambda") ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons (conj W1 W2) Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (fix_guard mfix) (Msg "Unguarded fixpoint") ;;
        ret (dtype decl; _)
      end


    | tCoFix mfix n =>
      (* to add when generalizing to all flags *)
      allowcofix <- check_eq_true allow_cofix (Msg "cofix not allowed") ;;
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix}
              : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥)
              := match mfix with
                 | [] => ret (sq wf_local_rel_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening_sq acc _ _ W.π2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (wf_local_rel_abs_sq Hacc (W.π1; W')) ;;
                   ret (wf_local_rel_app_inv_sq
                          (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)
                 end)
           mfix [] (sq wf_local_rel_nil);;
        YY <- (fix check_bodies (mfix' : mfixpoint term) (XX' : ∥ wf_local_rel Σ Γ (fix_context mfix') ∥) {struct mfix'}
 : typing_result (All (fun d =>
 ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥
   ) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        ret (dtype decl; _)
      end
    end.

  Next Obligation. sq; now econstructor. Defined.
  Next Obligation. sq; econstructor; tas.
                   now apply LevelSetFact.mem_2. Defined.
  (* tProd *)
  Next Obligation. sq; econstructor; cbn; easy. Defined.
  Next Obligation. sq; econstructor; eassumption. Defined.
  (* tLambda *)
  Next Obligation. sq; econstructor; cbn; easy. Defined.
  Next Obligation. sq; econstructor; eassumption. Defined.
  (* tLetIn *)
  Next Obligation. sq. right. econstructor; eauto. Defined.
  Next Obligation. sq; econstructor; cbn; eauto. Defined.
  Next Obligation. sq; now econstructor. Defined.

  (* tApp *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation.
    sq. eapply type_reduction in X1 ; try eassumption.
    eapply validity_term in X1 ; try assumption. destruct X1.
    - destruct i as [ctx [s [H1 H2]]]. cbn in H1.
      apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]] ; subst.
      rewrite app_context_assoc in H2. cbn in H2.
      apply wf_local_app in H2.
      inversion H2; subst. right. assumption.
    - destruct i as [s HH].
      eapply inversion_Prod in HH ; try assumption.
      destruct HH as [s1 [_ [HH _]]].
      right. eexists. eassumption.
  Defined.
  Next Obligation.
    sq; econstructor. 2: eassumption.
    eapply type_reduction; eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    sq; constructor; try assumption.
    symmetry in Heq_anonymous.
    etransitivity. eassumption.
    now rewrite (lookup_env_id _ _ _ Heq_anonymous).
  Defined.

  (* tInd *)
  Next Obligation. sq; econstructor; eassumption. Defined.

  (* tConstruct *)
  Next Obligation. sq; econstructor; try eassumption. now split. Defined.

  (* tCase *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. inversion HH; sq; right; assumption. Qed.
  Next Obligation. inversion HH; assumption. Qed.
  Next Obligation.
    destruct HΣ, HΓ, X.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate].
    rename Heq_anonymous into HH. symmetry in HH.
    eapply (type_Case_valid_btys Σ Γ) in HH; tea.
    eapply All_Forall, All_impl; tea. clear.
    intros x X; constructor; now exists ps.
  Defined.
  Next Obligation.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    assert (∥ All2 (fun x y  => ((fst x = fst y) *
                              (Σ;;; Γ |- snd x : snd y))%type) brs btys ∥). {
      eapply All2_sq. eapply All2_impl. eassumption.
      cbn; intros ? ? []. now sq. }
    destruct HΣ, HΓ, X9, X8, X5, X, H.
    constructor. eapply type_Case'; tea.
    - apply beq_nat_true; assumption.
    - symmetry; eassumption.
    - eapply check_correct_arity_spec; eassumption.
    - eapply type_reduction; eassumption.
  Defined.

  (* tProj *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation.
    sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - now apply beq_nat_true.
  Defined.

  (* tFix *)
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation.
    sq. cbn in *.
    apply wf_local_rel_app, fst in XX'. rewrite lift0_p in XX'.
    inversion XX'; subst. destruct X0 as [s HH].
    right. exists s.
    change (PCUICTerm.tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    apply wf_local_app_inv; assumption.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    change (wf_local_rel Σ Γ ([vass (dname def) ((lift0 0) (dtype def))] ,,, fix_context_i 1 mfix')) in XX'.
    rewrite lift0_p in XX'.
    pose proof (lift_fix_context mfix' 0 1 0) as e; cbn in e;
      rewrite e in XX' by reflexivity; clear e.
    pose proof (strengthening_wf_local_rel Σ Γ [] [vass (dname def) (dtype def)] (fix_context mfix')) as Y.
    now rewrite !app_context_nil_l in Y.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) * (isLambda (dbody d) = true))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      cbn; intros ? []. sq; now constructor. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
    now eapply All_local_env_app_inv.
  Qed.

  (* tCoFix *)
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation.
    sq. cbn in *.
    apply wf_local_rel_app, fst in XX'. rewrite lift0_p in XX'.
    inversion XX'; subst. destruct X0 as [s HH].
    right. exists s. change (PCUICTerm.tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    apply wf_local_app_inv; assumption.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    change (wf_local_rel Σ Γ ([vass (dname def) ((lift0 0) (dtype def))] ,,, fix_context_i 1 mfix')) in XX'.
    rewrite lift0_p in XX'.
    pose proof (lift_fix_context mfix' 0 1 0) as e; cbn in e;
      rewrite e in XX' by reflexivity; clear e.
    pose proof (strengthening_wf_local_rel Σ Γ [] [vass (dname def) (dtype def)] (fix_context mfix')) as Y.
    now rewrite !app_context_nil_l in Y.
  Defined.
  Next Obligation.
    apply All_sq in YY.
    sq. econstructor; eauto.
    now eapply All_local_env_app_inv.
  Defined.


  Lemma sq_wfl_nil : ∥ wf_local Σ [] ∥.
  Proof.
   repeat constructor.
  Qed.

  Program Fixpoint check_context Γ : typing_result (∥ wf_local Σ Γ ∥)
    := match Γ with
       | [] => ret sq_wfl_nil
       | {| decl_body := None; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type infer Γ HΓ A ;;
         ret _
       | {| decl_body := Some t; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type infer Γ HΓ A ;;
         XX <- infer_cumul infer Γ HΓ t A _ ;;
         ret _
       end.
  Next Obligation.
    sq. econstructor; tas. econstructor; eauto.
  Qed.
  Next Obligation.
    sq. right. econstructor; tea.
  Qed.
  Next Obligation.
    sq. econstructor; tas. econstructor; eauto.
  Qed.


  Program Definition check_isWfArity Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isWfArity typing Σ Γ A ∥) :=
    match destArity [] A with
    | None => raise (Msg (print_term Σ Γ A ++ " is not an arity"))
    | Some (ctx, s) => XX <- check_context (Γ ,,, ctx) ;;
                      ret _
    end.
  Next Obligation.
    destruct XX. constructor. exists ctx, s.
    split; auto.
  Defined.

  Program Definition check_isType Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isType Σ Γ A ∥) :=
    s <- infer Γ HΓ A ;;
    s' <- reduce_to_sort Γ s.π1 _ ;;
    ret _.
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. sq. eexists. eapply type_reduction; tea. Defined.


  Lemma isType_isWAT_sq {Γ A} : ∥ isType Σ Γ A ∥ -> ∥ isWfArity_or_Type Σ Γ A ∥.
  Proof.
    intro; sq; now right.
  Qed.

  Equations check_isWAT Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isWfArity_or_Type Σ Γ A ∥) :=
    check_isWAT Γ HΓ (tSort s) := ret _;
    check_isWAT Γ HΓ (tProd na A B) :=
      XX <- infer_type infer Γ HΓ A ;;
      YY <- check_isWAT (Γ ,, vass na A) _ B ;;
      ret _;
    check_isWAT Γ HΓ (tLetIn na t A B) :=
      XX <- infer_type infer Γ HΓ A ;;
      YY <- infer_cumul infer Γ HΓ t A _ ;;
      ZZ <- check_isWAT (Γ ,, vdef na t A) _ B ;;
      ret _;
    check_isWAT Γ HΓ A :=  XX <- check_isType Γ HΓ A ;; ret (isType_isWAT_sq XX).
  Next Obligation.
    sq. left. eexists. eexists. now split.
  Qed.
  Next Obligation.
    sq. constructor; cbn; eauto.
  Qed.
  Next Obligation.
    sq. eapply isWAT_tProd; tas. split; tas. econstructor; tea.
  Qed.
  Next Obligation.
    sq. right. eexists; eassumption.
  Qed.
  Next Obligation.
    sq. constructor; tas. eexists; eassumption.
  Qed.
  Next Obligation.
    sq. eapply isWAT_tLetIn; tas. repeat split; tas. econstructor; tea.
  Defined.


  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isWAT Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _.

End Typecheck.


Definition infer' {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := infer (map_squash fst HΣ) (map_squash snd HΣ).

Definition make_graph_and_infer {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := let '(G; HG) := wf_ext_is_graph HΣ in infer' HΣ G HG.


Print Assumptions infer.
(* Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString. *)
(* Extraction infer. *)


From MetaCoq.Checker Require kernel.Checker.
From MetaCoq.Checker Require Import wGraph.

Section CheckEnv.
  Context  {cf:checker_flags}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (e : env_error).
  Global Arguments EnvError {A} e.
  Global Arguments CorrectDecl {A} a.

  Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError e => EnvError e
         end
    |}.

  Instance envcheck_monad_exc : MonadExc env_error EnvCheck :=
    { raise A e := EnvError e;
      catch A m f :=
        match m with
        | CorrectDecl a => m
        | EnvError t => f t
        end
    }.

  Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | Checked a => CorrectDecl a
    | TypeError e => EnvError (IllFormedDecl id e)
    end.

  Definition check_wf_type id Σ HΣ HΣ' G HG t
    : EnvCheck (∑ u, ∥ Σ;;; [] |- t : tSort u ∥)
    := wrap_error id (@infer_type _ Σ HΣ (@infer _ Σ HΣ HΣ' G HG) [] sq_wfl_nil t).

  Definition check_wf_judgement id Σ HΣ HΣ' G HG t ty
    : EnvCheck (∥ Σ;;; [] |- t : ty ∥)
    := wrap_error id (@check _ Σ HΣ HΣ' G HG [] sq_wfl_nil t ty).

  Definition infer_term Σ HΣ HΣ' G HG t :=
    wrap_error "toplevel term" (@infer _ Σ HΣ HΣ' G HG [] sq_wfl_nil t).

  Program Fixpoint check_fresh id env : EnvCheck (∥ fresh_global id env ∥) :=
    match env with
    | [] => ret (sq (Forall_nil _))
    | g :: env =>
      p <- check_fresh id env;;
      match eq_constant id (global_decl_ident g) with
      | true => EnvError (AlreadyDeclared id)
      | false => ret _
      end
    end.
  Next Obligation.
    sq. constructor; tas.
    change (false = eqb id (global_decl_ident g)) in Heq_anonymous.
    destruct (eqb_spec id (global_decl_ident g)); [discriminate|].
    easy.
  Defined.

  Definition add_uctx (uctx : wGraph.VSet.t × GoodConstraintSet.t)
             (G : universes_graph) : universes_graph
    := let levels := wGraph.VSet.union uctx.1 G.1.1 in
       let edges := wGraph.VSet.fold
                      (fun l E =>
                         match l with
                         | lSet => E
                         | vtn ll => wGraph.EdgeSet.add (edge_of_level ll) E
                         end)
                      uctx.1 G.1.2 in
       let edges := GoodConstraintSet.fold
                      (fun ctr => wGraph.EdgeSet.add (edge_of_constraint ctr))
                      uctx.2 edges in
       (levels, edges, G.2).


  Definition Build_on_inductive_sq {Σ ind mdecl}
    : ∥ Alli (on_ind_body (lift_typing typing) Σ ind mdecl) 0 (ind_bodies mdecl) ∥ ->
      ∥ wf_local Σ (ind_params mdecl) ∥ ->
      context_assumptions (ind_params mdecl) = ind_npars mdecl ->
      ind_guard mdecl -> ∥ on_inductive (lift_typing typing) Σ ind mdecl ∥.
  Proof.
    intros H H0 H1 H2. sq. econstructor; eassumption.
  Defined.

  Program Fixpoint monad_Alli {T} {M : Monad T} {A} {P} (f : forall n x, T (∥ P n x ∥)) l n
    : T (∥ @Alli A P n l ∥)
    := match l with
       | [] => ret (sq (Alli_nil _ _))
       | a :: l => X <- f n a ;;
                    Y <- monad_Alli f l (S n) ;;
                    ret _
       end.
  Next Obligation.
    sq. constructor; assumption.
  Defined.


  (* Definition Build_on_ind_body Σ mind mdecl i idecl ind_indices ind_sort *)
  (*   : ind_type idecl = *)
  (*     it_mkProd_or_LetIn (ind_params mdecl) *)
  (*                        (it_mkProd_or_LetIn ind_indices (tSort ind_sort)) -> *)
  (*     ∥ on_type (lift_typing typing) Σ [] (ind_type idecl) ∥ -> *)
  (*     forall onConstructors : on_constructors P Σ mind mdecl i idecl (ind_ctors idecl), *)
  (*       (ind_projs idecl <> [] -> *)
  (*        on_projections P Σ mind mdecl i idecl ind_indices (ind_projs idecl)) -> *)
  (*       check_ind_sorts P onConstructors ind_sort -> on_ind_body P Σ mind mdecl i idecl *)


  Lemma check_one_ind_body:
    forall Σ : global_env_ext,
      ∥ wf Σ ∥ ->
      ∥ on_udecl Σ.1 Σ.2 ∥ ->
      forall G : universes_graph,
        is_graph_of_uctx G (global_ext_uctx Σ) ->
        forall (id : kername) (mdecl : mutual_inductive_body)
          (n : nat) (x : one_inductive_body),
          EnvCheck (∥ on_ind_body (lift_typing typing) Σ id mdecl n x ∥).
  Proof.
    intros Σ HΣ HΣ'0 G HG id mdecl n [].
  Admitted.


  Program Definition check_wf_decl (Σ : global_env_ext) HΣ HΣ' G HG
             (d : global_decl)
    : EnvCheck (∥ on_global_decl (lift_typing typing) Σ d ∥) :=
    match d with
    | ConstantDecl id cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement id Σ HΣ HΣ' G HG term cst.(cst_type) ;; ret _
      | None => check_wf_type id Σ HΣ HΣ' G HG cst.(cst_type) ;; ret _
      end
    | InductiveDecl id mdecl =>
      X1 <- monad_Alli (check_one_ind_body Σ HΣ HΣ' G HG id mdecl) _ _ ;;
      X2 <- wrap_error id (check_context HΣ HΣ' G HG (ind_params mdecl)) ;;
      X3 <- wrap_error id (check_eq_nat (context_assumptions (ind_params mdecl))
                                       (ind_npars mdecl)
                                       (Msg "wrong number of parameters")) ;;
      X4 <- wrap_error id (check_eq_true (ind_guard mdecl) (Msg "guard"));;
      ret (Build_on_inductive_sq X1 X2 X3 X4)
    end.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous; tas.
  Qed.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous.
    eexists. eassumption.
  Qed.


  Definition uctx_of_udecl u : ContextSet.t :=
    (levels_of_udecl u, constraints_of_udecl u).

  Lemma add_uctx_make_graph levels1 levels2 ctrs1 ctrs2
  : add_uctx (levels1, ctrs1) (make_graph (levels2, ctrs2))
    = make_graph (wGraph.VSet.union levels1 levels2,
                  GoodConstraintSet.union ctrs1 ctrs2).
  Admitted.

  Lemma gc_of_constraints_union S S'
    : gc_of_constraints (ConstraintSet.union S S') =
      (S1 <- gc_of_constraints S ;;
       S2 <- gc_of_constraints S' ;;
       ret (GoodConstraintSet.union S1 S2)).
  Admitted.

  Lemma no_prop_levels_union S S'
    : no_prop_levels (LevelSet.union S S')
      = wGraph.VSet.union (no_prop_levels S) (no_prop_levels S').
  Admitted.

  (* rely on proof irrelevance *)
  Axiom graph_eq : forall (G G' : universes_graph),
      wGraph.VSet.Equal G.1.1 G'.1.1
      -> wGraph.EdgeSet.Equal G.1.2 G'.1.2
      -> G.2 = G'.2
      -> G = G'.


  Program Definition check_udecl id (Σ : global_env) (HΣ : ∥ wf Σ ∥) G
          (HG : is_graph_of_uctx G (global_uctx Σ)) (udecl : universes_decl)
    : EnvCheck (∑ uctx', gc_of_uctx (uctx_of_udecl udecl) = Some uctx' /\
                         ∥ on_udecl Σ udecl ∥) :=
    let levels := levels_of_udecl udecl in
    let global_levels := global_levels Σ in
    let all_levels := LevelSet.union levels global_levels in
    check_eq_true (LevelSet.for_all (fun l => negb (LevelSet.mem l global_levels))
                                    levels) (IllFormedDecl id (Msg ("non fresh level in " ++ Pretty.print_lset levels)));;
    check_eq_true (ConstraintSet.for_all (fun '(l1, _, l2) => LevelSet.mem l1 all_levels && LevelSet.mem l2 all_levels) (constraints_of_udecl udecl))
                                    (IllFormedDecl id (Msg ("non declared level in " ++ Pretty.print_lset levels ++
                                    " |= " ++ Pretty.print_constraint_set (constraints_of_udecl udecl))));;
    check_eq_true match udecl with
                  | Monomorphic_ctx ctx
                    => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                  | _ => true
                  end (IllFormedDecl id (Msg "Var level in monomorphic context")) ;;
    (* TODO: could be optimized by reusing G *)
    match gc_of_uctx (uctx_of_udecl udecl) as X' return (X' = _ -> EnvCheck _) with
    | None => fun _ =>
      raise (IllFormedDecl id (Msg "constraints trivially not satisfiable"))
    | Some uctx' => fun Huctx =>
      check_eq_true (wGraph.is_acyclic (add_uctx uctx' G))
                    (IllFormedDecl id (Msg "constraints not satisfiable"));;
                                 ret (uctx'; (conj _ _))
    end eq_refl.
  Next Obligation.
    assert (HH: ConstraintSet.For_all
                  (fun '(l1, _, l2) =>
                     LevelSet.In l1 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)) /\
                     LevelSet.In l2 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)))
                  (constraints_of_udecl udecl)). {
      clear -H0. apply ConstraintSet.for_all_spec in H0.
      2: now intros x y [].
      intros [[l ct] l'] Hl. specialize (H0 _ Hl). simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H H0].
      apply LevelSet.mem_spec in H. apply LevelSet.mem_spec in H0.
      now split. }
    repeat split.
    - clear -H. apply LevelSet.for_all_spec in H.
      2: now intros x y [].
      intros l Hl. specialize (H l Hl); cbn in H.
      apply negb_true_iff in H. now apply LevelSetFact.not_mem_iff in H.
    - exact HH.
    - clear -H1. destruct udecl; trivial.
    - clear -HΣ HH Huctx H2 HG. unfold gc_of_uctx, uctx_of_udecl in *.
      simpl in *.
      unfold satisfiable_udecl.
      unfold is_graph_of_uctx in HG. unfold gc_of_uctx in *.
      case_eq (gc_of_constraints (global_uctx Σ).2);
        [|intro XX; rewrite XX in HG; contradiction HG].
      intros Σctrs HΣctrs.
      unfold global_ext_constraints. simpl in *.
      rewrite HΣctrs in HG.
      case_eq (gc_of_constraints (constraints_of_udecl udecl));
        [|intro XX; rewrite XX in Huctx; discriminate Huctx].
      intros ctrs Hctrs. rewrite Hctrs in Huctx. simpl in *.
      eapply (is_consistent_spec (global_ext_uctx (Σ, udecl))).
      { apply wf_global_uctx_invariants in HΣ.
        split.
        + clear -HΣ. cbn. apply LevelSet.union_spec; right.
          apply HΣ.
        + intros [[l ct] l'] Hl.
          apply ConstraintSet.union_spec in Hl. destruct Hl.
          apply (HH _ H). clear -HΣ H ct. destruct HΣ as [_ HΣ].
          specialize (HΣ (l, ct, l') H).
          split; apply LevelSet.union_spec; right; apply HΣ. }
      unfold is_consistent, global_ext_uctx, gc_of_uctx, global_ext_constraints.
      simpl.
      rewrite gc_of_constraints_union.
      rewrite HΣctrs, Hctrs.
      inversion Huctx; subst; clear Huctx.
      clear -H2 cf. rewrite add_uctx_make_graph in H2.
      refine (eq_rect _ (fun G => wGraph.is_acyclic G = true) H2 _ _).
      apply graph_eq; try reflexivity.
      + simpl. unfold global_ext_levels. simpl.
        rewrite no_prop_levels_union. reflexivity.
      + simpl. unfold global_ext_levels. simpl.
        rewrite no_prop_levels_union. reflexivity.
  Defined.

  Program Fixpoint check_wf_env (Σ : global_env)
    : EnvCheck (∑ G, (is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥)) :=
    match Σ with
    | [] => ret (init_graph; _)
    | d :: Σ =>
        G <- check_wf_env Σ ;;
        check_fresh (global_decl_ident d) Σ ;;
        let udecl := universes_decl_of_decl d in
        uctx <- check_udecl (global_decl_ident d) Σ _ G.π1 (proj1 G.π2) udecl ;;
        let G' := add_uctx uctx.π1 G.π1 in
        check_wf_decl (Σ, udecl) _ _ G' _ d ;;
        match udecl with
        | Monomorphic_ctx _ => ret (G'; _)
        | Polymorphic_ctx _ => ret (G.π1; _)
        | Cumulative_ctx _ => ret (G.π1; _)
        end
    end.
  Next Obligation.
    repeat constructor. apply graph_eq; try reflexivity.
    cbn. symmetry. apply wGraph.VSetProp.singleton_equal_add.
  Qed.
  Next Obligation.
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl d)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in *.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in *; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    symmetry; apply add_uctx_make_graph.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl d)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in *.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union.
    assert (eq: monomorphic_constraints_decl d
                = constraints_of_udecl (universes_decl_of_decl d)). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq; clear eq. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in *; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    assert (eq: monomorphic_levels_decl d
                = levels_of_udecl (universes_decl_of_decl d)). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq. symmetry; apply add_uctx_make_graph.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold global_uctx; simpl.
    assert (eq1: monomorphic_levels_decl d = LevelSet.empty). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assert (eq1: monomorphic_constraints_decl d = ConstraintSet.empty). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assumption.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold global_uctx; simpl.
    assert (eq1: monomorphic_levels_decl d = LevelSet.empty). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assert (eq1: monomorphic_constraints_decl d = ConstraintSet.empty). {
      destruct d. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assumption.
  Qed.


  Lemma wf_consistent Σ : wf Σ -> consistent (global_constraints Σ).
  Proof.
    destruct Σ.
    - exists {| valuation_mono := fun _ => 1%positive;  valuation_poly := fun _ => 0 |}.
      intros x Hx; now apply ConstraintSetFact.empty_iff in Hx.
    - inversion 1; subst. subst udecl. clear -H2.
      destruct H2 as [_ [_ [_ [v Hv]]]].
      exists v. intros ct Hc. apply Hv. simpl in *.
      apply ConstraintSet.union_spec in Hc. destruct Hc.
      apply ConstraintSet.union_spec; simpl.
      + left. destruct g.
        destruct c, cst_universes. assumption.
        1-2: apply ConstraintSetFact.empty_iff in H; contradiction.
        destruct m, ind_universes. assumption.
        1-2: apply ConstraintSetFact.empty_iff in H; contradiction.
      + apply ConstraintSet.union_spec; simpl.
        now right.
  Qed.


  Program Definition typecheck_program (p : program) φ Hφ
    : EnvCheck (∑ A, ∥ (List.rev p.1, φ) ;;; [] |- p.2  : A ∥) :=
    let Σ := List.rev (fst p) in
    G <- check_wf_env Σ ;;
    uctx <- check_udecl "toplevel term" Σ _ G.π1 (proj1 G.π2) φ ;;
    let G' := add_uctx uctx.π1 G.π1 in
    @infer_term (Σ, φ) (proj2 G.π2) Hφ G' _ (snd p).
  Next Obligation.
    (* todo: factorize with check_wf_env second obligation *)
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl φ));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in *.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints (List.rev p.1)));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in *; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    symmetry; apply add_uctx_make_graph.
  Qed.

End CheckEnv.
