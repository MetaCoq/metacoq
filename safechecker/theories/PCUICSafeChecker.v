(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICConversion PCUICWfUniverses.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion.

From Equations Require Import Equations.
Require Import ssreflect.

Local Set Keyed Unification.
Set Equations Transparent.

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
     | [], [] => ret All2_nil
     | a :: l1, b :: l2 => X <- f a b ;;
                          Y <- monad_All2 wrong_sizes f l1 l2 ;;
                          ret (All2_cons X Y)
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

Lemma isType_red {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T U} :
  isType Σ Γ T -> red Σ Γ T U -> isType Σ Γ U.
Proof.
  intros [s Hs] red; exists s.
  eapply subject_reduction; eauto.
Qed.




Derive NoConfusion EqDec for allowed_eliminations.

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotCumulSmaller (G : universes_graph) (Γ : context) (t u t' u' : term) (e : ConversionError)
| NotConvertible (G : universes_graph) (Γ : context) (t u : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| NotAnArity (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Definition print_level := string_of_level.

Definition string_of_Z z :=
  if (z <=? 0)%Z then "-" ^ string_of_nat (Z.to_nat (- z)) else string_of_nat (Z.to_nat z).

Definition print_edge '(l1, n, l2)
  := "(" ^ print_level l1 ^ ", " ^ string_of_Z n ^ ", "
         ^ print_level l2 ^ ")".

Definition print_universes_graph (G : universes_graph) :=
  let levels := LevelSet.elements G.1.1 in
  let edges := wGraph.EdgeSet.elements G.1.2 in
  string_of_list print_level levels
  ^ "\n" ^ string_of_list print_edge edges.

Definition string_of_conv_pb (c : conv_pb) : string :=
  match c with
  | Conv => "conversion"
  | Cumul => "cumulativity"
  end.

Definition print_term Σ Γ t :=
  print_term Σ Γ true false t.

Fixpoint string_of_conv_error Σ (e : ConversionError) : string :=
  match e with
  | NotFoundConstants c1 c2 =>
      "Both constants " ^ string_of_kername c1 ^ " and " ^ string_of_kername c2 ^
      " are not found in the environment."
  | NotFoundConstant c =>
      "Constant " ^ string_of_kername c ^
      " common in both terms is not found in the environment."
  | LambdaNotConvertibleAnn Γ1 na A1 t1 Γ2 na' A2 t2 =>
      "When comparing\n" ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      "\nand\n" ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      "\nbinding annotations are not convertible\n"
  | LambdaNotConvertibleTypes Γ1 na A1 t1 Γ2 na' A2 t2 e =>
      "When comparing\n" ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      "\nand\n" ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      "\ntypes are not convertible:\n" ^
      string_of_conv_error Σ e
  | ProdNotConvertibleAnn Γ1 na A1 B1 Γ2 na' A2 B2 =>
      "When comparing\n" ^ print_term Σ Γ1 (tProd na A1 B1) ^
      "\nand\n" ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      "\nbinding annotations are not convertible:\n"
  | ProdNotConvertibleDomains Γ1 na A1 B1 Γ2 na' A2 B2 e =>
      "When comparing\n" ^ print_term Σ Γ1 (tProd na A1 B1) ^
      "\nand\n" ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      "\ndomains are not convertible:\n" ^
      string_of_conv_error Σ e
  | CaseOnDifferentInd Γ ind par p c brs Γ' ind' par' p' c' brs' =>
      "The two stuck pattern-matching\n" ^
      print_term Σ Γ (tCase (ind, par) p c brs) ^
      "\nand\n" ^ print_term Σ Γ' (tCase (ind', par') p' c' brs') ^
      "\nare done on distinct inductive types."
  | CaseBranchNumMismatch
      ind par Γ p c brs1 m br brs2 Γ' p' c' brs1' m' br' brs2' =>
      "The two stuck pattern-matching\n" ^
      print_term Σ Γ (tCase (ind, par) p c (brs1 ++ (m,br) :: brs2)) ^
      "\nand\n" ^
      print_term Σ Γ' (tCase (ind, par) p' c' (brs1' ++ (m',br') :: brs2')) ^
      "\nhave a mistmatch in the branch number " ^ string_of_nat #|brs1| ^
      "\nthe number of parameters do not coincide\n" ^
      print_term Σ Γ br ^
      "\nhas " ^ string_of_nat m ^ " parameters while\n" ^
      print_term Σ Γ br' ^
      "\nhas " ^ string_of_nat m' ^ "."
  | DistinctStuckProj Γ p c Γ' p' c' =>
      "The two stuck projections\n" ^
      print_term Σ Γ (tProj p c) ^
      "\nand\n" ^
      print_term Σ Γ' (tProj p' c') ^
      "\nare syntactically different."
  | CannotUnfoldFix Γ mfix idx Γ' mfix' idx' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix mfix idx) ^
      "\nand\n" ^ print_term Σ Γ' (tFix mfix' idx') ^
      "\ncorrespond to syntactically distinct terms that can't be unfolded."
  | FixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix (mfix1 ++ u :: mfix2) idx) ^
      "\nand\n" ^ print_term Σ Γ' (tFix (mfix1' ++ v :: mfix2') idx) ^
      "\nhave a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | FixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix mfix idx) ^
      "\nand\n" ^
      print_term Σ Γ' (tFix mfix' idx) ^
      "\nhave a different number of mutually defined functions."
  | DistinctCoFix Γ mfix idx Γ' mfix' idx' =>
      "The two cofixed-points\n" ^
      print_term Σ Γ (tCoFix mfix idx) ^
      "\nand\n" ^ print_term Σ Γ' (tCoFix mfix' idx') ^
      "\ncorrespond to syntactically distinct terms."
  | CoFixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two co-fixed-points\n" ^
      print_term Σ Γ (tCoFix (mfix1 ++ u :: mfix2) idx) ^
      "\nand\n" ^ print_term Σ Γ' (tCoFix (mfix1' ++ v :: mfix2') idx) ^
      "\nhave a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | CoFixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two co-fixed-points\n" ^
      print_term Σ Γ (tCoFix mfix idx) ^
      "\nand\n" ^
      print_term Σ Γ' (tCoFix mfix' idx) ^
      "\nhave a different number of mutually defined functions."
  | StackHeadError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stackheaderror\n" ^
      string_of_conv_error Σ e
  | StackTailError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stacktailerror\n" ^
      string_of_conv_error Σ e
  | StackMismatch Γ1 t1 args1 l1 Γ2 t2 l2 =>
      "Convertible terms\n" ^
      print_term Σ Γ1 t1 ^
      "\nand\n" ^ print_term Σ Γ2 t2 ^
      "are convertible/convertible (TODO) but applied to a different number" ^
      " of arguments."
  | HeadMismatch leq Γ1 t1 Γ2 t2 =>
      "Terms\n" ^
      print_term Σ Γ1 t1 ^
      "\nand\n" ^ print_term Σ Γ2 t2 ^
      "\ndo not have the same head when comparing for " ^
      string_of_conv_pb leq
  end.

Definition string_of_type_error Σ (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unbound rel " ^ string_of_nat n
  | UnboundVar id => "Unbound var " ^ id
  | UnboundEvar ev => "Unbound evar " ^ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ^ string_of_kername c
  | UndeclaredInductive c => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | NotCumulSmaller G Γ t u t' u' e => "Terms are not <= for cumulativity:\n" ^
      print_term Σ Γ t ^ "\nand:\n" ^ print_term Σ Γ u ^
      "\nafter reduction:\n" ^
      print_term Σ Γ t' ^ "\nand:\n" ^ print_term Σ Γ u' ^
      "\nerror:\n" ^ string_of_conv_error Σ e ^
      "\nin universe graph:\n" ^ print_universes_graph G
  | NotConvertible G Γ t u => "Terms are not convertible:\n" ^
      print_term Σ Γ t ^ "\nand:\n" ^ print_term Σ Γ u ^
      "\nin universe graph:\n" ^ print_universes_graph G
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnArity t => print_term Σ [] t ^ " is not an arity"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg: " ^ s
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
Defined.

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

Lemma destArity_mkApps_None ctx t l :
  destArity ctx t = None -> destArity ctx (mkApps t l) = None.
Proof.
  induction l in t |- *. trivial.
  intros H. cbn. apply IHl. reflexivity.
Qed.

Lemma destArity_mkApps_Ind ctx ind u l :
  destArity ctx (mkApps (tInd ind u) l) = None.
Proof.
    apply destArity_mkApps_None. reflexivity.
Qed.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Definition isType_welltyped {Γ t}
    : isType Σ Γ t -> welltyped Σ Γ t.
  Proof.
    intros []. now econstructor.
  Qed.

  Lemma validity_wf {Γ t T} :
    ∥ wf_local Σ Γ ∥ -> ∥ Σ ;;; Γ |- t : T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [wΓ] [X].
    intros. eapply validity_term in X; try assumption.
    destruct X. now exists (tSort x).
  Defined.

  Lemma wat_welltyped {Γ T} :
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [X].
    now apply isType_welltyped.
  Defined.

  Definition hnf := reduce_term RedFlags.default Σ HΣ.

  Theorem hnf_sound {Γ t h} : ∥ red (fst Σ) Γ t (hnf Γ t h) ∥.
  Proof.
    apply reduce_term_sound.
  Defined.
  
  Theorem hnf_complete {Γ t h} : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
  Proof.
    apply reduce_term_complete.
  Qed.

  Inductive view_sort : term -> Type :=
  | view_sort_sort s : view_sort (tSort s)
  | view_sort_other t : ~isSort t -> view_sort t.

  Equations view_sortc (t : term) : view_sort t :=
    view_sortc (tSort s) := view_sort_sort s;
    view_sortc t := view_sort_other t _.

  Equations? reduce_to_sort (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ u, ∥ red (fst Σ) Γ t (tSort u) ∥) :=
    reduce_to_sort Γ t h with view_sortc t := {
      | view_sort_sort s => ret (s; sq (refl_red _ _ _));
      | view_sort_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_sortc hnft := {
          | view_sort_sort s => ret (s; _);
          | view_sort_other t _ => raise (NotASort t)
        }
      }.
  Proof.
    pose proof (hnf_sound (h:=h)).
    now rewrite eq.
  Qed.

  Lemma reduce_to_sort_complete {Γ t wt} e :
    reduce_to_sort Γ t wt = TypeError e ->
    (forall s, red Σ Γ t (tSort s) -> False).
  Proof.
    funelim (reduce_to_sort Γ t wt); try congruence.
    intros _ s r.
    pose proof (@hnf_complete Γ t0 h) as [wh].
    pose proof (@hnf_sound Γ t0 h) as [r'].
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); eauto.
    apply invert_red_sort in r2 as ->.
    eapply whnf_red_inv in r1; eauto.
    depelim r1.
    clear Heq.
    rewrite H in n0.
    now cbn in n0.
  Qed.

  Inductive view_prod : term -> Type :=
  | view_prod_prod na A b : view_prod (tProd na A b)
  | view_prod_other t : ~isProd t -> view_prod t.

  Equations view_prodc (t : term) : view_prod t :=
    view_prodc (tProd na A b) := view_prod_prod na A b;
    view_prodc t := view_prod_other t _.

  Equations? reduce_to_prod (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ na a b, ∥ red (fst Σ) Γ t (tProd na a b) ∥) :=
    reduce_to_prod Γ t h with view_prodc t := {
      | view_prod_prod na a b => ret (na; a; b; sq (refl_red _ _ _));
      | view_prod_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_prodc hnft := {
          | view_prod_prod na a b => ret (na; a; b; _);
          | view_prod_other t' _ => raise (NotAProduct t t')
        }
      }.
  Proof.
    pose proof (hnf_sound (h:=h)).
    now rewrite eq.
  Qed.

  Lemma reduce_to_prod_complete {Γ t wt} e :
    reduce_to_prod Γ t wt = TypeError e ->
    (forall na a b, red Σ Γ t (tProd na a b) -> False).
  Proof.
    funelim (reduce_to_prod Γ t wt); try congruence.
    intros _ na a b r.
    pose proof (@hnf_complete Γ t0 h) as [wh].
    pose proof (@hnf_sound Γ t0 h) as [r'].
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); eauto.
    apply invert_red_prod in r2 as (?&?&(->&?)&?); auto.
    eapply whnf_red_inv in r1; auto.
    depelim r1.
    clear Heq.
    rewrite H in n0.
    now cbn in n0.
  Qed.

  Definition isInd (t : term) : bool :=
    match t with
    | tInd _ _ => true
    | _ => false
    end.

  Inductive view_ind : term -> Type :=
  | view_ind_tInd ind u : view_ind (tInd ind u)
  | view_ind_other t : negb (isInd t) -> view_ind t.

  Equations view_indc (t : term) : view_ind t :=
    view_indc (tInd ind u) => view_ind_tInd ind u;
    view_indc t => view_ind_other t _.

  Equations? reduce_to_ind (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ i u l, ∥ red (fst Σ) Γ t (mkApps (tInd i u) l) ∥) :=
    reduce_to_ind Γ t h with inspect (decompose_app t) := {
      | exist (thd, args) eq_decomp with view_indc thd := {
        | view_ind_tInd i u => ret (i; u; args; sq _);
        | view_ind_other t _ with inspect (reduce_stack RedFlags.default Σ HΣ Γ t Empty h) := {
          | exist (hnft, π) eq with view_indc hnft := {
            | view_ind_tInd i u with inspect (decompose_stack π) := {
              | exist (l, _) eq_decomp => ret (i; u; l; _)
              };
            | view_ind_other _ _ => raise (NotAnInductive t)
            }
          }
        }
      }.
  Proof.
    - assert (X : mkApps (tInd i u) args = t); [|rewrite X; apply refl_red].
      etransitivity. 2: symmetry; eapply mkApps_decompose_app.
      now rewrite <- eq_decomp.
    - pose proof (reduce_stack_sound RedFlags.default Σ HΣ _ _ Empty h).
      rewrite <- eq in H.
      cbn in *.
      assert (π = appstack l ε) as ->.
      2: { now rewrite zipc_appstack in H. }
      unfold reduce_stack in eq.
      destruct reduce_stack_full as (?&_&stack_val&?).
      subst x.
      unfold Pr in stack_val.
      cbn in *.
      assert (decomp: decompose_stack π = ((decompose_stack π).1, ε)).
      { rewrite stack_val.
        now destruct decompose_stack. }
      apply decompose_stack_eq in decomp as ->.
      now rewrite <- eq_decomp0.
  Qed.

  Lemma reduce_to_ind_complete Γ ty wat e :
    reduce_to_ind Γ ty wat = TypeError e ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
  Proof.
    funelim (reduce_to_ind Γ ty wat); try congruence.
    intros _ ind u args r.
    pose proof (reduce_stack_whnf RedFlags.default Σ HΣ Γ t ε h) as wh.
    unfold reduce_stack in *.
    destruct reduce_stack_full as ((hd&π)&r'&stack_valid&(notapp&_)).
    destruct wh as [wh].
    apply Req_red in r' as [r'].
    unfold Pr in stack_valid.
    cbn in *.
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); [|eassumption|exact r'].
    assert (exists args, π = appstack args ε) as (?&->).
    { exists ((decompose_stack π).1).
      assert (decomp: decompose_stack π = ((decompose_stack π).1, ε)).
      { now rewrite stack_valid; destruct decompose_stack. }
      now apply decompose_stack_eq in decomp. }

    unfold zipp in wh.
    rewrite stack_context_appstack decompose_stack_appstack in wh.
    rewrite zipc_appstack in r1.
    cbn in *.
    rewrite app_nil_r in wh.
    apply red_mkApps_tInd in r2 as (?&->&?); auto.
    eapply whnf_red_inv in r1; eauto.
    apply whnf_red_mkApps_inv in r1 as (?&?); auto.
    depelim w.
    noconf e0.
    discriminate i0.
  Qed.

  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.

  Program Definition convert_leq Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
    match leqb_term Σ G t u with true => ret _ | false =>
    match iscumul Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
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
      : typing_result ({u : Universe.t & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
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

    Program Definition infer_cumul Γ HΓ t A (hA : ∥ isType Σ Γ A ∥)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.π1 A _ _ ;;
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation. destruct hA; now apply wat_welltyped. Qed.
    Next Obligation.
      destruct HΣ, HΓ, hA, X, X0. constructor. eapply type_Cumul'; eassumption.
    Qed.
  End InferAux.


  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption. reflexivity.
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

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (uGraph.wGraph.V G) ->
    LevelSet.mem l (global_ext_levels Σ).
  Proof.
    unfold is_graph_of_uctx in HG.
    case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
      rewrite -> XX in *; simpl in *; [|contradiction].
    unfold gc_of_uctx in XX; simpl in XX.
    destruct (gc_of_constraints Σ); [|discriminate].
    inversion XX; subst. generalize (global_ext_levels Σ); intros lvs; cbn.
    clear. intro H. apply LevelSet.mem_spec. now apply LevelSet.mem_spec in H.
  Qed.


  Program Definition check_consistent_instance uctx u
    : typing_result (consistent_instance_ext Σ uctx u)
    := match uctx with
       | Monomorphic_ctx _ =>
         check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0")
       | Polymorphic_ctx (inst, cstrs) =>
         let '(inst, cstrs) := AUContext.repr (inst, cstrs) in
         check_eq_true (forallb (fun l => LevelSet.mem l (uGraph.wGraph.V G)) u)
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
    clear -cf HG. intros x; simpl. apply is_graph_of_uctx_levels.
  Qed.
  Next Obligation.
    repeat split.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.

  Definition eqb_opt_term (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term Σ G t u
    | None, None => true
    | _, _ => false
    end.


  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn.
    apply eqb_term_spec; tea. trivial.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term Σ G d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl Σ (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. rtoProp. apply eqb_opt_term_spec in H.
    eapply eqb_term_spec in H0; tea. now split.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.
  
  Program Definition check_is_allowed_elimination (u : Universe.t) (al : allowed_eliminations) :
    typing_result (is_allowed_elimination Σ u al) :=
    let o :=
    match al return option (is_allowed_elimination Σ u al) with
    | IntoSProp =>
      match Universe.is_sprop u with
      | true => Some _
      | false => None
      end
    | IntoPropSProp =>
      match is_propositional u with
      | true => Some _
      | false => None
      end
    | IntoSetPropSProp =>
      match is_propositional u || check_eqb_universe G u Universe.type0 with
      | true => Some _
      | false => None
      end
    | IntoAny => Some _
    end in
    match o with
    | Some t => Checked t
    | None => TypeError (Msg "Cannot eliminate over this sort")
    end.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
    intros val sat.
    symmetry in Heq_anonymous.
    apply is_sprop_val with (v := val) in Heq_anonymous.
    now rewrite Heq_anonymous.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
    intros val sat.
    unfold is_propositional in *.
    destruct Universe.is_prop eqn:prop.
    - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
    - destruct Universe.is_sprop eqn:sprop.
      + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
      + discriminate.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs eqn:cu; auto.
    intros val sat.
    unfold is_propositional in *.
    destruct Universe.is_prop eqn:prop.
    - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
    - destruct Universe.is_sprop eqn:sprop.
      + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
      + destruct check_eqb_universe eqn:check; [|discriminate].
        eapply check_eqb_universe_spec' in check; eauto.
        * unfold eq_universe, eq_universe0 in check.
          rewrite cu in check.
          specialize (check val sat).
          now rewrite check.
        * destruct HΣ, Hφ.
          now apply wf_ext_global_uctx_invariants.
        * destruct HΣ, Hφ.
          now apply global_ext_uctx_consistent.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
  Qed.

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
      check_eq_true (wf_universeb Σ u)
                    (Msg ("Sort contains an undeclared level " ^ string_of_sort u));;
      ret (tSort (Universe.super u); _)

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
      | Some (ConstantDecl d) =>
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
                    (* bad case info *)
                    (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_coind <- check_eq_true (negb (isCoFinite (ind_finite decl)))
            (Msg "Case on coinductives disallowed") ;;
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      pty <- infer Γ HΓ p ;;
      match destArity [] pty.π1 with
      | None => raise (Msg "the type of the return predicate of a Case is not an arity")
      | Some (pctx, ps) =>
        check_is_allowed_elimination ps (ind_kelim body);;
        let params := firstn par args in
        match build_case_predicate_type ind decl body params u ps with
        | None => raise (Msg "failure in build_case_predicate_type")
        | Some pty' =>
          (* We could avoid one useless sort comparison by only comparing *)
          (* the contexts [pctx] and [indctx] (what is done in Coq). *)
          match iscumul Γ pty.π1 _ pty' _ with
          | ConvError e => raise (NotCumulSmaller G Γ pty.π1 pty' pty.π1 pty' e)
          | ConvSuccess =>
            match map_option_out (build_branches_type ind decl body params u p) with
            | None => raise (Msg "failure in build_branches_type")
            | Some btys =>
              let btyswf : ∥ All (isType Σ Γ ∘ snd) btys ∥ := _ in
              (fix check_branches (brs btys : list (nat * term))
                (HH : ∥ All (isType Σ Γ ∘ snd) btys ∥) {struct brs}
                  : typing_result
                    (All2 (fun br bty => br.1 = bty.1 /\ ∥ Σ ;;; Γ |- br.2 : bty.2 ∥) brs btys)
                          := match brs, btys with
                             | [], [] => ret All2_nil
                             | (n, t) :: brs , (m, A) :: btys =>
                               W <- check_dec (Msg "not nat eq")
                                             (EqDecInstances.nat_eqdec n m) ;;
                               Z <- infer_cumul infer Γ HΓ t A _ ;;
                               X <- check_branches brs btys _ ;;
                               ret (All2_cons (conj _ _) X)
                             | [], _ :: _
                             | _ :: _, [] => raise (Msg "wrong number of branches")
                             end) brs btys btyswf ;;
                ret (mkApps p (List.skipn par args ++ [c]); _)
            end
          end
        end
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
        let ty := snd pdecl in
        ret (subst0 (c :: List.rev args) (subst_instance_constr u ty);
                _)
      | None => raise (Msg "projection not found")
      end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) {struct mfix}
              : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
              := match mfix with
                 | [] => ret (sq All_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   Z <- check_types mfix ;;
                   ret _
                 end)
           mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
              (XX : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
            {struct mfix'}
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
        wffix <- check_eq_true (wf_fixpoint Σ.1 mfix) (Msg "Ill-formed fixpoint: not defined on a mutually inductive family") ;;
        ret (dtype decl; _)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <-  (fix check_types (mfix : mfixpoint term) {struct mfix}
        : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
        := match mfix with
           | [] => ret (sq All_nil)
           | def :: mfix =>
            (* probably not tail recursive but needed so that next line terminates *)
             W <- infer_type infer Γ HΓ (dtype def) ;;
             Z <- check_types mfix ;;
             ret _
           end)
         mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
        (XX' : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
        {struct mfix'}
        : typing_result (All (fun d =>
            ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (cofix_guard mfix) (Msg "Unguarded cofixpoint") ;;
        wfcofix <- check_eq_true (wf_cofixpoint Σ.1 mfix) (Msg "Ill-formed cofixpoint: not producing values in a mutually coinductive family") ;;
        ret (dtype decl; _)
      end
    end.

  (* tRel *)
  Next Obligation. intros; sq; now econstructor. Defined.
  (* tSort *)
  Next Obligation.
    eapply (reflect_bP (wf_universe_reflect _ _)) in H.
    sq; econstructor; tas.
  Defined.
  (* tProd *)
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s ?];  *)
      sq; econstructor; cbn; easy. Defined.
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s1 ?] [s2 ?]; *)
    sq; econstructor; eassumption.
  Defined.
  (* tLambda *)
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?]; *)
      sq; econstructor; cbn; easy.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?] [B ?]; *)
      sq; econstructor; eassumption.
  Defined.
  (* tLetIn *)
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?]; *)
      sq. econstructor; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0; *)
    sq; econstructor; cbn; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0 [? ?]; *)
    sq; econstructor; eassumption.
  Defined.

  (* tApp *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    cbn in *; sq.
    eapply type_reduction in X1 ; try eassumption.
    eapply validity_term in X1 ; try assumption. destruct X1 as [s HH].
    eapply inversion_Prod in HH ; try assumption.
    destruct HH as [s1 [_ [HH _]]].
    eexists. eassumption.
  Defined.
  Next Obligation.
    cbn in *; sq; econstructor.
    2: eassumption.
    eapply type_reduction; eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    rename Heq_anonymous into HH.
    sq; constructor; try assumption.
    symmetry in HH.
    etransitivity. eassumption. reflexivity.
  Defined.

  (* tInd *)
  Next Obligation.
    sq; econstructor; eassumption.
  Defined.

  (* tConstruct *)
  Next Obligation.
    sq; econstructor; tea. now split.
  Defined.

  (* tCase *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    destruct X, X9. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate].
    rename Heq_anonymous into HH. symmetry in HH.
    simpl in *.
    eapply type_reduction in t0; eauto. eapply validity in t0; eauto.
    rewrite <- e in HH.
    eapply PCUICInductiveInversion.WfArity_build_case_predicate_type in HH; eauto.
    destruct HH as [[s Hs] ?]. eexists; eauto.
    eapply validity in t; eauto.
    generalize (PCUICClosed.destArity_spec [] pty).
    rewrite -Heq_anonymous0 /=. intros ->.
    eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in t; eauto.
    eapply isType_wf_universes in t. simpl in t.
    now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) t). auto.
  Qed.

  Next Obligation.
    symmetry in Heq_anonymous2.
    unfold iscumul in Heq_anonymous2. simpl in Heq_anonymous2.
    apply isconv_term_sound in Heq_anonymous2.
    red in Heq_anonymous2.
    noconf Heq_I''.
    noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'.
    simpl in *; sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_reduction in X9; eauto.
    have val:= validity_term wfΣ X9.
    eapply type_Cumul' in X; [| |eassumption].
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in X; eauto.
        generalize (PCUICClosed.destArity_spec [] pty).
        rewrite -Heq_anonymous0 /=. intros ->.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in X; eauto.
        eapply isType_wf_universes in X. simpl in X.
        now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) X). auto. }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', ps)).
    { symmetry in Heq_anonymous1.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous1 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) in HH as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply PCUICInductiveInversion.build_branches_type_wt. 6:eapply X. all:eauto.
  Defined.

  Next Obligation.
    rename Heq_anonymous2 into XX2.
    symmetry in XX2. simpl in *. eapply isconv_sound in XX2.
    change (eqb ind ind' = true) in H0.
    destruct (eqb_spec ind ind') as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars decl) par = true) in H1.
    destruct (eqb_spec (ind_npars decl) par) as [e|e]; [|discriminate]; subst.
    depelim HH.
    sq. auto. now depelim X10.
  Defined.
  Next Obligation.
    sq. now depelim HH.
  Defined.

  (* The obligation tactic removes a useful let here. *)
  Obligation Tactic := idtac.
  Next Obligation.
    intros. clearbody btyswf. idtac; Program.Tactics.program_simplify.
    symmetry in Heq_anonymous2.
    unfold iscumul in Heq_anonymous2. simpl in Heq_anonymous2.
    apply isconv_term_sound in Heq_anonymous2.
    noconf Heq_I''. noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'. simpl in *.
    assert (∥ All2 (fun x y  => ((fst x = fst y) *
                              (Σ;;; Γ |- snd x : snd y) * isType Σ Γ y.2)%type) brs btys ∥). {
      solve_all. simpl in *.
      destruct btyswf. eapply All2_sq. solve_all. simpl in *; intuition (sq; auto). }
    clear H3. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_reduction in X9; eauto.
    eapply type_Cumul' in X; eauto.
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        now eapply validity in X9.
        eapply validity in X; eauto.
        generalize (PCUICClosed.destArity_spec [] pty).
        rewrite -Heq_anonymous0 /=. intros ->.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in X; eauto.
        eapply isType_wf_universes in X. simpl in X.
        now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) X). auto. }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', ps)).
    { symmetry in Heq_anonymous1.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous1 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) in HH as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply type_Case with (pty0:=pty'); tea.
    - reflexivity.
    - symmetry; eassumption.
    - destruct isCoFinite; auto.
    - symmetry; eauto.
  Defined.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.

  (* tProj *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    simpl in *; sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - eapply type_reduction in X5; eauto.
      eapply validity_term in X5; eauto.
      destruct (ssrbool.elimT (eqb_spec ind I)); auto.
      unshelve eapply (PCUICInductives.isType_mkApps_Ind _ X7 _) in X5 as [parsubst [argsubst [[sp sp'] cu]]]; eauto.
      pose proof (PCUICContexts.context_subst_length2 (PCUICSpine.inst_ctx_subst sp)).
      pose proof (PCUICContexts.context_subst_length2 (PCUICSpine.inst_ctx_subst sp')).
      autorewrite with len in H, H2.
      destruct (PCUICWeakeningEnv.on_declared_inductive HΣ X7) eqn:ond.
      rewrite -o.(onNpars) -H.
      forward (o0.(onProjections)).
      intros H'; rewrite H' nth_error_nil // in Heq_anonymous.
      destruct ind_cshapes as [|cs []]; auto.
      intros onps.
      unshelve epose proof (onps.(on_projs_noidx _ _ _ _ _ _)).
      rewrite ond /= in H2.
      change (ind_indices o0) with (ind_indices o0) in *.
      destruct (ind_indices o0) => //.
      simpl in H2.
      rewrite List.skipn_length in H2.
      rewrite List.firstn_length. lia.
  Qed.

  (* tFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX0. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX HΣ. sq.
    now depelim XX.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) * (isLambda (dbody d) = true))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      cbn; intros ? []. sq; now constructor. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

  (* tCoFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX'.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    now depelim XX'.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      now cbn; intros ? []. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

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
    sq. econstructor; tea.
  Qed.
  Next Obligation.
    sq. econstructor; tas. econstructor; eauto.
  Qed.

(* 
  Program Definition check_isWfArity Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isWfArity Σ Γ A ∥) :=
    match destArity [] A with
    | None => raise (Msg (print_term Σ Γ A ^ " is not an arity"))
    | Some (ctx, s) => XX <- check_context (Γ ,,, ctx) ;;
                      ret _
    end.
  Next Obligation.
    destruct XX. constructor. exists ctx, s.
    split; auto.
  Defined. *)

  Program Definition check_isType Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isType Σ Γ A ∥) :=
    s <- infer Γ HΓ A ;;
    s' <- reduce_to_sort Γ s.π1 _ ;;
    ret _.
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. destruct X0. sq. eexists. eapply type_reduction; tea. Defined.

  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isType Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _.

End Typecheck.


Definition infer' {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := infer (map_squash fst HΣ) (map_squash snd HΣ).

Definition make_graph_and_infer {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := let '(G; HG) := wf_ext_is_graph HΣ in infer' HΣ G HG.

Section CheckEnv.
  Context  {cf:checker_flags}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (Σ : global_env_ext) (e : env_error).
  Global Arguments EnvError {A} Σ e.
  Global Arguments CorrectDecl {A} a.

  Global Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError g e => EnvError g e
         end
    |}.

  Global Instance envcheck_monad_exc
    : MonadExc (global_env_ext * env_error) EnvCheck :=
    { raise A '(g, e) := EnvError g e;
      catch A m f :=
        match m with
        | CorrectDecl a => m
        | EnvError g t => f (g, t)
        end
    }.

  Definition wrap_error {A} Σ (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | Checked a => CorrectDecl a
    | TypeError e => EnvError Σ (IllFormedDecl id e)
    end.

  Definition check_wf_type kn Σ HΣ HΣ' G HG t
    : EnvCheck (∑ u, ∥ Σ;;; [] |- t : tSort u ∥)
    := wrap_error Σ (string_of_kername  kn) (@infer_type _ Σ HΣ (@infer _ Σ HΣ HΣ' G HG) [] sq_wfl_nil t).

  Definition check_wf_judgement kn Σ HΣ HΣ' G HG t ty
    : EnvCheck (∥ Σ;;; [] |- t : ty ∥)
    := wrap_error Σ (string_of_kername kn) (@check _ Σ HΣ HΣ' G HG [] sq_wfl_nil t ty).

  Definition infer_term Σ HΣ HΣ' G HG t :=
    wrap_error Σ "toplevel term" (@infer _ Σ HΣ HΣ' G HG [] sq_wfl_nil t).

  Program Fixpoint check_fresh id env : EnvCheck (∥ fresh_global id env ∥) :=
    match env with
    | [] => ret (sq (Forall_nil _))
    | g :: env =>
      p <- check_fresh id env;;
      match eq_constant id g.1 with
      | true => EnvError (empty_ext env) (AlreadyDeclared (string_of_kername id))
      | false => ret _
      end
    end.
  Next Obligation.
    sq. constructor; tas. simpl.
    change (false = eqb id k) in Heq_anonymous.
    destruct (eqb_spec id k); [discriminate|].
    easy.
  Defined.
      
  Definition check_variance univs (variances : option (list Variance.t)) :=
    match variances with
    | None => true
    | Some v =>
      match univs with
      | Monomorphic_ctx _ => false
      | Polymorphic_ctx auctx => eqb #|v| #|UContext.instance (AUContext.repr auctx)|
      end
    end.

  Definition Build_on_inductive_sq {Σ ind mdecl}
    : ∥ Alli (on_ind_body (lift_typing typing) Σ ind mdecl) 0 (ind_bodies mdecl) ∥ ->
      ∥ wf_local Σ (ind_params mdecl) ∥ ->
      context_assumptions (ind_params mdecl) = ind_npars mdecl ->
      ind_guard mdecl ->
      check_variance (ind_universes mdecl) (ind_variance mdecl) ->
      ∥ on_inductive (lift_typing typing) Σ ind mdecl ∥.
  Proof.
    intros H H0 H1 H2 H3. sq. econstructor; try eassumption.
    unfold check_variance in H3. unfold on_variance.
    destruct (ind_universes mdecl) eqn:E;
    destruct (ind_variance mdecl) eqn:E'; try congruence.
    2:split. now eapply eqb_eq in H3.
  Defined.

  Program Fixpoint monad_Alli {T} {M : Monad T} {A} {P} (f : forall n x, T (∥ P n x ∥)) l n
    : T (∥ @Alli A P n l ∥)
    := match l with
       | [] => ret (sq Alli_nil)
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

  (* We pack up all the information required on the global environment and graph in a 
    single record. *)
  Record wf_env {cf:checker_flags} := { 
      wf_env_env :> global_env_ext;
      wf_env_wf :> ∥ wf_ext wf_env_env ∥;
      wf_env_graph :> universes_graph;
      wf_env_graph_wf : is_graph_of_uctx wf_env_graph (global_ext_uctx wf_env_env)
  }.

  Definition wf_env_sq_wf (Σ : wf_env) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_wf Σ).
    sq. apply X.
  Qed.

  Definition check_type_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : 
    typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    @check cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (let 'sq wfΣ := wfΣ in sq wfΣ.2) G HG Γ wfΓ t T.

  Definition check_type_wf_env (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    check_type_wf_ext Σ (wf_env_wf Σ) Σ (wf_env_graph_wf Σ) Γ wfΓ t T.
  
  Definition infer_type_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : 
    typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥) := 
    @infer cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (let 'sq wfΣ := wfΣ in sq wfΣ.2) G HG Γ wfΓ t.

  Definition infer_type_wf_env (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥) := 
    infer_type_wf_ext Σ (wf_env_wf Σ) Σ (wf_env_graph_wf Σ) Γ wfΓ t.
    
  Definition wfnil {Σ : global_env_ext} : ∥ wf_local Σ [] ∥ := sq localenv_nil.
  Print Grammar constr.
  Notation " ' pat <- m ;; f " := (bind m (fun pat => f)) (pat pattern, right associativity, at level 100, m at next level).

  Fixpoint split_at_aux {A} (n : nat) (acc : list A) (l : list A) : list A * list A :=
    match n with 
    | 0 => (List.rev acc, l)
    | S n' => 
      match l with
      | [] => (List.rev acc, [])
      | hd :: l' => split_at_aux n' (hd :: acc) l'
      end
    end.

  Lemma split_at_aux_firstn_skipn {A} n acc (l : list A) : split_at_aux n acc l = (List.rev acc ++ firstn n l, skipn n l).
  Proof.
    induction n in acc, l |- *; destruct l; simpl; auto.
    now rewrite app_nil_r skipn_0.
    now rewrite app_nil_r skipn_0.
    now rewrite app_nil_r skipn_nil.
    rewrite IHn. simpl. 
    now rewrite -app_assoc skipn_S /=.
  Qed.

  Definition split_at {A} (n : nat) (l : list A) : list A * list A :=
    split_at_aux n [] l.

  Lemma split_at_firstn_skipn {A} n (l : list A) : split_at n l = (firstn n l, skipn n l).
  Proof.
    now rewrite /split_at split_at_aux_firstn_skipn /= //.
  Qed.
  
  Lemma inversion_it_mkProd_or_LetIn Σ {wfΣ : wf Σ.1}:
    forall {Γ Δ s A},
      Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) : A ->
      isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)).
  Proof.
    unfold isType. unfold PCUICTypingDef.typing. intros Γ Δ s A h. revert Γ s A h.
    induction Δ using rev_ind; intros.
    - simpl in h. eapply inversion_Sort in h as (?&?&?).
      eexists; constructor; eauto. apply wfΣ.
    - destruct x as [na [b|] ty]; simpl in *;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in h *.
      * eapply inversion_LetIn in h as [s' [? [? [? [? ?]]]]]; auto.
        specialize (IHΔ _ _ _ t1) as [s'' vdefty].
        exists s''.
        eapply type_Cumul'. econstructor; eauto. pcuic.
        eapply red_cumul. repeat constructor.
      * eapply inversion_Prod in h as [? [? [? [? ]]]]; auto.
        specialize (IHΔ _ _ _ t0) as [s'' Hs''].
        eexists (Universe.sort_of_product x s'').
        eapply type_Cumul'; eauto. econstructor; pcuic. pcuic.
        reflexivity.
  Qed.

  Program Definition check_constructors (Σ : wf_env) (id : kername) (mdecl : mutual_inductive_body)
    (n : nat) (idecl : one_inductive_body) (indices : context) : typing_result (∑ cs : list constructor_shape,
      on_constructors (lift_typing typing) Σ mdecl n idecl indices (ind_ctors idecl) cs) :=
      _.
  Admit Obligations.

  Definition check_projections_type (Σ : wf_env) (mind : kername) (mdecl : mutual_inductive_body)
  (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_shape) :=
    ind_projs idecl <> [] ->
    match cs return Type with
    | [cs] => on_projections mdecl mind i idecl indices cs
    | _ => False
    end.

  Program Definition check_projections (Σ : wf_env) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_shape) : 
    typing_result (check_projections_type Σ mind mdecl i idecl indices cs) := _.
  Admit Obligations.

  Program Definition check_ind_sorts' (Σ : wf_env) (params : context) (kelim : sort_family) (indices : context) 
    (cs : list constructor_shape) (ind_sort : Universe.t) : 
    typing_result (check_ind_sorts (lift_typing typing) Σ params kelim indices cs ind_sort) := _.
  Admit Obligations.

  Program Definition check_indices Σ mdecl indices :
    typing_result (forall v : list Variance.t,
                PCUICEnvironment.ind_variance mdecl = Some v ->
                ind_respects_variance (PCUICEnvironment.fst_ctx Σ) mdecl v indices) := _.
  Admit Obligations.

  Program Definition check_one_ind_body (Σ : wf_env) (mind : kername) (mdecl : mutual_inductive_body)
      (i : nat) (idecl : one_inductive_body) : typing_result (∥ on_ind_body (lift_typing typing) Σ mind mdecl i idecl ∥) :=
      '(T ; Tty) <- infer_type_wf_env Σ [] wfnil idecl.(ind_type) ;;
      '(ctxinds; p) <-
        ((match destArity [] idecl.(ind_type) as da return da = destArity [] idecl.(ind_type) -> typing_result (∑ ctxs, idecl.(ind_type) = it_mkProd_or_LetIn ctxs.1 (tSort ctxs.2)) with
        | Some (ctx, s) => fun eq => ret ((ctx, s); _)
        | None => fun _ => raise (NotAnArity T)
        end eq_refl)) ;;
      let '(indices, params) := split_at (#|ctxinds.1| - #|mdecl.(ind_params)|) ctxinds.1 in
      eqpars <- check_eq_true (eqb params mdecl.(ind_params)) (Msg "Inductive arity parameters do not match the parameters of the mutual declaration");;
      '(cs; oncstrs) <- check_constructors Σ mind mdecl i idecl indices ;;
      onprojs <- check_projections Σ mind mdecl i idecl indices cs ;;
      onsorts <- check_ind_sorts' Σ mdecl.(ind_params) idecl.(ind_kelim) indices cs ctxinds.2 ;;
      onindices <- check_indices Σ mdecl indices ;;
      ret (let 'sq Tty := Tty in 
        let 'sq wfext := Σ.(wf_env_wf) in
        (sq 
        {| ind_indices := indices; ind_sort := ctxinds.2; 
           ind_arity_eq := _; onArity := _;
           ind_cshapes := cs;
           onConstructors := oncstrs;
           onProjections := onprojs;
           ind_sorts := onsorts; 
           onIndices := onindices |})).
  Next Obligation. 
    symmetry in eq.
    apply destArity_spec_Some in eq. now simpl in eq.
  Qed.
  
  Next Obligation.
    change (eq_list _ _ _) with (eqb params (ind_params mdecl)) in eqpars.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    rewrite split_at_firstn_skipn in Heq_anonymous2. noconf Heq_anonymous2.
    rewrite -it_mkProd_or_LetIn_app H; autorewrite with len.
    rewrite List.skipn_length.
    replace (#|l0| - (#|l0| - (#|l0| - #|ind_params mdecl|))) with (#|l0| - #|ind_params mdecl|) by lia.
    now rewrite firstn_skipn.
  Qed.

  Next Obligation.
    red. red. 
    rewrite X0 in Tty.
    eapply inversion_it_mkProd_or_LetIn in Tty; auto.
    rewrite X0. apply Tty.
  Qed.
  
  Program Definition check_wf_decl (Σ : global_env_ext) HΣ HΣ' G HG
             kn (d : global_decl)
    : EnvCheck (∥ on_global_decl (lift_typing typing) Σ kn d ∥) :=
    match d with
    | ConstantDecl cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement kn Σ HΣ HΣ' G HG term cst.(cst_type) ;; ret _
      | None => check_wf_type kn Σ HΣ HΣ' G HG cst.(cst_type) ;; ret _
      end
    | InductiveDecl mdecl =>
      let wfΣ : wf_env := {| wf_env_env := Σ; wf_env_wf := _; 
        wf_env_graph := G; wf_env_graph_wf := HG |} in
      let id := string_of_kername kn in
      X1 <- monad_Alli (fun i oib => wrap_error Σ id (check_one_ind_body wfΣ kn mdecl i oib)) _ _ ;;
      X2 <- wrap_error Σ id (check_context HΣ HΣ' G HG (ind_params mdecl)) ;;
      X3 <- wrap_error Σ id (check_eq_nat (context_assumptions (ind_params mdecl))
                                       (ind_npars mdecl)
                                       (Msg "wrong number of parameters")) ;;
      X4 <- wrap_error Σ id (check_eq_true (ind_guard mdecl) (Msg "guard"));;
      X5 <- wrap_error Σ id (check_eq_true (check_variance mdecl.(ind_universes) mdecl.(ind_variance)) (Msg "variance"));;
      ret (Build_on_inductive_sq X1 X2 X3 X4 X5)
    end.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous; tas.
  Qed.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous.
    eexists. eassumption.
  Qed.
  Next Obligation.
    sq. split; auto.
  Qed.

  Obligation Tactic := idtac.
  Program Definition check_udecl id (Σ : global_env) (HΣ : ∥ wf Σ ∥) G
          (HG : is_graph_of_uctx G (global_uctx Σ)) (udecl : universes_decl)
    : EnvCheck (∑ uctx', gc_of_uctx (uctx_of_udecl udecl) = Some uctx' /\
                         ∥ on_udecl Σ udecl ∥) :=
    let levels := levels_of_udecl udecl in
    let global_levels := global_levels Σ in
    let all_levels := LevelSet.union levels global_levels in
    check_eq_true (LevelSet.for_all (fun l => negb (LevelSet.mem l global_levels)) levels)
       (empty_ext Σ, IllFormedDecl id (Msg ("non fresh level in " ^ print_lset levels)));;
    check_eq_true (ConstraintSet.for_all (fun '(l1, _, l2) => LevelSet.mem l1 all_levels && LevelSet.mem l2 all_levels) (constraints_of_udecl udecl))
                                    (empty_ext Σ, IllFormedDecl id (Msg ("non declared level in " ^ print_lset levels ^
                                    " |= " ^ print_constraint_set (constraints_of_udecl udecl))));;
    check_eq_true match udecl with
                  | Monomorphic_ctx ctx
                    => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                  | _ => true
                  end (empty_ext Σ, IllFormedDecl id (Msg "Var level in monomorphic context")) ;;
    (* TODO: could be optimized by reusing G *)
    match gc_of_uctx (uctx_of_udecl udecl) as X' return (X' = _ -> EnvCheck _) with
    | None => fun _ =>
      raise (empty_ext Σ, IllFormedDecl id (Msg "constraints trivially not satisfiable"))
    | Some uctx' => fun Huctx =>
      check_eq_true (wGraph.is_acyclic (add_uctx uctx' G))
                    (empty_ext Σ, IllFormedDecl id (Msg "constraints not satisfiable"));;
      ret (uctx'; _)
    end eq_refl.
  Next Obligation.
    Tactics.program_simpl.
  Qed.
  Next Obligation.
    simpl. intros. rewrite <- Huctx.
    split; auto.
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
      rewrite HΣctrs in HG. simpl in HG.
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
      pose proof (gc_of_constraints_union (constraints_of_udecl udecl) (global_constraints Σ)).
      rewrite {}HΣctrs {}Hctrs in H. simpl in H.
      destruct gc_of_constraints. simpl in H.
      inversion Huctx; subst; clear Huctx.
      clear -H H2 cf. rewrite add_uctx_make_graph in H2.
      refine (eq_rect _ (fun G => wGraph.is_acyclic G = true) H2 _ _).
      apply graph_eq; try reflexivity.
      + assert(make_graph (global_ext_levels (Σ, udecl), t) = 
        make_graph (global_ext_levels (Σ, udecl), (GoodConstraintSet.union ctrs Σctrs))).
        apply graph_eq. simpl; reflexivity.
        unfold make_graph. simpl.
        now rewrite H. simpl. reflexivity.
        rewrite H0. reflexivity.
      + now simpl in H. 
    Qed.

  Obligation Tactic := Program.Tactics.program_simpl.

  Lemma levelset_union_empty s : LevelSet.union LevelSet.empty s = s.
  Proof.
    apply LevelSet.eq_leibniz.
    change LevelSet.eq with LevelSet.Equal.
    intros x; rewrite LevelSet.union_spec. lsets.
  Qed.

  Lemma constraintset_union_empty s : ConstraintSet.union ConstraintSet.empty s = s.
  Proof.
    apply ConstraintSet.eq_leibniz.
    change ConstraintSet.eq with ConstraintSet.Equal.
    intros x; rewrite ConstraintSet.union_spec. lsets.
  Qed.

  Program Fixpoint check_wf_env (Σ : global_env)
    : EnvCheck (∑ G, (is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥)) :=
    match Σ with
    | [] => ret (init_graph; _)
    | d :: Σ =>
        G <- check_wf_env Σ ;;
        check_fresh d.1 Σ ;;
        let udecl := universes_decl_of_decl d.2 in
        uctx <- check_udecl (string_of_kername d.1) Σ _ G.π1 (proj1 G.π2) udecl ;;
        let G' := add_uctx uctx.π1 G.π1 in
        check_wf_decl (Σ, udecl) _ _ G' _ d.1 d.2 ;;
        match udecl with
        | Monomorphic_ctx _ => ret (G'; _)
        | Polymorphic_ctx _ => ret (G.π1; _)
        end
    end.
  Next Obligation.
    repeat constructor.
  Qed.
  Next Obligation.
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union 
      (constraints_of_udecl (universes_decl_of_decl g)) (global_constraints Σ)).
    rewrite Hctrs' /= in H0.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in H0, i; simpl in *.
    destruct (gc_of_constraints (ConstraintSet.union _ _)).
    simpl in H0. 
    subst G. unfold global_ext_levels; simpl.
    symmetry. rewrite add_uctx_make_graph.
    apply graph_eq. simpl. reflexivity.
    simpl. now rewrite H0. simpl. reflexivity.
    now simpl in H0.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union 
      (constraints_of_udecl (universes_decl_of_decl g)) (global_constraints Σ)).
    rewrite Hctrs' /= in H1.
    red in i. unfold gc_of_uctx in i; simpl in i.
    assert (eq: monomorphic_constraints_decl g
                = constraints_of_udecl (universes_decl_of_decl g)). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq; clear eq. 
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in H1, i; simpl in *.
    destruct (gc_of_constraints (ConstraintSet.union _ _)).
    simpl in H1.
    subst G. unfold global_ext_levels; simpl.
    assert (eq: monomorphic_levels_decl g
                = levels_of_udecl (universes_decl_of_decl g)). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq. simpl. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    simpl. now rewrite H1.
    now simpl in H1.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold global_uctx; simpl.
    assert (eq1: monomorphic_levels_decl g = LevelSet.empty). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assert (eq1: monomorphic_constraints_decl g = ConstraintSet.empty). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    now rewrite levelset_union_empty constraintset_union_empty.
  Qed.

  Obligation Tactic := idtac.

  Program Definition check_wf_ext (Σ : global_env_ext) : EnvCheck (∑ G, is_graph_of_uctx G (global_ext_uctx Σ) * ∥ wf_ext Σ ∥) :=
    G <- check_wf_env Σ.1 ;;
    uctx <- check_udecl "toplevel term" Σ.1 (proj2 G.π2) G.π1 (proj1 G.π2) Σ.2 ;;
    let G' := add_uctx uctx.π1 G.π1 in
    ret (G'; _).

  Next Obligation. simpl. 
    simpl; intros. subst. destruct G as [G []].
    destruct uctx as [uctx' []]. split.
    unfold is_graph_of_uctx, gc_of_uctx in *; simpl.
    destruct Σ as [Σ univs]. simpl in *.
    simpl in e. simpl. 
    case_eq (gc_of_constraints (constraints_of_udecl univs));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    noconf e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union (constraints_of_udecl univs) (global_constraints Σ)).
    rewrite Hctrs' /= in H.
    red in i. unfold gc_of_uctx in i; simpl in i. 
    destruct (gc_of_constraints (global_constraints Σ)) eqn:HΣcstrs; auto.
    simpl. unfold global_ext_levels; simpl.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
    simpl.
    subst G. symmetry. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    now simpl; rewrite H.
    sq; split; auto.
  Qed.

  (** We ensure the proof obligations stay opaque. *)

  Program Definition make_wf_env Σ : EnvCheck wf_env :=
    Gwf <- check_wf_ext Σ ;;
    ret {| wf_env_env := Σ; wf_env_wf := _; 
          wf_env_graph := Gwf.π1; wf_env_graph_wf := _ |}.
    Next Obligation.
      simpl; intros.
      abstract exact (Gwf.π2.2).
    Qed.
    Next Obligation.
      simpl; intros.
      abstract exact (Gwf.π2.1).
    Qed.
  
  Definition check_type_wf_env_bool (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : bool :=
    match check_type_wf_env Σ Γ wfΓ t T with
    | Checked _ => true
    | TypeError e => false
    end.
  
  Definition check_wf_env_bool_spec (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = true -> ∥ Σ ;;; Γ |- t : T ∥.
  Proof.
    unfold check_type_wf_env_bool, check_type_wf_env.
    destruct check_type_wf_ext; auto.
    discriminate.
  Qed.

  Definition check_wf_env_bool_spec2 (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = false -> type_error.
  Proof.
    unfold check_type_wf_env_bool, check_type_wf_env.
    destruct check_type_wf_ext; auto.
    discriminate.
  Defined.

  (* This function is appropriate for live evaluation inside Coq: 
     it forgets about the derivation produced by typing and replaces it with an opaque constant. *)

  Program Definition check_type_wf_env_fast (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t {T} : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    (if check_type_wf_env_bool Σ Γ wfΓ t T as x return (check_type_wf_env_bool Σ Γ wfΓ t T = x -> typing_result _) then
      fun eq => ret _
    else fun eq => raise (check_wf_env_bool_spec2 Σ Γ wfΓ t T eq)) eq_refl.

  Next Obligation.
    simpl; intros. exact (check_wf_env_bool_spec Σ Γ wfΓ t T eq).
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
      + left. destruct d.
        destruct c, cst_universes. assumption.
        apply ConstraintSetFact.empty_iff in H; contradiction.
        destruct m, ind_universes. assumption.
        apply ConstraintSetFact.empty_iff in H; contradiction.
      + apply ConstraintSet.union_spec; simpl.
        now right.
  Qed.

  Obligation Tactic := Program.Tactics.program_simpl.

  Program Definition typecheck_program (p : program) φ Hφ
    : EnvCheck (∑ A, ∥ (p.1, φ) ;;; [] |- p.2  : A ∥) :=
    let Σ := fst p in
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
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union (constraints_of_udecl φ) (global_constraints p.1)).
    rewrite Hctrs' /= in H.
    red in i. unfold gc_of_uctx in i; simpl in i. 
    destruct (gc_of_constraints (global_constraints p.1)) eqn:HΣcstrs; auto.
    simpl. unfold global_ext_levels; simpl.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
    simpl. simpl in i.
    subst G. symmetry. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    now simpl; rewrite H. simpl in H.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
  Qed.

End CheckEnv.
