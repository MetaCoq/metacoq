(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICUnivSubstitution PCUICWeakeningEnv.

From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICEqualityDec PCUICSafeConversion PCUICWfReduction.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

(** It otherwise tries [auto with *], very bad idea. *)
Ltac Coq.Program.Tactics.program_solve_wf ::= 
  match goal with 
  | |- @Wf.well_founded _ _ => auto with subterm wf
  | |- ?T => match type of T with
                | Prop => auto
                end
  end.

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
  intros; sq; now eapply wf_local_rel_app.
Qed.

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
  apply wf_local_local_rel, wf_local_rel_app.
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
  assert (consistent (global_ext_uctx Σ).2) as HC.
  { sq; apply (global_ext_uctx_consistent _ HΣ). }
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

  Definition isconv Γ := isconv_term Σ HΣ Hφ G HG Γ Conv.
  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.
  
  Program Definition convert Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t = u ∥) :=
    match eqb_term Σ G t u with true => ret _ | false =>
    match isconv Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller G Γ t u t' u' e)
      (* end *)
    end end.
  Next Obligation.
    symmetry in Heq_anonymous; eapply eqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

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
    sq; now eapply wf_ext_global_uctx_invariants.
    sq; now apply global_ext_uctx_consistent.
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
    eapply (elimT wf_universe_reflect) in H.
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
    now exact (elimT wf_universe_reflect t). auto.
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
        now exact (elimT wf_universe_reflect X). auto. }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', ps)).
    { symmetry in Heq_anonymous1.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous1 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) in HH as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply PCUICInductiveInversion.build_branches_type_wt. 6:eapply X. all:eauto.
  Defined.

  Obligation Tactic := simpl; intros.

  Next Obligation.
    rename Heq_anonymous2 into XX2.
    symmetry in XX2. simpl in *. eapply isconv_sound in XX2.
    change (eqb ind ind' = true) in H0.
    destruct (eqb_spec ind ind') as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars decl) par = true) in H1.
    destruct (eqb_spec (ind_npars decl) par) as [e|e]; [|discriminate]; subst.
    depelim HH.
    sq. auto. now depelim X.
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
        now exact (elimT wf_universe_reflect X). auto. }
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

  Program Fixpoint monad_Alli_All {T} {M : Monad T} {A} {P} {Q} (f : forall n x, ∥ Q x ∥ -> T (∥ P n x ∥)) l n :
    ∥ All Q l ∥ -> T (∥ @Alli A P n l ∥)
    := match l with
       | [] => fun _ => ret (sq Alli_nil)
       | a :: l => fun allq => X <- f n a _ ;;
                    Y <- monad_Alli_All f l (S n) _ ;;
                    ret _
       end.
  Next Obligation. sq.
    now depelim allq.
  Qed.
  Next Obligation.
    sq; now depelim allq.
  Qed.
  Next Obligation.
    sq. constructor; assumption.
  Defined.
  
  Section monad_Alli_nth.
    Context {T} {M : Monad T} {A} {P : nat -> A -> Type}.
    Program Fixpoint monad_Alli_nth_gen l k
      (f : forall n x, nth_error l n = Some x -> T (∥ P (k + n) x ∥)) : 
      T (∥ @Alli A P k l ∥)
      := match l with
        | [] => ret (sq Alli_nil)
        | a :: l => X <- f 0 a _ ;;
                    Y <- monad_Alli_nth_gen l (S k) (fun n x hnth => px <- f (S n) x hnth;; ret _) ;;
                    ret _
        end.
      Next Obligation.
        sq. now rewrite Nat.add_succ_r in px.
      Qed.
      Next Obligation.
        sq. rewrite Nat.add_0_r in X. constructor; auto.
      Qed.

    Definition monad_Alli_nth l (f : forall n x, nth_error l n = Some x -> T (∥ P n x ∥)) : T (∥ @Alli A P 0 l ∥) :=
      monad_Alli_nth_gen l 0 f.

  End monad_Alli_nth.

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
    wf_env_env :> global_env;
    wf_env_wf :> ∥ wf wf_env_env ∥;
    wf_env_graph :> universes_graph;
    wf_env_graph_wf : is_graph_of_uctx wf_env_graph (global_uctx wf_env_env)
  }.

  Record wf_env_ext {cf:checker_flags} := { 
      wf_env_ext_env :> global_env_ext;
      wf_env_ext_wf :> ∥ wf_ext wf_env_ext_env ∥;
      wf_env_ext_graph :> universes_graph;
      wf_env_ext_graph_wf : is_graph_of_uctx wf_env_ext_graph (global_ext_uctx wf_env_ext_env)
  }.

  Definition wf_env_sq_wf (Σ : wf_env) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_wf Σ).
    sq. apply X.
  Qed.
  
  Definition wf_env_ext_sq_wf (Σ : wf_env_ext) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_ext_wf Σ).
    sq. apply X.
  Qed.

  Section UniverseChecks.
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
      { sq. apply wf_global_uctx_invariants in HΣ.
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

  Program Definition check_wf_env_ext (Σ : global_env) (id : kername) (wfΣ : ∥ wf Σ ∥) (G : universes_graph) 
    (wfG : is_graph_of_uctx G (global_uctx Σ)) (ext : universes_decl) : 
    EnvCheck (∑ G, is_graph_of_uctx G (global_ext_uctx (Σ, ext)) /\ ∥ wf_ext (Σ, ext) ∥) :=
    uctx <- check_udecl (string_of_kername id) Σ wfΣ G wfG ext ;;
    let G' := add_uctx uctx.π1 G in
    ret (G'; _).
  Next Obligation.
    intros. simpl.
    destruct uctx as [uctx' [gcof onu]].
    subst G'.
    simpl. split.
    red in wfG |- *.
    unfold global_ext_uctx, gc_of_uctx. simpl.
    unfold gc_of_uctx in gcof. simpl in gcof.
    unfold gc_of_uctx in wfG. unfold global_ext_constraints. simpl in wfG |- *.
    pose proof (gc_of_constraints_union (constraints_of_udecl ext) (global_constraints Σ)).
    destruct (gc_of_constraints (global_constraints Σ)); simpl in *; auto.
    destruct (gc_of_constraints (constraints_of_udecl ext)); simpl in *; auto.
    noconf gcof.
    simpl in H.
    destruct gc_of_constraints; simpl in *; auto.
    symmetry. subst G.
    rewrite add_uctx_make_graph.
    apply graph_eq; simpl; auto.
    reflexivity. now rewrite H. discriminate.
    sq. pcuic.
  Qed.

  Program Definition make_wf_env_ext (Σ : wf_env) id (ext : universes_decl) : 
    EnvCheck ({ Σ' : wf_env_ext | Σ'.(wf_env_ext_env) = (Σ, ext)}) :=
    '(G; pf) <- check_wf_env_ext Σ id _ Σ _ ext ;;
    ret (exist {| wf_env_ext_env := (Σ, ext) ;
           wf_env_ext_wf := _ ;
           wf_env_ext_graph := G ;
           wf_env_ext_graph_wf := _ |} eq_refl).
    Next Obligation.
      intros []; simpl; intros. sq. apply wf_env_wf0.
    Qed.
    Next Obligation.
      intros []; simpl; intros. sq. apply wf_env_graph_wf0.
    Qed.
    Next Obligation.
      intros []; simpl; intros.
      destruct pf. destruct s. subst x.
      sq. apply w.
    Qed.
    Next Obligation.
      intros []; simpl; intros.
      destruct pf. destruct s. subst x.
      exact i.
    Qed.
  End UniverseChecks.

  Definition check_type_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : 
    typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    @check cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (let 'sq wfΣ := wfΣ in sq wfΣ.2) G HG Γ wfΓ t T.

  Definition check_type_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    check_type_wf_ext Σ (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t T.
  
  Definition infer_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : 
    typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥) := 
    @infer cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (let 'sq wfΣ := wfΣ in sq wfΣ.2) G HG Γ wfΓ t.

  Definition infer_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥) := 
    infer_wf_ext Σ (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t.
  
  Definition infer_type_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : 
    typing_result (∑ s, ∥ Σ ;;; Γ |- t : tSort s ∥) := 
    @infer_type cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (@infer_wf_ext Σ wfΣ G HG) Γ wfΓ t.

  Definition infer_type_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : typing_result (∑ s, ∥ Σ ;;; Γ |- t : tSort s ∥) := 
    infer_type_wf_ext Σ (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t.

  Definition wfnil {Σ : global_env_ext} : ∥ wf_local Σ [] ∥ := sq localenv_nil.
  
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
  
  Program Fixpoint check_type_local_ctx (Σ : wf_env_ext) Γ Δ s (wfΓ : ∥ wf_local Σ Γ ∥) : 
    typing_result (∥ type_local_ctx (lift_typing typing) Σ Γ Δ s ∥) := 
    match Δ with
    | [] => match wf_universeb Σ s with true => ret _ | false => raise (Msg "Ill-formed universe") end
    | {| decl_body := None; decl_type := ty |} :: Δ => 
      checkΔ <- check_type_local_ctx Σ Γ Δ s wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ ty (tSort s) ;;
      ret _
    | {| decl_body := Some b; decl_type := ty |} :: Δ => 
      checkΔ <- check_type_local_ctx Σ Γ Δ s wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ b ty ;;
      ret _
    end.
    Next Obligation.
      symmetry in Heq_anonymous. sq.
      now apply/PCUICWfUniverses.wf_universe_reflect.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      sq. split; auto.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto. split; auto.
      eapply PCUICValidity.validity_term in checkty; auto.
    Qed.
  
  Program Fixpoint infer_sorts_local_ctx (Σ : wf_env_ext) Γ Δ (wfΓ : ∥ wf_local Σ Γ ∥) : 
    typing_result (∑ s, ∥ sorts_local_ctx (lift_typing typing) Σ Γ Δ s ∥) := 
    match Δ with
    | [] => ret ([]; sq tt)
    | {| decl_body := None; decl_type := ty |} :: Δ => 
      '(Δs; Δinfer) <- infer_sorts_local_ctx Σ Γ Δ wfΓ ;;
      '(tys; tyinfer) <- infer_type_wf_env Σ (Γ ,,, Δ) _ ty ;;
      ret ((tys :: Δs); _)
    | {| decl_body := Some b; decl_type := ty |} :: Δ => 
      '(Δs; Δinfer) <- infer_sorts_local_ctx Σ Γ Δ wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ b ty ;;
      ret (Δs; _)
    end.
    Next Obligation.
      sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto. split; auto.
      eapply PCUICValidity.validity_term in checkty; auto.
    Qed.

  Definition cumul_decl Σ Γ (d d' : context_decl) : Type := cumul_decls Σ Γ Γ d d'.

  Program Definition wf_env_conv (Σ : wf_env_ext) (Γ : context) (t u : term) :
    welltyped Σ Γ t -> welltyped Σ Γ u -> typing_result (∥ Σ;;; Γ |- t = u ∥) :=
    @convert _ Σ (wf_env_ext_sq_wf Σ) _ Σ _ Γ t u.
  Next Obligation.
    destruct Σ. sq. simpl. apply wf_env_ext_wf0.
  Qed.
  Next Obligation.
    destruct Σ. sq. simpl. apply wf_env_ext_graph_wf0.
  Qed.

  Program Definition wf_env_cumul (Σ : wf_env_ext) (Γ : context) (t u : term) :
    welltyped Σ Γ t -> welltyped Σ Γ u -> typing_result (∥ Σ;;; Γ |- t <= u ∥) :=
    @convert_leq _ Σ (wf_env_ext_sq_wf Σ) _ Σ _ Γ t u.
  Next Obligation.
    destruct Σ. sq. simpl. apply wf_env_ext_wf0.
  Qed.
  Next Obligation.
    destruct Σ. sq. simpl. apply wf_env_ext_graph_wf0.
  Qed.

  Definition wt_decl (Σ : global_env_ext) Γ d :=
    match d with
    | {| decl_body := Some b; decl_type := ty |} => 
      welltyped Σ Γ ty /\ welltyped Σ Γ b
    | {| decl_body := None; decl_type := ty |} =>
      welltyped Σ Γ ty
    end.

  Lemma inv_wf_local (Σ : global_env_ext) Γ d :
    wf_local Σ (Γ ,, d) ->
    wf_local Σ Γ * wt_decl Σ Γ d.
  Proof.
    intros wfd; depelim wfd; split; simpl; pcuic.
    destruct l as [s Hs]. now exists (tSort s).
    destruct l as [s Hs]. now exists (tSort s).
    now exists t.
  Qed.

  Program Definition check_cumul_decl (Σ : wf_env_ext) Γ d d' : wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result (∥ cumul_decls Σ Γ Γ d d' ∥) := 
    match d, d' return wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result _ with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |},
      {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
      fun wtd wtd' =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumb <- wf_env_conv Σ Γ b b' _ _ ;;
      cumt <- wf_env_cumul Σ Γ ty ty' _ _ ;;
      ret (let 'sq cumb := cumb in 
            let 'sq cumt := cumt in
            sq _)
    | {| decl_name := na; decl_body := None; decl_type := ty |},
      {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
      fun wtd wtd' =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- wf_env_cumul Σ Γ ty ty' wtd wtd' ;;
      ret (let 'sq cumt := cumt in sq _)      
    | _, _ =>
      fun wtd wtd' => raise (Msg "While checking cumulativity of contexts: declarations do not match")
    end.
  Next Obligation.
    constructor; pcuics. now apply eqb_binder_annot_spec.
  Qed.
  Next Obligation.
    constructor; pcuics. now apply eqb_binder_annot_spec.
  Qed.

  Lemma cumul_ctx_rel_close Σ Γ Δ Δ' : 
    cumul_ctx_rel Σ Γ Δ Δ' ->
    cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    induction 1; pcuic.
  Qed.

  Lemma wf_ext_wf_p1 (Σ : global_env_ext) (wfΣ : wf_ext Σ) : wf Σ.1.
  Proof. apply wfΣ. Qed.
  Hint Resolve wf_ext_wf_p1 : pcuic.

  Lemma context_cumulativity_welltyped Σ (wfΣ : wf_ext Σ) Γ Γ' t : 
    welltyped Σ Γ t ->
    cumul_context Σ Γ' Γ ->
    wf_local Σ Γ' ->
    welltyped Σ Γ' t.
  Proof.
    intros [s Hs] cum wfΓ'; exists s; eapply context_cumulativity; pcuics.
  Qed.

  Lemma context_cumulativity_wt_decl Σ (wfΣ : wf_ext Σ) Γ Γ' d :
    wt_decl Σ Γ d ->
    cumul_context Σ Γ' Γ ->
    wf_local Σ Γ' ->
    wt_decl Σ Γ' d.
  Proof.
    destruct d as [na [b|] ty]; simpl;
    intuition pcuics; eapply context_cumulativity_welltyped; pcuics.
  Qed.

  Lemma cumul_decls_irrel_sec Σ (wfΣ : wf_ext Σ) Γ Γ' d d' :
    cumul_decls Σ Γ Γ d d' ->
    cumul_decls Σ Γ Γ' d d'.
  Proof.
    intros cum; depelim cum; intros; constructor; auto.
  Qed.

  Lemma cumul_ctx_rel_cons {Σ Γ Δ Δ' d d'} (c : cumul_ctx_rel Σ Γ Δ Δ') (p : cumul_decls Σ (Γ,,, Δ) (Γ ,,, Δ') d d') : 
    cumul_ctx_rel Σ Γ (Δ ,, d) (Δ' ,, d').
  Proof.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; try constructor; auto.
    depelim p. depelim p.
  Qed.

  Program Fixpoint check_cumul_ctx (Σ : wf_env_ext) Γ Δ Δ' 
    (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
    typing_result (∥ cumul_ctx_rel Σ Γ Δ Δ' ∥) :=
    match Δ, Δ' with
    | [], [] => ret (sq (ctx_rel_nil _))
    | decl :: Δ, decl' :: Δ' => 
      cctx <- check_cumul_ctx Σ Γ Δ Δ' _ _ ;;
      cdecl <- check_cumul_decl Σ (Γ ,,, Δ) decl decl' _ _ ;;
      ret _
    | _, _ => raise (Msg "While checking cumulativity of contexts: contexts have not the same length")
    end.
    Next Obligation.
      sq; now depelim wfΔ.
    Qed.
    Next Obligation.
      sq; now depelim wfΔ'.
    Qed.
    Next Obligation.
      sq.
      depelim wfΔ; simpl.
      destruct l; eexists; eauto.
      destruct l; split; eexists; eauto.
    Qed.
    Next Obligation.
      destruct Σ as [Σ [wfext] G isG].
      sq.
      assert(cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ')).
      now apply cumul_ctx_rel_close.
      simpl in *. eapply inv_wf_local in wfΔ as [wfΔ wfd].
      eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
      eapply context_cumulativity_wt_decl. 3:eassumption. all:pcuics.
    Qed.
    Next Obligation.
      destruct Σ as [Σ [wfext] G isG].
      sq; simpl in *.
      eapply inv_wf_local in wfΔ as [wfΔ wfd].
      eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
      apply cumul_ctx_rel_cons. auto.
      eapply cumul_decls_irrel_sec; pcuics.
    Qed.
    Next Obligation.
      split. intros. intros []. congruence. intros []; congruence.
    Qed.
    Next Obligation.
      split. intros. intros []. congruence. intros []; congruence.
    Qed.

  Program Definition check_eq_term le (Σ : wf_env_ext) t u : typing_result (∥ compare_term le Σ Σ t u ∥) :=
    check <- check_eq_true (if le then leqb_term Σ Σ t u else eqb_term Σ Σ t u) (Msg "Terms are not equal") ;;
    ret _.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
      destruct le; simpl.
      - eapply leqb_term_spec in check0; sq; auto.
        eapply wfΣ.
      - eapply eqb_term_spec in check0; sq; auto.
        apply wfΣ.
    Qed.

  Program Definition check_eq_decl le (Σ : wf_env_ext) d d' : typing_result (∥ eq_decl le Σ Σ d d' ∥) := 
    match d, d' return typing_result _ with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |},
      {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      eqb <- check_eq_term false Σ b b' ;;
      leqty <- check_eq_term le Σ ty ty' ;;
      ret (let 'sq eqb := eqb in 
            let 'sq leqty := leqty in
            sq _)
    | {| decl_name := na; decl_body := None; decl_type := ty |},
      {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- check_eq_term le Σ ty ty' ;;
      ret (let 'sq cumt := cumt in sq _)  
    | _, _ => raise (Msg "While checking syntactic cumulativity of contexts: declarations do not match")
    end.
    Next Obligation.
      eapply eqb_binder_annot_spec in eqna.
      now constructor; simpl.
    Qed.
    Next Obligation.
      eapply eqb_binder_annot_spec in eqna.
      now constructor; simpl.
    Qed.

  Program Fixpoint check_leq_context (le : bool) (Σ : wf_env_ext) Γ Δ : typing_result (∥ eq_context le Σ Σ Γ Δ ∥) :=
    match Γ, Δ with
    | [], [] => ret (sq All2_nil)
    | decl :: Γ, decl' :: Δ => 
      cctx <- check_leq_context le Σ Γ Δ ;;
      cdecl <- check_eq_decl le Σ decl decl' ;;
      ret _
    | _, _ => raise (Msg "While checking equality of contexts: contexts do not have the same length")
    end.

    Next Obligation.
      sq.
      constructor; auto.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.

  Program Fixpoint check_leq_terms (le : bool) (Σ : wf_env_ext) l l' : typing_result (∥ All2 (compare_term le Σ Σ) l l' ∥) :=
    match l, l' with
    | [], [] => ret (sq All2_nil)
    | t :: l, t' :: l' => 
      cctx <- check_leq_terms le Σ l l' ;;
      cdecl <- check_eq_term le Σ t t' ;;
      ret _
    | _, _ => raise (Msg "While checking equality of term lists: lists do not have the same length")
    end.

    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation. intuition congruence. Qed.
    Next Obligation. intuition congruence. Qed.

  Definition wt_terms Σ Γ l := Forall (welltyped Σ Γ) l.
  
  Program Fixpoint check_conv_args (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) l l'
    (wfl : wt_terms Σ Γ l) (wfl' : wt_terms Σ Γ l') :
    typing_result (∥ conv_terms Σ Γ l l' ∥) :=
    match l, l' with
    | [], [] => ret (sq All2_nil)
    | t :: l, t' :: l' => 
      checkt <- wf_env_conv Σ Γ t t' _ _ ;;
      checkts <- check_conv_args Σ Γ wfΓ l l' _ _ ;;
      ret _
    | _, _ => raise (Msg "While checking convertibility of arguments: lists have not the same length")
    end.
    Next Obligation.
      now depelim wfl.
    Qed.
    Next Obligation.
      now depelim wfl'.
    Qed.
    Next Obligation.
      now depelim wfl.
    Qed.
    Next Obligation.
      now depelim wfl'.
    Qed.
    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.
      
  Section MonadMapi.
    Context {T} {M : Monad T} {A B : Type} (f : nat -> A -> T B).
  
    Fixpoint monad_mapi_rec (n : nat) (l : list A) : T (list B) :=
      match l with
      | [] => ret []
      | x :: xs => x' <- f n x ;;
        xs' <- monad_mapi_rec (S n) xs ;;
        ret (x' :: xs')
      end.

    Definition monad_mapi (l : list A) := monad_mapi_rec 0 l.
  End MonadMapi.

  Definition check_constructor_spec (Σ : wf_env_ext) (ind : nat) (mdecl : mutual_inductive_body)
    (d : ((ident × term) × nat)) (cs : constructor_shape) :=
    isType Σ (arities_context mdecl.(ind_bodies)) d.1.2 * 
    (d.1.2 = 
      it_mkProd_or_LetIn 
        (mdecl.(ind_params) ,,, cs.(cshape_args))
        (mkApps (tRel (#|mdecl.(ind_params) ,,, cs.(cshape_args)| + (#|ind_bodies mdecl| - ind)))
          (to_extended_list_k mdecl.(ind_params) #|cs.(cshape_args)| ++ 
          cs.(cshape_indices)))) * 
    (sorts_local_ctx (lift_typing typing) Σ 
      (arities_context mdecl.(ind_bodies) ,,, ind_params mdecl) cs.(cshape_args) 
      cs.(cshape_sorts)) * 
    (d.2 = context_assumptions cs.(cshape_args)).

  Program Definition isRel_n n (t : term) : typing_result (t = tRel n) :=
    match t with
    | tRel k => match eqb k n with true => ret _ | false => raise (Msg "De-bruijn error") end
    | _ => raise (Msg "isRel_n: not a variable")
    end.
    Next Obligation.
      symmetry in Heq_anonymous.
      change (eqb k n : Prop) in Heq_anonymous. 
      destruct (eqb_spec k n). congruence. discriminate.
    Qed.

  Program Definition decompose_cstr_concl mdecl (k : nat) argctx (t : term) : typing_result 
    (∑ args, t = mkApps (tRel (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|)) args) :=
    let '(hd, args) := decompose_app t in
    eqr <- isRel_n (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|) hd ;;
    ret (args; _).
    Next Obligation.
      symmetry in Heq_anonymous.
      now apply decompose_app_inv in Heq_anonymous.
    Qed.

  Lemma decompose_prod_n_assum_inv ctx n t ctx' t' : 
    decompose_prod_n_assum ctx n t = Some (ctx', t') ->
    it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' t'.
  Proof.
    induction n in t, ctx, ctx', t' |- *; simpl.
    intros [= ->]. subst; auto.
    destruct t => //.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
  Qed.

  Arguments eqb : simpl never.

  Definition wf_ind_types (Σ : global_env_ext) (mdecl : mutual_inductive_body) :=
    All (fun ind => isType Σ [] ind.(ind_type)) mdecl.(ind_bodies).

  Lemma wf_ind_types_wf_arities (Σ : global_env_ext) (wfΣ : wf Σ) mdecl :
    wf_ind_types Σ mdecl -> 
    wf_local Σ (arities_context mdecl.(ind_bodies)).
  Proof.
    rewrite /wf_ind_types.
    unfold arities_context.
    induction 1; simpl; auto.
    rewrite rev_map_cons /=.
    eapply All_local_env_app; split. constructor; pcuic.
    eapply All_local_env_impl; eauto.
    move=> Γ t [] /=.
    * move=> ty ht. eapply weaken_ctx; eauto.
      constructor; pcuic.
    * move=> [s Hs]; exists s.
      eapply weaken_ctx; eauto.
      constructor; pcuic.
  Qed.

  Program Definition check_constructor (Σ : wf_env_ext) (ind : nat) (mdecl : mutual_inductive_body)
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (d : ((ident × term) × nat)) : 

    EnvCheck (∑ cs : constructor_shape, ∥ check_constructor_spec Σ ind mdecl d cs ∥) :=

    '(s; Hs) <- wrap_error Σ ("While checking type of constructor: " ^ d.1.1)
      (infer_type_wf_env Σ (arities_context mdecl.(ind_bodies)) _ d.1.2) ;;
    match decompose_prod_n_assum [] #|mdecl.(ind_params)| d.1.2 with
    | Some (params, concl) => 
      eqpars <- wrap_error Σ d.1.1
         (check_eq_true (eqb params mdecl.(ind_params)) 
        (Msg "Constructor parameters do not match the parameters of the mutual declaration"));;
      let '(args, concl) := decompose_prod_assum [] concl in
      eqargs <- wrap_error Σ d.1.1
        (check_eq_true (eqb (context_assumptions args) d.2)
          (Msg "Constructor arguments do not match the argument number of the declaration"));;
      '(conclargs; Hargs) <- wrap_error Σ d.1.1 
        (decompose_cstr_concl mdecl ind args concl) ;;
      eqbpars <- wrap_error Σ d.1.1
        (check_eq_true (eqb (firstn mdecl.(ind_npars) conclargs) (to_extended_list_k mdecl.(ind_params) #|args|))
          (Msg "Parameters in the conclusion of the constructor type do not match the inductive parameters")) ;;
      '(cs; Hcs) <- wrap_error Σ d.1.1 
        (infer_sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params)) args _) ;;
      ret ({| cshape_args := args;
              cshape_indices := skipn mdecl.(ind_npars) conclargs;
              cshape_sorts := cs |}; _)
    | None =>
      raise (Σ.(wf_env_ext_env), IllFormedDecl d.1.1 (Msg "Not enough parameters in constructor type"))
    end.

    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq.
      now apply wf_ind_types_wf_arities in wfar.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq.
      apply wf_ind_types_wf_arities in wfar.
      (* TODO lemma name clash between imports *)
      eapply PCUICWeakening.weaken_wf_local; eauto. apply wfΣ.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. red; simpl.
      intuition auto.
      eexists; eauto. 
      rename Heq_anonymous1 into dt.
      rename Heq_anonymous2 into dc.
      symmetry in dt.
      eapply decompose_prod_n_assum_inv in dt; simpl in dt; subst t.
      destruct (eqb_spec params (ind_params mdecl)) => //. subst params.
      symmetry in dc. eapply PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn in dc.
      simpl in dc. subst concl0.
      rewrite it_mkProd_or_LetIn_app. do 3 f_equal.
      f_equal. autorewrite with len. lia.
      rewrite -{1}(firstn_skipn (ind_npars mdecl) pat1). f_equal.
      revert eqbpars. 
      elim: (eqb_spec (firstn (ind_npars mdecl) pat1) _) => //.
      revert eqargs.
      elim: eqb_spec => //.
    Qed.

  Fixpoint All_sigma {A B} {P : A -> B -> Type} {l : list A} (a : All (fun x => ∑ y : B, P x y) l) : 
    ∑ l' : list B, All2 P l l' :=
    match a with
    | All_nil => ([]; All2_nil)
    | All_cons x l px pl =>
      let '(l'; pl') := All_sigma pl in
      ((px.π1 :: l'); All2_cons px.π2 pl')
    end.

  Fixpoint All2_sq {A B} {P : A -> B -> Type} {l : list A} {l' : list B} 
    (a : All2 (fun x y => ∥ P x y ∥) l l') : ∥ All2 P l l' ∥ :=
    match a with
    | All2_nil => sq All2_nil
    | All2_cons _ _ _ _ rxy all' => 
      let 'sq all := All2_sq all' in
      let 'sq rxy := rxy in
      sq (All2_cons rxy all)
    end.

  Program Definition constructor_shapes (Σ : wf_env_ext) (id : ident) (mdecl : mutual_inductive_body)
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (ind : nat)
    (cstrs : list ((ident × term) × nat)) : EnvCheck (∑ cs : list constructor_shape, 
      ∥ All2 (fun cstr cs => check_constructor_spec Σ ind mdecl cstr cs) cstrs cs ∥) :=
    css <- monad_All (fun d => check_constructor Σ ind mdecl wfar wfpars d) cstrs ;;
    let '(cs; all2) := All_sigma css in
    ret (cs; All2_sq all2).
    
  Lemma isType_it_mkProd_or_LetIn_inv {Σ : global_env_ext} Γ Δ T :
    wf Σ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    isType Σ (Γ ,,, Δ) T.
  Proof.
    move=> wfΣ [u Hu].
    exists u. unfold PCUICTypingDef.typing in *.
    now eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hu.
  Qed.

  Lemma isType_mkApps_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ f args :
    isType Σ Γ (mkApps f args) ->
    ∑ fty s, (Σ ;;; Γ |- f : fty) * 
      typing_spine Σ Γ fty args (tSort s).
  Proof.
    intros [s Hs].
    eapply inversion_mkApps in Hs as [fty [Hf Hargs]]; auto.
    now exists fty, s.
  Qed.

  Lemma nth_error_arities_context mdecl i idecl : 
    nth_error (List.rev mdecl.(ind_bodies)) i = Some idecl ->
    nth_error (arities_context mdecl.(ind_bodies)) i = 
      Some {| decl_name := {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |};
              decl_body := None;
              decl_type := idecl.(ind_type) |}.
  Proof.
    generalize mdecl.(ind_bodies) => l.
    intros hnth.
    epose proof (nth_error_Some_length hnth). autorewrite with len in H.
    rewrite nth_error_rev in hnth. now autorewrite with len.
    rewrite List.rev_involutive in hnth. autorewrite with len in hnth.
    unfold arities_context.
    rewrite rev_map_spec.
    rewrite nth_error_rev; autorewrite with len; auto.
    rewrite List.rev_involutive nth_error_map.
    rewrite hnth. simpl. reflexivity.
  Qed.

  Lemma ctx_inst_app {Σ : global_env_ext} (wfΣ : wf Σ) Γ args args' Δ Δ' :
    forall dom : ctx_inst Σ Γ args Δ, 
    ctx_inst Σ Γ args' (subst_telescope (ctx_inst_sub dom) 0 Δ') ->
    ctx_inst Σ Γ (args ++ args') (Δ ++ Δ').
  Proof.
    induction Δ as [|[na [b|] ty] Δ] using PCUICContexts.ctx_length_ind in args, Δ' |- *; simpl; auto; len.
    - intros ctx ctx'. depelim ctx; simpl in ctx'.
      now rewrite subst_telescope_empty in ctx'.
    - intros ctx ctx'. depelim ctx. simpl in *.
      specialize (X (subst_telescope [b] 0 Δ) ltac:(now len) args).
      len in X. 
      rewrite subst_app_telescope in ctx'. len in ctx'.
      specialize (X _ ctx ctx').
      constructor. rewrite subst_telescope_app.
      rewrite ctx_inst_subst_length in X. len in X. now len.
    - intros ctx ctx'. depelim ctx. simpl in *.
      specialize (X (subst_telescope [i] 0 Δ) ltac:(now len) inst).
      rewrite subst_app_telescope in ctx'. len in ctx'.
      specialize (X _ ctx ctx').
      constructor; auto. rewrite subst_telescope_app.
      rewrite ctx_inst_subst_length in X. len in X. now len.
  Qed.

  Lemma subst_context_subst_telescope s k Γ :
    subst_context s k (List.rev Γ) = List.rev (subst_telescope s k Γ).
  Proof.
    rewrite /subst_telescope subst_context_alt.
    rewrite rev_mapi. apply mapi_rec_ext.
    intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=; 
    rewrite List.rev_length Nat.add_0_r in le'; len; lia_f_equal.
  Qed.

  Definition smash_telescope acc Γ := 
    List.rev (smash_context acc (List.rev Γ)).

  Lemma ctx_inst_smash {Σ : global_env_ext} (wfΣ : wf Σ) (Γ Δ : context) args :
    ctx_inst Σ Γ args (smash_telescope [] Δ) ->
    ctx_inst Σ Γ args Δ.
  Proof.
    rewrite /smash_telescope.
    induction Δ as [|[na [b|] ty] Δ] using PCUICContexts.ctx_length_ind in args |- *; simpl; auto.
    - rewrite smash_context_app smash_context_acc /= lift0_context lift0_id subst_empty subst_context_nil 
        app_nil_r -smash_context_subst subst_context_nil.
      rewrite subst_context_subst_telescope.
      intros ctx. eapply X in ctx. 2:now len.
      now constructor.
    - rewrite smash_context_app smash_context_acc /=.
      rewrite subst_context_lift_id. rewrite List.rev_app_distr /=.
      intros ctx. depelim ctx.
      constructor; auto.
      eapply X. now len.
      rewrite -subst_context_subst_telescope.
      rewrite subst_telescope_subst_context in ctx.
      now rewrite -smash_context_subst /= subst_context_nil in ctx.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ Δ s args s' :
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') ->
    ctx_inst Σ Γ args (List.rev Δ).
  Proof.
    intros wf sp.
    pose proof (wf_local_smash_end _ _ _ wfΣ wf). clear wf.
    eapply PCUICCanonicity.typing_spine_smash in sp; auto.
    unfold expand_lets, expand_lets_k in sp. simpl in sp.
    apply ctx_inst_smash; auto.
    rewrite /smash_telescope List.rev_involutive.
    revert X sp.
    move: (@smash_context_assumption_context [] Δ assumption_context_nil).
    move: (smash_context [] Δ) => {}Δ.
    induction Δ using PCUICContexts.ctx_length_rev_ind in s, s', args |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros ass wf sp; depelim sp; try constructor.
    * now eapply cumul_Sort_Prod_inv in c.
    * apply assumption_context_app in ass as [ass assd].  
      destruct d as [na [b|] ty]; unfold mkProd_or_LetIn in c; simpl in *.
      elimtype False; depelim assd.
      eapply cumul_Prod_Sort_inv in c; auto.
    * apply assumption_context_app in ass as [ass assd].  
      destruct d as [na' [b'|] ty']; unfold mkProd_or_LetIn in c; simpl in *.
      elimtype False; depelim assd.
      eapply cumul_Prod_Prod_inv in c as [eqann [eqdom codom]]; auto.
      rewrite List.rev_app_distr.
      constructor.
      eapply All_local_env_app_inv in wf as [wfΓ wfr].
      eapply All_local_env_app_inv in wfr as [wfd wfΓ0].
      depelim wfd. destruct l as [? Hs].
      red. eapply type_Cumul'; pcuic. eapply conv_cumul. now symmetry.
      rewrite subst_telescope_subst_context. eapply X. now len.
      pcuic.
      eapply substitution_wf_local; eauto.
      2:rewrite app_context_assoc in wf; eapply wf.
      repeat constructor. rewrite subst_empty.
      eapply All_local_env_app_inv in wf as [wfΓ wfr].
      eapply All_local_env_app_inv in wfr as [wfd wfΓ0].
      depelim wfd. destruct l as [? Hs].
      eapply type_Cumul'; pcuic. eapply conv_cumul. now symmetry.
      eapply typing_spine_strengthen; eauto.
      eapply substitution_cumul0 in codom; eauto.
      now rewrite /subst1 subst_it_mkProd_or_LetIn in codom.
  Qed.
  
  Lemma typing_spine_letin_inv' {Σ : global_env_ext} (wfΣ : wf Σ) Γ na b ty Δ T args T' :
    let decl := {| decl_name := na; decl_body := Some b; decl_type := ty |} in
    wf_local Σ (Γ ,, decl) ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T)) args T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof.
    intros decl wf.
    cbn. intros sp.
    eapply typing_spine_strengthen; eauto.
    eapply conv_cumul.
    etransitivity.
    2:{ symmetry; eapply red_conv. repeat constructor. }
    etransitivity.
    symmetry.
    pose proof (red_expand_let Γ na b ty T).
    forward X. apply wf.
    epose proof (weakening_conv _ (Γ ,, decl) [] Δ).
    simpl in X0. len in X0.
    eapply X0. eauto.
    symmetry. eapply red_conv. apply X.
    simpl.
    rewrite distr_lift_subst. simpl.
    rewrite distr_lift_subst /=.
    rewrite simpl_lift. lia. lia.
    rewrite simpl_lift. lia. lia. 
    reflexivity.
  Qed.

  Lemma typing_spine_prod_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ na ty Δ T args T' :
    let decl := {| decl_name := na; decl_body := None; decl_type := ty |} in
    wf_local Σ (Γ ,, decl) ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T)) 
      (tRel #|Δ| :: args) T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof.
    intros decl wf.
    cbn. intros sp.
    depelim sp.
    eapply typing_spine_strengthen; eauto.
    eapply cumul_Prod_Prod_inv in c as [eqann [eqdom eqcodom]]; auto.
    eapply (substitution_cumul0 _ _ _ _ _ _ (tRel #|Δ|)) in eqcodom; auto.
    etransitivity; eauto.
    rewrite /subst1.
    replace ([tRel #|Δ|]) with (map (lift #|Δ| 0) [tRel 0]). 2:simpl; lia_f_equal.
    rewrite -(simpl_lift T _ _ _ 1); try lia.
    change 1 with (0 + #|[tRel 0]| + 0) at 1.
    rewrite -distr_lift_subst_rec /= //.
    now rewrite subst_rel0_lift_id.
  Qed.
  
  (** Non-trivial lemma: 
    this shows that instantiating a product/let-in type with the identity substitution on some 
    sub-context of the current context is the same as typechecking the remainder of the 
    type approapriately lifted to directly refer to the variables in the subcontext. 
    This is a quite common operation in tactics. Making this work up-to unfolding of
    let-ins is the tricky part.
  *)
  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen {Σ : global_env_ext} (wfΣ : wf Σ) Γ Δ Δ' Δ'' s args s' :
    wf_local Σ (Γ ,,, Δ) ->
    closedn_ctx #|Γ| (Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ ,,, Δ'| 0 (Δ ,,, Δ'')) (tSort s)) 
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s)) 
      args (tSort s').
  Proof.
    induction Δ using PCUICContexts.ctx_length_rev_ind in Γ, s, s', args, Δ' |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros wf cl sp.
    * rewrite app_context_nil_l in cl. len in sp.
      now rewrite app_context_nil_l in sp.
    * set (decl := d) in *.
      destruct d as [na [b|] ty]. simpl in sp; unfold mkProd_or_LetIn in sp; simpl in *.
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /= 
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        rewrite closedn_ctx_app in cl.
        move/andP:cl; rewrite closedn_ctx_app => [[/andP [cld clΓ0]] clΔ''].
        simpl in *. len in clΔ''.
        unfold closedn_ctx in cld. simpl in cld. rewrite andb_true_r /id in cld.
        rewrite Nat.add_0_r in cld.
        epose proof (typing_spine_letin_inv' wfΣ Γ na b ty (Γ0 ,,, Δ') _ _ _).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X. rewrite Nat.add_1_r in clΓ0 clΔ''. 
        rewrite app_context_assoc in wf. specialize (X wf).
        forward X. rewrite closedn_ctx_app clΓ0 /=. red. rewrite -clΔ''. lia_f_equal.
        len in X. rewrite app_context_assoc in sp.
        now specialize (X sp).
        rewrite app_context_assoc in wf. now eapply All_local_env_app_inv in wf as [? ?].
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /= 
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        rewrite closedn_ctx_app in cl.
        move/andP:cl; rewrite closedn_ctx_app => [[/andP [cld clΓ0]] clΔ''].
        simpl in *. len in clΔ''.
        unfold closedn_ctx in cld. simpl in cld. rewrite andb_true_r /id in cld.
        rewrite Nat.add_0_r in cld.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        epose proof (typing_spine_prod_inv wfΣ Γ na ty (Γ0 ,,, Δ') _ _ _).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        rewrite {3}(Nat.add_comm #|Δ'| #|Γ0|) in X0.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X. rewrite Nat.add_1_r in clΓ0 clΔ''. 
        rewrite app_context_assoc in wf. specialize (X wf).
        forward X. rewrite closedn_ctx_app clΓ0 /=. red. rewrite -clΔ''. lia_f_equal.
        len in X. rewrite app_context_assoc in sp.
        now specialize (X sp).
        rewrite app_context_assoc in wf. now eapply All_local_env_app_inv in wf as [? ?].
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ Δ Δ' Δ'' s args s' :
    wf_local Σ (Γ ,,, Δ) ->
    closedn_ctx 0 (Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (Δ ,,, Δ'') (tSort s)) 
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s)) 
      args (tSort s').
  Proof.
    intros.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen; eauto.
    eapply closedn_ctx_upwards; eauto. lia.
    rewrite closed_ctx_lift //.
  Qed.

  Lemma firstn_all_app_eq {A : Type} (n : nat) (l l' : list A) :
    n = #|l| -> firstn n (l ++ l') = l.
  Proof.
    intros ->.
    now rewrite -(Nat.add_0_r #|l|) firstn_app_2 firstn_0 // app_nil_r.
  Qed.

  Notation "'if' c 'then' vT 'else' vF" := 
    (match c with true => vT | false => vF end) 
    (at level 200, c, vT, vF at level 200, only parsing).

  Equations discr_prod_letin (t : term) : Prop :=
    discr_prod_letin (tProd _ _ _) := False ;
    discr_prod_letin (tLetIn _ _ _ _) := False ;
    discr_prod_letin _ := True.

  Variant prod_letin_view : term -> Type :=
  | prod_letin_tProd : forall na dom codom, prod_letin_view (tProd na dom codom)
  | prod_letin_tLetIn : forall na b ty t, prod_letin_view (tLetIn na b ty t) 
  | prod_letin_other : forall t, discr_prod_letin t -> prod_letin_view t.

  Equations prod_letin_viewc t : prod_letin_view t :=
    prod_letin_viewc (tProd na ty t) := prod_letin_tProd na ty t ;
    prod_letin_viewc (tLetIn na b ty t) := prod_letin_tLetIn na b ty t ;
    prod_letin_viewc t := prod_letin_other t I.

  Lemma welltyped_prod_inv {Σ : global_env_ext} {Γ na ty ty'} {wfΣ : wf Σ} :
    welltyped Σ Γ (tProd na ty ty') ->
    welltyped Σ Γ ty * welltyped Σ (Γ ,, vass na ty) ty'.
  Proof.
    intros [s [s1 [s2 [hty [hty' hcum]]]]%inversion_Prod]; auto.
    split; eexists; eauto.
  Qed.
  
  Lemma welltyped_letin_inv {Σ : global_env_ext} {Γ na b ty t} {wfΣ : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ ty * 
    welltyped Σ Γ b * 
    welltyped Σ (Γ ,, vdef na b ty) t.
  Proof.
    intros [s [s1 [s2 [hty [hdef [hty' hcum]]]]]%inversion_LetIn]; auto.
    split; [split|]; eexists; eauto.
  Qed.
  
  Lemma welltyped_letin_red {Σ : global_env_ext} {Γ na b ty t} {wfΣ : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ (subst0 [b] t).
  Proof.
    intros [s [s1 [s2 [hty [hdef [hty' hcum]]]]]%inversion_LetIn]; auto.
    exists (subst0 [b] s2).
    now eapply substitution_let in hty'.
  Qed.

  Section PositivityCheck.
    Context {Σ : global_env_ext}.
    Context {wfΣ : ∥ wf Σ ∥}.

    Obligation Tactic := Program.Tactics.program_simpl.

    Program Definition isRel (t : term) : typing_result (∑ n, t = tRel n) :=
      match t with
      | tRel k => ret (k; _)
      | _ => raise (Msg "isRel: not a variable")
      end.

    (** Positivity checking involves reducing let-ins, so it can only be applied to 
        already well-typed terms to ensure termination.

        We could also intersperse weak-head normalizations to reduce the types.
        This would need to be done in sync with a change in the spec in EnvironmentTyping though. *)

    Program Fixpoint check_positive_cstr_arg mdecl Γ t (wt : welltyped Σ Γ t) Δ
      {measure (Γ; t; wt) (@redp_subterm_rel cf Σ)} : typing_result (∥ positive_cstr_arg mdecl Δ t ∥) :=
      if closedn #|Δ| t then ret _ 
      else 
      match prod_letin_viewc t in prod_letin_view t' return t' = t -> _ with
      | prod_letin_tProd na ty t => fun eq =>
        posarg <- check_eq_true (closedn #|Δ| ty) (Msg "Non-positive occurrence.");;
        post <- check_positive_cstr_arg mdecl (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t => fun eq =>
        post <- check_positive_cstr_arg mdecl Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t nprodlet => fun eq =>
        let '(hd, args) := decompose_app t in
        '(hdrel; eqr) <- isRel hd ;;
        isind <- check_eq_true ((#|Δ| <=? hdrel) && (hdrel <? #|Δ| + #|ind_bodies mdecl|)) (Msg "Conclusion is not an inductive type") ;;
        (** Actually this is the only necessary check *)
        check_closed <- check_eq_true (forallb (closedn #|Δ|) args) (Msg "Conclusion arguments refer to the inductive type being defined") ;;
        match nth_error (List.rev mdecl.(ind_bodies)) (hdrel - #|Δ|) with
        | Some i => 
          check_eq_true (eqb (ind_realargs i) #|args|) (Msg "Partial application of inductive") ;;
          ret _
        | None => False_rect _ _
        end
      end eq_refl.

      Next Obligation. sq.
        now constructor; rewrite -Heq_anonymous.
      Qed.

      Next Obligation. 
        sq.
        clear check_positive_cstr_arg.
        apply (welltyped_prod_inv wt).
      Qed.
      
      Next Obligation.
        sq. right.
        unshelve eexists. repeat constructor. now reflexivity.
      Qed.

      Next Obligation.
        sq. constructor 4.
        now rewrite posarg.
        apply post.
      Qed.
      
      Next Obligation.
        sq.
        eapply (welltyped_letin_red wt).
      Qed.

      Next Obligation.
        sq; left. split; auto. repeat constructor.
      Qed.
      
      Next Obligation. sq.
        now constructor 3.
      Qed.

      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous1; eapply decompose_app_inv in Heq_anonymous1.
        subst t0. econstructor 2; eauto.
        now eapply eqb_eq in H.
      Qed.
      
      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous1; eapply decompose_app_inv in Heq_anonymous1.
        subst t0. symmetry in Heq_anonymous.
        eapply nth_error_None in Heq_anonymous.
        len in Heq_anonymous. lia.
      Qed.

      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm_rel; eauto.
      Defined.

    (** We already assume that constructor types are of the form `it_mkProd_or_LetIn (params,,, args) concl` so
        we don't need to recude further. *)
    Program Fixpoint check_positive_cstr mdecl n Γ t (wt : welltyped Σ Γ t) Δ
      { measure (Γ; t; wt) (@redp_subterm_rel cf Σ) }
      : typing_result (∥ positive_cstr mdecl n Δ t ∥) :=
      match prod_letin_viewc t in prod_letin_view t' return t' = t -> typing_result (∥ positive_cstr mdecl n Δ t ∥) with 
      | prod_letin_tProd na ty t => fun eq =>
        posarg <- check_positive_cstr_arg mdecl Γ ty _ Δ ;;
        post <- check_positive_cstr mdecl n (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t => fun eq =>
        (* Do reduction *)
        post <- check_positive_cstr mdecl n Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t Ht => fun eq =>
        let '(hd, indices) := decompose_app t in
        eqhd <- check_eq_true (eqb hd (tRel (#|ind_bodies mdecl| - S n + #|Δ|)))
          (Msg "Conclusion of constructor is not the right inductive type") ;;
          (* actually impossible with prior typing checks. *)
        closedargs <- check_eq_true (forallb (closedn #|Δ|) indices)
          (Msg "Arguments of the inductive in the conclusion of a constructor mention the inductive itself");;
        ret _
      end eq_refl.
  
      Next Obligation.
        sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        sq. right. unshelve eexists. repeat constructor. reflexivity.
      Qed.
      Next Obligation.
        sq. constructor 3; eauto.
      Qed.
      Next Obligation.
        sq. eapply (welltyped_letin_red wt).
      Qed.
      Next Obligation.
        sq. left. repeat constructor.
      Qed.
      Next Obligation.
        sq. now constructor 2.
      Qed.
      Next Obligation.
        sq. rename Heq_anonymous into eqa.
        symmetry in eqa; eapply decompose_app_inv in eqa.
        subst t0.
        move: eqhd; case: eqb_spec => // -> _.
        constructor.
        now eapply forallb_All in closedargs.
      Qed.
      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm_rel; eauto.
      Qed.
  End PositivityCheck.

  Section MonadAllAll.
    Context {T} {M : Monad T} {A} {P : A -> Type} {Q} (f : forall x, ∥ Q x ∥ -> T (∥ P x ∥)).
    Program Fixpoint monad_All_All l : ∥ All Q l ∥ -> T (∥ All P l ∥) := 
      match l return ∥ All Q l ∥ -> T (∥ All P l ∥) with
       | [] => fun _ => ret (sq All_nil)
       | a :: l => fun allq => 
        X <- f a _ ;;
        Y <- monad_All_All l _ ;;
        ret _
       end.
    Next Obligation. sq.
      now depelim allq.
    Qed.
    Next Obligation.
      sq; now depelim allq.
    Qed.
    Next Obligation.
      sq. constructor; assumption.
    Defined.
  End MonadAllAll.

  (* Does not work due to implicit arguments I guess  
    Coercion isType_welltyped : isType >-> welltyped. *)

  Lemma forallb_unfold {A} (f : A -> bool) (g : nat -> A) n : 
    (forall x, x < n -> f (g x)) ->
    forallb f (PCUICUnivSubstitution.unfold n g).
  Proof.
    intros fg.
    induction n; simpl; auto.
    rewrite forallb_app IHn //.
    intros x lt; rewrite fg //. lia.
    rewrite /= fg //.
  Qed.

  Lemma In_Var_global_ext_poly {n Σ inst cstrs} : 
    n < #|inst| ->
    LevelSet.mem (Level.Var n) (global_ext_levels (Σ, Polymorphic_ctx (inst, cstrs))).
  Proof.
    intros Hn.
    unfold global_ext_levels; simpl.
      apply LevelSet.mem_spec; rewrite LevelSet.union_spec. left.
    rewrite /AUContext.levels /= PCUICUnivSubstitution.mapi_unfold.
    apply LevelSetProp.of_list_1, InA_In_eq.
    eapply In_unfold_var. exists n. intuition auto.
  Qed.

  
  Lemma on_udecl_poly_bounded Σ inst cstrs :
    wf Σ ->
    on_udecl Σ (Polymorphic_ctx (inst, cstrs)) ->
    closedu_cstrs #|inst| cstrs.
  Proof.
    rewrite /on_udecl. intros wfΣ [_ [nlevs _]].
    red.
    rewrite /closedu_cstrs.
    intros x incstrs. simpl in nlevs.
    specialize (nlevs x incstrs).
    destruct x as [[l1 p] l2].
    destruct nlevs.
    apply LevelSetProp.Dec.F.union_1 in H.
    apply LevelSetProp.Dec.F.union_1 in H0.
    destruct H. eapply LSet_in_poly_bounded in H.
    destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
    now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H => //. simpl.
    destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
    now rewrite H H0.
  Qed.
 
  Lemma subst_instance_level_lift inst l : 
    closedu_level #|inst| l ->
    subst_instance_level (lift_instance #|inst| (level_var_instance 0 inst)) l = lift_level #|inst| l.
  Proof.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite nth_nth_error.
    destruct nth_error eqn:eq. move:eq.
    rewrite nth_error_map /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
    simpl. now intros [=].
    eapply nth_error_None in eq. len in eq. lia.
  Qed.
  
  Lemma subst_instance_level_var_instance inst l : 
    closedu_level #|inst| l ->
    subst_instance_level (level_var_instance 0 inst) l = l.
  Proof.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite /level_var_instance.
    rewrite nth_nth_error.
    now rewrite /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
  Qed.

  Lemma variance_universes_spec Σ ctx v univs u u' : 
    wf_ext (Σ, ctx) ->
    wf_ext (Σ, univs) ->
    variance_universes ctx v = Some (univs, u, u') ->
    consistent_instance_ext (Σ, univs) ctx u * 
    consistent_instance_ext (Σ, univs) ctx u'.
  Proof.
    intros wfctx wfext.
    unfold variance_universes. destruct ctx as [|[inst cstrs]] => //.
    intros [= eq].
    set (vcstrs := ConstraintSet.union _ _) in *.
    subst univs. simpl.
    subst u u'. len.
    repeat (split; auto).
    - rewrite forallb_map /level_var_instance.
      rewrite [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx. apply In_Var_global_ext_poly. len. lia.
    - destruct wfext as [onΣ onu]. simpl in *.
      destruct onu as [_ [_ [_ sat]]].
      do 2 red in sat.
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite ConstraintSet.union_spec; left.
      rewrite /vcstrs !ConstraintSet.union_spec.
      left. right.
      rewrite In_lift_constraints.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x. eexists. unfold subst_instance_cstr.
      unfold lift_constraint. split; eauto. destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr].
      rewrite !subst_instance_level_lift //.
    - rewrite /level_var_instance.
      rewrite [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx. apply In_Var_global_ext_poly. len. lia.
    - destruct wfext as [onΣ onu]. simpl in *.
      destruct onu as [_ [_ [_ sat]]].
      do 2 red in sat.
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite ConstraintSet.union_spec; left.
      rewrite /vcstrs !ConstraintSet.union_spec.
      left. left.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x.
      destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr]. rewrite /subst_instance_cstr /=.
      rewrite !subst_instance_level_var_instance //.
    Qed.

  Program Fixpoint check_wf_local (Σ : wf_env_ext) Γ : typing_result (∥ wf_local Σ Γ ∥) :=
    match Γ with
    | [] => ret (sq localenv_nil)
    | {| decl_body := Some b; decl_type := ty |} :: Γ => 
      wfΓ <- check_wf_local Σ Γ ;;
      wfty <- check_type_wf_env Σ Γ wfΓ b ty ;;
      ret _
    | {| decl_body := None; decl_type := ty |} :: Γ =>
      wfΓ <- check_wf_local Σ Γ ;;
      wfty <- infer_type_wf_env Σ Γ wfΓ ty ;;
      ret _
    end.
    Next Obligation.
      destruct Σ as [Σ wfΣ G' wfG']; simpl in *.
      sq. constructor; auto.
      eapply validity_term in wfty. apply wfty. auto.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G' wfG']; simpl in *.
      sq. constructor; auto. now exists wfty.
    Qed.

  Definition wt_indices Σ mdecl indices cs :=
    wf_local Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cshape_args)) *
    ctx_inst Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cshape_args)) 
      (cs.(cshape_indices)) (List.rev (lift_context #|cs.(cshape_args)| 0 indices)).

  Lemma ctx_inst_wt Σ Γ s Δ : 
    ctx_inst Σ Γ s Δ ->
    Forall (welltyped Σ Γ) s.
  Proof.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

  Lemma type_smash {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ t T} : 
    Σ ;;; Γ ,,, Δ |- t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ t : expand_lets Δ T.
  Proof.
    revert Γ t T.
    induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl; auto.
    - intros. now rewrite! PCUICCanonicity.expand_lets_nil.
    - intros Γ t T h.
      rewrite !smash_context_app_def !expand_lets_vdef.
      eapply X. now len.
      eapply substitution; eauto.
      2:{ now rewrite app_context_assoc in h. }
      rewrite -{1}(subst_empty 0 b). repeat constructor.
      rewrite !subst_empty.
      eapply typing_wf_local in h.
      rewrite app_context_assoc in h. eapply All_local_env_app_inv in h as [h _].
      now depelim h.
    - intros Γ t T h.
      rewrite !smash_context_app_ass !expand_lets_vass.
      rewrite app_context_assoc. eapply X. lia.
      now rewrite app_context_assoc in h.
  Qed.

  Lemma sub_context_set_empty Σ : sub_context_set ContextSet.empty (global_context_set Σ).
  Proof.
    split; simpl.
    intros x hin. now eapply LS.empty_spec in hin.
    intros x hin. now eapply CS.empty_spec in hin.
  Qed.

  Lemma cumul_ctx_rel_close' Σ Γ Δ Δ' : 
    cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    cumul_ctx_rel Σ Γ Δ Δ'.
  Proof.
    intros H.
    eapply context_relation_app in H as [cumΓ cumΔs]; auto.
    eapply context_relation_length in H. len in H. lia.
  Qed.

  Lemma eq_decl_eq_decl_upto (Σ : global_env_ext) x y : 
    eq_decl true Σ Σ x y ->
    eq_decl_upto Σ (eq_universe Σ) (leq_universe Σ) x y.
  Proof.
    destruct x, y; simpl; constructor; simpl in *; auto.
    destruct X as [[eqann H1] H2]; simpl in *. repeat split; auto.
    destruct decl_body, decl_body0; simpl in *; try constructor; auto.
    destruct X as [[eqann H1] H2]; simpl in *. repeat split; auto.
  Qed.

  Lemma eq_decl_upto_refl (Σ : global_env_ext) x : eq_decl_upto Σ (eq_universe Σ) (leq_universe Σ) x x.
  Proof.
    destruct x as [na [b|] ty]; constructor; simpl; auto.
    split; constructor; reflexivity. reflexivity.
    split; constructor; reflexivity. reflexivity.
  Qed.
  Lemma leq_context_cumul_context (Σ : global_env_ext) Γ Δ Δ' : 
    eq_context true Σ Σ Δ Δ' ->
    cumul_ctx_rel Σ Γ Δ Δ'.
  Proof.
    intros eqc.
    apply cumul_ctx_rel_close'.
    apply eq_context_upto_univ_cumul_context.
    apply All2_eq_context_upto.
    eapply All2_app.
    eapply All2_impl; eauto.
    intros; now eapply eq_decl_eq_decl_upto.
    eapply All2_refl. intros. simpl. eapply (eq_decl_upto_refl Σ).
  Qed.

  Program Definition check_cstr_variance (Σ : wf_env) mdecl (id : kername) indices
    (mdeclvar : check_variance mdecl.(ind_universes) mdecl.(ind_variance) = true) cs 
    (wfΣ : ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (wfΓ : ∥ wt_indices (Σ, ind_universes mdecl) mdecl indices cs ∥) :
    EnvCheck (∥ forall v : list Variance.t,
                    mdecl.(ind_variance) = Some v ->
                    cstr_respects_variance Σ mdecl v cs ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v => 
      let univs := ind_universes mdecl in
      match variance_universes univs v with          
      | Some ((univs0, u), u') => 
        '(exist wfext eq) <- make_wf_env_ext Σ id univs0 ;;
        (* Incompleteness: this is an underapproximation of cumulativity of the contexts: 
           in general we should allow unfolding and reduction to happen before comparing the types of arguments.
           However in many cases it will be sufficient. E.g. for lists and regular structures this is enough 
           to check variance.

           Note that both contexts are well-typed in different contexts: 
           ind_arities@{u} ,,, params@{u} for args@{u} and
           ind_arities@{u'} ,,, params@{u'} for args@{u'}. 
           
           Hence we cannot use check_cumul_ctx here to verify the variance up-to conversion: the terms to be 
           converted would be in different, incompatible contexts.

           TODO: do as in Coq's kernel and implement a routine that takes whnfs of both sides and compare
           syntactically the heads. *)
        check_args <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_context true wfext 
            (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cshape_args cs))))
            (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] (cshape_args cs))))) ;;
        check_indices <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_terms false wfext
            (map (subst_instance_constr u ∘ expand_lets (ind_params mdecl ,,, cs.(cshape_args))) (cshape_indices cs))
            (map (subst_instance_constr u' ∘ expand_lets (ind_params mdecl ,,, cs.(cshape_args))) (cshape_indices cs))) ;;
        ret _
      | None => False_rect _ _
      end
    end.

    Next Obligation.
      sq. by [].
    Qed.

    Next Obligation.
      destruct pat as [Σ' wfΣ' G wfG]; simpl in *. subst Σ'.
      clear eq.
      destruct Σ as [Σ [wfΣ''] G' wfG']; simpl in *. sq.
      intros v0 [= <-].
      red. rewrite -Heq_anonymous1.
      split; auto.
      now apply leq_context_cumul_context.
      clear check_args.
      eapply All2_impl. eauto. simpl; intros.
      now constructor.
    Qed.
    Next Obligation.
      unfold variance_universes in Heq_anonymous.
      unfold check_variance in mdeclvar.
      rewrite -Heq_anonymous0 in mdeclvar.
      destruct ind_universes as [|[]] => //.
    Qed.

  Lemma wt_cstrs {Σ : wf_env_ext} {n mdecl cstrs cs} :
    ∥ All2
      (fun (cstr : (ident × term) × nat) (cs0 : constructor_shape) =>
      check_constructor_spec Σ n mdecl cstr cs0) cstrs cs ∥ -> 
    ∥ All (fun cstr => welltyped Σ (arities_context mdecl.(ind_bodies)) cstr.1.2) cstrs ∥.
  Proof.
    intros; sq.
    solve_all. simpl.
    destruct X as [[[isTy _] _] _]. simpl in isTy. 
    apply (isType_welltyped isTy).
  Qed.
  
  Lemma get_wt_indices {Σ : wf_env_ext} {mdecl cstrs cs}
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (n : nat) (idecl : one_inductive_body) (indices : context)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl)    
    (heq : ∥ ∑ inds, idecl.(ind_type) = it_mkProd_or_LetIn (mdecl.(ind_params) ,,, indices) (tSort inds) ∥) :
    ∥ All2
      (fun (cstr : (ident × term) × nat) (cs0 : constructor_shape) =>
      check_constructor_spec Σ (S n) mdecl cstr cs0) cstrs cs ∥ -> 
    ∥ All (fun cs => wt_indices Σ mdecl indices cs) cs ∥.
  Proof.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. destruct wfΣ.
    intros; sq.
    solve_all. simpl.
    destruct X as [[[isTy eq] sorts] eq']. simpl in *.
    assert(wf_local Σ (ind_params mdecl,,, indices)).
    { eapply nth_error_all in wfar; eauto. simpl in wfar.
      destruct heq as [s Hs]. rewrite Hs in wfar.
      eapply isType_it_mkProd_or_LetIn_wf_local in wfar.
      now rewrite app_context_nil_l in wfar. auto. }
    red. rewrite eq in isTy.
    eapply isType_it_mkProd_or_LetIn_inv in isTy; auto.
    eapply isType_mkApps_inv in isTy as [fty [s [Hf Hsp]]]; auto.
    eapply inversion_Rel in Hf as [decl [wfctx [Hnth cum]]]; auto.
    rewrite nth_error_app_ge in Hnth. lia.
    split. now rewrite app_context_assoc in wfctx.
    replace (#|ind_params mdecl,,, cshape_args y| + (#|ind_bodies mdecl| - S n) -
    #|ind_params mdecl,,, cshape_args y|) with (#|ind_bodies mdecl| - S n) in Hnth by lia.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev in hnth => //.
    eapply nth_error_arities_context in hnth. rewrite Hnth in hnth.
    noconf hnth; simpl in *. clear Hnth.
    eapply PCUICSpine.typing_spine_strengthen in Hsp; eauto.
    clear cum.
    destruct heq as [inds eqind].
    move: Hsp. rewrite eqind.
    rewrite lift_it_mkProd_or_LetIn /= => Hs.
    rewrite closed_ctx_lift in Hs. eapply PCUICClosed.closed_wf_local; eauto.
    rewrite app_context_assoc in Hs wfctx.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv in Hs; auto.
    2:{ eapply PCUICWeakening.weaken_wf_local; pcuic.
        now eapply wf_ind_types_wf_arities. }
    2:{ eapply PCUICClosed.closed_wf_local; eauto. }
    eapply typing_spine_it_mkProd_or_LetIn_inv in Hs => //. auto.
    eapply weakening_wf_local; eauto.
    rewrite -app_context_assoc.
    eapply PCUICWeakening.weaken_wf_local; eauto.
    now eapply wf_ind_types_wf_arities.
  Qed.

  Program Definition check_constructors (Σ0 : wf_env) (Σ : wf_env_ext) (id : kername) (mdecl : mutual_inductive_body)
    (HΣ : Σ.(wf_env_ext_env) = (Σ0, ind_universes mdecl))
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (mdeclvar : check_variance mdecl.(ind_universes) mdecl.(ind_variance) = true)    
    (n : nat) (idecl : one_inductive_body) (indices : context)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl)
    (heq : ∥ ∑ inds, idecl.(ind_type) = it_mkProd_or_LetIn (mdecl.(ind_params) ,,, indices) (tSort inds) ∥)
    : EnvCheck (∑ cs : list constructor_shape,
      ∥ on_constructors (lift_typing typing) Σ mdecl n idecl indices (ind_ctors idecl) cs ∥) :=
    
    '(cs; Hcs) <- constructor_shapes Σ (string_of_kername id) mdecl wfar wfpars (S n) idecl.(ind_ctors) ;;
    posc <- wrap_error Σ (string_of_kername id)
      (monad_All_All (fun x px => @check_positive_cstr Σ (wf_env_ext_sq_wf Σ) mdecl n (arities_context mdecl.(ind_bodies)) x.1.2 _ []) 
        idecl.(ind_ctors) (wt_cstrs Hcs)) ;;
    var <- monad_All_All (fun cs px => check_cstr_variance Σ0 mdecl id indices mdeclvar cs _ _) cs 
      (get_wt_indices wfar wfpars n idecl indices hnth heq Hcs) ;;
    ret (cs; _).
      
  Next Obligation. now sq. Qed.
  Next Obligation. apply wf_env_ext_wf. Qed.
  
  Next Obligation.
    epose proof (get_wt_indices wfar wfpars _ _ _ hnth heq Hcs).
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. clear X.
    subst Σ; simpl in *. unfold check_constructor_spec in Hcs; simpl in *. sq.
    solve_all.
    eapply All2_impl; eauto. simpl.
    intros. destruct X as [[posc [[[isTy eq] sorts] eq']] [[wfargs wtinds] wfvar]].
    assert(wf_local (Σ0.(wf_env_env), ind_universes mdecl) (ind_params mdecl,,, indices)).
    { eapply nth_error_all in wfar; eauto. simpl in wfar.
      destruct heq as [s Hs]. rewrite Hs in wfar.
      eapply isType_it_mkProd_or_LetIn_wf_local in wfar.
      now rewrite app_context_nil_l in wfar. auto. }
    econstructor => //.
    unfold cdecl_type. rewrite eq.
    rewrite it_mkProd_or_LetIn_app. autorewrite with len. lia_f_equal.
  Qed.

  Definition check_projections_type (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
  (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_shape) :=
    ind_projs idecl <> [] ->
    match cs return Type with
    | [cs] => on_projections mdecl mind i idecl indices cs
    | _ => False
    end.

  Program Definition check_projection (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) 
    (cs : constructor_shape) 
    (oncs : ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices idecl.(ind_ctors) [cs] ∥) 
    (k : nat) (p : ident × term) (hnth : nth_error idecl.(ind_projs) k = Some p)
    (heq : #|idecl.(ind_projs)| = context_assumptions cs.(cshape_args))
    : typing_result (∥ on_projection mdecl mind i cs k p ∥) :=
    let Γ :=  smash_context [] (cs.(cshape_args) ++ ind_params mdecl) in
    match nth_error Γ (context_assumptions (cs.(cshape_args)) - S k) with
    | Some decl =>
      let u := abstract_instance (ind_universes mdecl) in
      let ind := {| inductive_mind := mind; inductive_ind := i |} in
      check_na <- check_eq_true (eqb (binder_name (decl_name decl)) (nNamed p.1)) 
        (Msg "Projection name does not match argument binder name");;
      check_eq <- check_eq_true (eqb p.2
          (subst (inds mind u (ind_bodies mdecl)) (S (ind_npars mdecl))
          (subst0 (projs ind (ind_npars mdecl) k) (lift 1 k (decl_type decl)))))
        (Msg "Projection type does not match argument type") ;;
      ret _
    | None => False_rect _ _
    end.
  Next Obligation.
    eapply eqb_eq in check_na.
    eapply eqb_eq in check_eq.
    sq.
    red. rewrite -Heq_anonymous. simpl. split; auto. 
  Qed.
  Next Obligation.
    sq. depelim oncs. depelim oncs.
    rename Heq_anonymous into hnth'.
    symmetry in hnth'. eapply nth_error_None in hnth'.
    eapply nth_error_Some_length in hnth.
    len in hnth'. lia.
  Qed.

  Program Definition check_projections_cs (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) 
    (cs : constructor_shape) 
    (oncs : ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices idecl.(ind_ctors) [cs] ∥) : 
    typing_result (∥ on_projections mdecl mind i idecl indices cs ∥) :=
    check_indices <- check_eq_true (eqb [] indices) (Msg "Primitive records cannot have indices") ;;
    check_elim <- check_eq_true (eqb (ind_kelim idecl) IntoAny) (Msg "Primitive records must be eliminable to Type");;
    check_length <- check_eq_true (eqb #|idecl.(ind_projs)| (context_assumptions cs.(cshape_args)))
      (Msg "Invalid number of projections") ;;
    check_projs <- monad_Alli_nth idecl.(ind_projs) 
      (fun n p hnth => check_projection Σ mind mdecl i idecl indices cs oncs n p hnth (eqb_eq _ _ check_length)) ;;
    ret _.

    Next Obligation.
      sq.
      depelim oncs. depelim oncs.
      eapply eqb_eq in check_indices; subst indices.
      eapply eqb_eq in check_elim. eapply eqb_eq in check_length.
      constructor => //.
      now rewrite H.
    Qed.

  Program Definition check_projections (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_shape) :
    ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices idecl.(ind_ctors) cs ∥ -> 
    typing_result (∥ check_projections_type Σ mind mdecl i idecl indices cs ∥) :=
    match ind_projs idecl with
    | [] => fun _ => ret _
    | _ => 
      match cs with
      | [ cs ] => fun oncs => ccs <- check_projections_cs Σ mind mdecl i idecl indices cs oncs ;; 
        ret _
      | _ => fun oncs => raise (Msg "Projections can only be declared for an inductive type with a single constructor")
      end
    end.
  Next Obligation.
    rename Heq_anonymous into eqp. 
    sq. red. rewrite -eqp. congruence.
  Qed.
  Next Obligation.
    sq. red. intros. auto.
  Qed.

  Definition checkb_constructors_smaller (G : universes_graph) (cs : list constructor_shape) (ind_sort : Universe.t) :=
    List.forallb (fun cs => List.forallb (fun argsort => check_leqb_universe G argsort ind_sort) cs.(cshape_sorts)) cs.

  Lemma forallbP_cond {A} (P Q : A -> Prop) (p : A -> bool) l : 
    Forall Q l ->
    (forall x, Q x -> reflect (P x) (p x)) -> reflect (Forall P l) (forallb p l).
  Proof.
    intros HQ Hp.
    apply: (iffP idP).
    - induction HQ; rewrite /= //. move/andP => [pa pl].
      constructor; auto. now apply/(Hp _).
    - induction HQ; intros HP; depelim HP; rewrite /= // IHHQ // andb_true_r.
      now apply/(Hp _).
  Qed.

  Lemma check_constructors_smallerP (Σ : wf_env_ext) cs ind_sort : 
    Forall (fun cs => Forall (wf_universe Σ) cs.(cshape_sorts)) cs -> wf_universe Σ ind_sort ->
    ∥ reflect (check_constructors_smaller Σ cs ind_sort) (checkb_constructors_smaller Σ cs ind_sort) ∥.
  Proof.
    unfold check_constructors_smaller, checkb_constructors_smaller.
    intros wfcs wfind.
    destruct Σ as [Σ wfΣ G wfG]. simpl in *. sq.
    eapply forallbP_cond; eauto. clear wfcs.
    simpl; intros c wfc.
    pose proof (check_leqb_universe_spec' G (global_ext_uctx Σ)).
    forward H. apply wf_ext_global_uctx_invariants; auto.
    forward H. apply wfΣ.
    eapply forallbP_cond; eauto. simpl. intros x wfx.
    specialize (H wfG x ind_sort). simpl.
    destruct check_leqb_universe eqn:eq; constructor.
    now simpl in H.
    intro. simpl in H.
    pose proof (check_leqb_universe_complete G (global_ext_uctx Σ)).
    forward H1. apply wf_ext_global_uctx_invariants. now sq.
    forward H1. apply wfΣ.
    specialize (H1 wfG x ind_sort). simpl in H1.
    forward H1.
    red in wfx. destruct x; auto.
    forward H1.
    red in wfind. destruct ind_sort; auto.
    specialize (H1 H0). congruence.
  Qed.

  Definition wf_cs_sorts (Σ : wf_env_ext) cs := 
    Forall (fun cs => Forall (wf_universe Σ) cs.(cshape_sorts)) cs.

  Program Definition do_check_ind_sorts (Σ : wf_env_ext) (params : context) (wfparams : ∥ wf_local Σ params ∥) 
    (kelim : allowed_eliminations) (indices : context) 
    (cs : list constructor_shape) 
    (wfcs : wf_cs_sorts Σ cs)
    (ind_sort : Universe.t) 
    (wfi : wf_universe Σ ind_sort): 
    typing_result (∥ check_ind_sorts (lift_typing typing) Σ params kelim indices cs ind_sort ∥) := 
    match ind_sort with
    | Universe.lSProp => 
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_sprop_ind cs)) 
        (Msg "Incorrect allowed_elimination for inductive") ;; 
      ret _
    | Universe.lProp => 
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_prop_ind cs)) 
        (Msg "Incorrect allowed_elimination for inductive") ;; ret _
    | Universe.lType u => 
      check_eq_true (checkb_constructors_smaller Σ cs ind_sort) 
        (Msg ("Incorrect inductive sort: The constructor arguments universes are not smaller than the declared inductive sort")) ;;
      match indices_matter with
      | true =>
        tyloc <- check_type_local_ctx Σ params indices ind_sort wfparams ;;
        ret _
      | false => ret _
      end
    end.

    Next Obligation.
      unfold check_ind_sorts. simpl. 
      now rewrite H.
    Qed.
    Next Obligation.
      unfold check_ind_sorts. 
      now rewrite H.
    Qed.
    Next Obligation.
      unfold check_ind_sorts. simpl.
      pose proof (check_constructors_smallerP Σ cs u wfcs wfi).
      sq. split. destruct H0 => //.
      destruct indices_matter; auto.
    Qed.
    Next Obligation.
      unfold check_ind_sorts; simpl.
      pose proof (check_constructors_smallerP Σ cs u wfcs wfi).
      sq. split. destruct H0 => //. now rewrite -Heq_anonymous.
    Qed.

  Lemma sorts_local_ctx_wf_sorts (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ s : 
    sorts_local_ctx (lift_typing typing) Σ Γ Δ s ->
    Forall (wf_universe Σ) s.
  Proof.
    induction Δ in s |- *; destruct s; simpl; auto.
    destruct a as [na [b|] ty].
    - intros []. eauto.
    - intros []; eauto. constructor; eauto.
      now eapply typing_wf_universe in t0.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify.

  Program Definition check_indices (Σ : wf_env) mdecl (id : kername)
    (wfΣ : ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (mdeclvar : check_variance mdecl.(ind_universes) mdecl.(ind_variance) = true)
    indices (wfΓ : ∥ wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, indices) ∥) :
    EnvCheck (∥ forall v : list Variance.t,
                    mdecl.(ind_variance) = Some v ->
                    ind_respects_variance Σ mdecl v indices ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v => 
      let univs := ind_universes mdecl in
      match variance_universes univs v with          
      | Some ((univs0, u), u') => 
        '(exist wfext eq) <- make_wf_env_ext Σ id univs0 ;;
        checkctx <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_context true wfext
            (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
            (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))) ;;
        ret _
      | None => False_rect _ _
      end
    end.
  Next Obligation.
    sq. discriminate.
  Qed.
  Next Obligation. 
    clear H.
    destruct pat as [Σ' wfΣ' G wfG]. simpl in *. subst Σ'.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous1 into eqvaru.
    sq. intros ? [= <-]. red. simpl.
    rewrite -eqvaru.
    unfold variance_universes in eqvaru.
    unfold check_variance in mdeclvar.
    rewrite -eqvar in mdeclvar.
    destruct (ind_universes mdecl) as [|[inst cstrs]] => //.
    now eapply leq_context_cumul_context.
  Qed.

  Next Obligation.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous into eqvaru.
    unfold variance_universes in eqvaru.
    unfold check_variance in mdeclvar.
    rewrite -eqvar in mdeclvar.
    destruct (ind_universes mdecl) as [|[inst cstrs]] => //.
  Qed.

  Program Definition check_ind_types (Σ : wf_env_ext) (mdecl : mutual_inductive_body)
      : EnvCheck (∥ wf_ind_types Σ mdecl ∥) :=
    indtys <- monad_All (fun ind => wrap_error Σ ind.(ind_name) (infer_type_wf_env Σ [] wfnil ind.(ind_type))) mdecl.(ind_bodies) ;;
    ret _.
    Next Obligation.
      eapply All_sigma in indtys as [indus Hinds].
      eapply All2_sq in Hinds. sq.
      red.
      solve_all. now exists y.
    Qed.

  Program Definition check_one_ind_body (Σ0 : wf_env) (Σ : wf_env_ext) 
      (mind : kername) (mdecl : mutual_inductive_body)
      (pf : Σ.(wf_env_ext_env) = (Σ0.(wf_env_env), mdecl.(ind_universes)))
      (wfpars : ∥ wf_local Σ mdecl.(ind_params) ∥)
      (wfars : ∥ wf_ind_types Σ mdecl ∥)
      (mdeclvar : check_variance mdecl.(ind_universes) mdecl.(ind_variance) = true)
      (i : nat) (idecl : one_inductive_body)
      (hnth : nth_error mdecl.(ind_bodies) i = Some idecl)
      : EnvCheck (∥ on_ind_body (lift_typing typing) Σ mind mdecl i idecl ∥) :=
      let id := string_of_kername mind in
      '(ctxinds; p) <-
        wrap_error Σ id ((match destArity [] idecl.(ind_type) as da return da = destArity [] idecl.(ind_type) -> typing_result (∑ ctxs, idecl.(ind_type) = it_mkProd_or_LetIn ctxs.1 (tSort ctxs.2)) with
        | Some (ctx, s) => fun eq => ret ((ctx, s); _)
        | None => fun _ => raise (NotAnArity idecl.(ind_type))
        end eq_refl)) ;;
      let '(indices, params) := split_at (#|ctxinds.1| - #|mdecl.(ind_params)|) ctxinds.1 in
      eqpars <- wrap_error Σ id 
        (check_eq_true (eqb params mdecl.(ind_params)) 
        (Msg "Inductive arity parameters do not match the parameters of the mutual declaration"));;
      '(cs; oncstrs) <- (check_constructors Σ0 Σ mind mdecl pf wfars wfpars mdeclvar i idecl indices hnth _) ;;
      onprojs <- wrap_error Σ ("Checking projections of " ^ id)
       (check_projections Σ mind mdecl i idecl indices cs oncstrs) ;;
      onsorts <- wrap_error Σ ("Checking universes of " ^ id)
        (do_check_ind_sorts Σ mdecl.(ind_params) wfpars idecl.(ind_kelim) indices cs _ ctxinds.2 _) ;;
      onindices <- (check_indices Σ0 mdecl mind _ mdeclvar indices _) ;;
      ret (let 'sq wfars := wfars in 
        let 'sq wfext := Σ.(wf_env_ext_wf) in
        let 'sq oncstrs := oncstrs in
        let 'sq onprojs := onprojs in
        let 'sq onindices := onindices in
        let 'sq onsorts := onsorts in
        (sq 
        {| ind_indices := indices; ind_sort := ctxinds.2; 
           ind_arity_eq := _; onArity := _;
           ind_cshapes := cs;
           onConstructors := oncstrs;
           onProjections := onprojs;
           ind_sorts := onsorts; 
           onIndices := _ |})).
  Next Obligation. 
    symmetry in eq.
    apply destArity_spec_Some in eq. now simpl in eq.
  Qed.

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    sq. exists t0.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    rewrite split_at_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    rewrite {1}H. now rewrite [_ ,,, _]firstn_skipn.
  Qed.
  
  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    sq. red. simpl. red in X. solve_all.
    destruct X.
    now eapply sorts_local_ctx_wf_sorts in on_cargs.
  Qed. 

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
    eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs]. red in Hs.
    clear X0; rewrite p in Hs.
    eapply (* todo fix clash *) PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
    now eapply inversion_Sort in Hs as [_ [wf _]].
  Qed. 

  Next Obligation.
    apply wf_env_ext_wf.
  Qed.
  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
    clear onprojs onsorts X.
    red in wfars. eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs].
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    red in Hs.
    rewrite split_at_firstn_skipn in Heq_anonymous1. noconf Heq_anonymous1.
    rewrite {1}H; autorewrite with len. rewrite [_ ,,, _]firstn_skipn.
    rewrite X0 in Hs.
    eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
    eapply typing_wf_local in Hs. now rewrite app_context_nil_l in Hs.
  Qed.

  Next Obligation.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    sq.
    eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs]. red in Hs.
    rewrite split_at_firstn_skipn in Heq_anonymous1. noconf Heq_anonymous1.
    rewrite p H; autorewrite with len. simpl.
    rewrite List.skipn_length.
    replace (#|l0| - (#|l0| - (#|l0| - #|ind_params mdecl|))) with (#|l0| - #|ind_params mdecl|) by lia.
    rewrite -it_mkProd_or_LetIn_app.
    rewrite /app_context firstn_skipn. reflexivity.
  Qed.
  
  Next Obligation.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    red. red.
    eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs]. red in Hs. now exists s.
  Qed.

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    subst Σ; simpl in *.
    now apply onindices.
  Qed.

  Program Definition check_wf_decl (Σ0 : wf_env) (Σ : global_env_ext)  HΣ HΣ' G HG
             kn (d : global_decl) (eq : Σ = (Σ0, universes_decl_of_decl d))
    : EnvCheck (∥ on_global_decl (lift_typing typing) Σ kn d ∥) :=
    match d with
    | ConstantDecl cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement kn Σ HΣ HΣ' G HG term cst.(cst_type) ;; ret _
      | None => check_wf_type kn Σ HΣ HΣ' G HG cst.(cst_type) ;; ret _
      end
    | InductiveDecl mdecl =>
      let wfΣ : wf_env_ext := {| wf_env_ext_env := Σ; wf_env_ext_wf := _; 
        wf_env_ext_graph := G; wf_env_ext_graph_wf := HG |} in
      let id := string_of_kername kn in
      X5 <- wrap_error Σ id (check_eq_true (check_variance mdecl.(ind_universes) mdecl.(ind_variance)) (Msg "variance"));;
      X2 <- wrap_error Σ id (check_context HΣ HΣ' G HG (ind_params mdecl)) ;;
      X3 <- wrap_error Σ id (check_eq_nat (context_assumptions (ind_params mdecl))
                                       (ind_npars mdecl)
                                       (Msg "wrong number of parameters")) ;;
      onarities <- check_ind_types wfΣ mdecl ;;
      X1 <- monad_Alli_nth mdecl.(ind_bodies) (fun i oib Hoib => check_one_ind_body Σ0 wfΣ kn mdecl eq X2 onarities X5 i oib Hoib);;
      X4 <- wrap_error Σ id (check_eq_true (ind_guard mdecl) (Msg "guard"));;
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
  Next Obligation.
    simpl. reflexivity.
  Qed.
  Fail Next Obligation.

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
        let wfΣ : wf_env := {| wf_env_env := Σ; wf_env_graph := G.π1 |} in
        check_fresh d.1 Σ ;;
        let udecl := universes_decl_of_decl d.2 in
        uctx <- check_udecl (string_of_kername d.1) Σ _ G.π1 (proj1 G.π2) udecl ;;
        let G' := add_uctx uctx.π1 G.π1 in
        check_wf_decl wfΣ (Σ, udecl) _ _ G' _ d.1 d.2 _ ;;
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

  Definition check_type_wf_env_bool (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : bool :=
    match check_type_wf_env Σ Γ wfΓ t T with
    | Checked _ => true
    | TypeError e => false
    end.
  
  Definition check_wf_env_bool_spec (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = true -> ∥ Σ ;;; Γ |- t : T ∥.
  Proof.
    unfold check_type_wf_env_bool, check_type_wf_env.
    destruct check_type_wf_ext; auto.
    discriminate.
  Qed.

  Definition check_wf_env_bool_spec2 (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = false -> type_error.
  Proof.
    unfold check_type_wf_env_bool, check_type_wf_env.
    destruct check_type_wf_ext; auto.
    discriminate.
  Defined.

  (* This function is appropriate for live evaluation inside Coq: 
     it forgets about the derivation produced by typing and replaces it with an opaque constant. *)

  Program Definition check_type_wf_env_fast (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t {T} : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
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

Print Assumptions typecheck_program.
