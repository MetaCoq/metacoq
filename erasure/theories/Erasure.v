(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils uGraph Pretty.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction EPretty.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr.

Existing Instance envcheck_monad.
Existing Instance extraction_checker_flags.

(** This is a hack to avoid having to handle template polymorphism and make
    erasure fast: we actually admit the proof of wf Σ and never build it. *)

Definition assume_wf_decl {cf : checker_flags} (Σ : global_env_ext) :
  ∥ wf Σ ∥ ->
  ∥ on_udecl Σ.1 Σ.2 ∥ ->
  forall G : universes_graph,
    is_graph_of_uctx G (global_ext_uctx Σ) ->
    forall kn (d : global_decl), EnvCheck (∥ on_global_decl (lift_typing typing) Σ kn d ∥).
Proof.
  intros. apply CorrectDecl. constructor. todo "assumed correct global declaration".
Defined.

Definition assume_fresh id env : EnvCheck (∥ fresh_global id env ∥).
Proof.
  left. todo "assumed fresh".
Defined.

Program Definition compute_udecl (id : string) (Σ : global_env) (HΣ : ∥ wf Σ ∥) G
  (HG : is_graph_of_uctx G (global_uctx Σ)) (udecl : universes_decl)
  : EnvCheck (∑ uctx', gc_of_uctx (uctx_of_udecl udecl) = Some uctx' /\
               ∥ on_udecl Σ udecl ∥) :=
    match gc_of_uctx (uctx_of_udecl udecl) with
    | Some uctx => ret (uctx; conj _ _)
    | None => raise (empty_ext Σ, IllFormedDecl id (Msg "constraints not satisfiable"))
    end.
  Next Obligation.
    constructor. todo "assume udecl is ok".
  Defined.

Program Fixpoint check_wf_env_only_univs (Σ : global_env)
  : EnvCheck (∑ G, (is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥)) :=
  match Σ with
  | nil => ret (init_graph; _)
  | d :: Σ =>
    G <- check_wf_env_only_univs Σ ;;
    assume_fresh d.1 Σ ;;
    let udecl := universes_decl_of_decl d.2 in
    uctx <- compute_udecl (string_of_kername d.1) Σ _ G.π1 (proj1 G.π2) udecl ;;
    let G' := add_uctx uctx.π1 G.π1 in
    assume_wf_decl (Σ, udecl) _ _ G' _ d.1 d.2 ;;
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
    rewrite Hctrs' in H0. simpl in H0.
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
    rewrite Hctrs' in H1; simpl in H1.
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
    now rewrite LevelSet_union_empty, CS_union_empty.
  Qed.

(* This is the total erasure function + the optimization that removes all 
  pattern-matches on propositions. *)

Program Definition erase_template_program (p : Ast.program) 
  : (EAst.global_context * EAst.term) :=
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  let t := ErasureFunction.erase (empty_ext Σ) _ nil (trans p.2) _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) Σ _ in
  (EOptimizePropDiscr.optimize_env Σ', EOptimizePropDiscr.optimize Σ' t).

Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. constructor. todo "assuming wf environment".
Defined.

Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. todo "assuming well-typedness".
Defined.
Next Obligation.
  constructor. todo "assuming wf environment".
Defined.
Local Open Scope string_scope.

(** This uses the retyping-based erasure *)
Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.program)
  : string :=
  let p := fix_program_universes p in
  let (Σ', t) := erase_template_program p in
  "Environment is well-formed and " ^ Pretty.print_term (Ast.empty_ext p.1) [] true p.2 ^
  " erases to: " ^ nl ^ print_term Σ' [] true false t.
