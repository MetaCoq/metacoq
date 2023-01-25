(** This file provides the main function for invoking our extraction. *)
From Coq Require Import String.
From MetaCoq.Erasure.Typed Require Import Erasure.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require OptimizePropDiscr.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Transform.
From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import Certifying.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Common Require Import config.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeCheckerPlugin Require Import SafeTemplateChecker.

#[export]
Existing Instance extraction_checker_flags.

Local Open Scope list_scope.

Module PEnv := P.PCUICEnvironment.

(** We consider a type to be empty, if it is not mutual and has no constructors *)
Definition is_empty_type_decl (d : ExAst.global_decl) : bool :=
  match d with
  | ExAst.ConstantDecl _ => false
  | ExAst.InductiveDecl mib =>
    match mib.(ExAst.ind_bodies) with
    | oib :: _ => match oib.(ExAst.ind_ctors) with [] => true | _ => false end
    | _ => false (** NOTE: this should not happen, the list of bodies should not be empty for a well-formed inductive *)
    end
  | ExAst.TypeAliasDecl _ => false
  end.

Record extract_pcuic_params :=
  { (** Whether to remove discrimination (matches and projections) on things in Prop.
        Necessary to run the transforms. *)
    optimize_prop_discr : bool;
    (** The transforms to apply after extraction. Only run when optimize_prop_discr is true. *)
    extract_transforms : list ExtractTransform; }.


Lemma fresh_global_erase_global_decl_rec :
    forall (Σ0 : global_declarations) (universes0 : ContextSet.t) (retroknowledge0 : Retroknowledge.t)
           (wfΣ : ∥ wf ({| PEnv.universes := universes0; PEnv.declarations := Σ0; PEnv.retroknowledge := retroknowledge0 |}) ∥)
           (seeds : KernameSet.t) (ignore : kername -> bool) kn,
      EnvMap.EnvMap.fresh_global kn Σ0 ->
      ExAst.fresh_global kn (erase_global_decls_deps_recursive Σ0 universes0 retroknowledge0 wfΣ seeds ignore).
Proof.
  intros Σ0 universes0 retroknowledge0 wfΣ seeds ignore kn fresh.
  revert wfΣ seeds.
  induction Σ0;intros wfΣ seeds.
  - constructor.
  - cbn. destruct a;cbn.
    inversion fresh;cbn in *;subst;clear fresh.
    destruct (KernameSet.mem _ _) eqn:Hmem;cbn.
    * constructor;auto.
      now apply IHΣ0.
    * now apply IHΣ0.
Qed.

Lemma fresh_globals_erase_global_decl_rec :
    forall (Σ0 : global_declarations) (universes0 : ContextSet.t) (retroknowledge0 : Retroknowledge.t)
           (wfΣ : ∥ wf ({| PEnv.universes := universes0; PEnv.declarations := Σ0; PEnv.retroknowledge := retroknowledge0 |}) ∥)
           (seeds : KernameSet.t) (ignore : kername -> bool),
      EnvMap.EnvMap.fresh_globals Σ0 ->
      ExAst.fresh_globals (erase_global_decls_deps_recursive Σ0 universes0 retroknowledge0 wfΣ seeds ignore).
Proof.
  intros Σ0 universes0 retroknowledge0 wfΣ seeds ignore fresh.
  revert wfΣ seeds.
  induction Σ0;intros wfΣ seeds;cbn in *.
  - constructor.
  - destruct a;cbn.
    inversion fresh;subst.
    destruct (KernameSet.mem _ _).
    * constructor.
      ** now apply IHΣ0.
      ** now apply fresh_global_erase_global_decl_rec.
    * easy.
Qed.

Program Definition extract_pcuic_env
           (params : extract_pcuic_params)
           (Σ : global_env)
           (wfΣ : ∥wf Σ ∥)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env _ :=
  let Σ := timed "Erasure" (fun _ => erase_global_decls_deps_recursive (declarations Σ) (universes Σ) (retroknowledge Σ) wfΣ seeds ignore) in
  if optimize_prop_discr params then
    let Σ := timed "Removal of prop discrimination" (fun _ => OptimizePropDiscr.optimize_env Σ _) in
    compose_transforms (extract_transforms params) Σ
  else
    Ok Σ.
Next Obligation.
  apply fresh_globals_erase_global_decl_rec.
  sq.
  now apply PCUICWfEnvImpl.wf_fresh_globals.
Qed.

Record extract_template_env_params :=
  { (** The transforms to apply at the template coq level, before translating to
        PCUIC and extracting.
        After performing all the transforms, the pipiline generates proofs that
        the transformed terms are convertible to the originals. *)
    template_transforms : list TemplateTransform;

    (** Function to use to check wellformedness of the environment *)
    check_wf_env_func : forall Σ, result (∥wf Σ∥) string;
    pcuic_args : extract_pcuic_params }.

Import MCMonadNotation.

Definition check_wf_and_extract (params : extract_template_env_params)
           (Σ : global_env) (seeds : KernameSet.t) (ignore : kername -> bool) :=
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition extract_template_env_general
           (pcuic_trans : PCUICEnvironment.global_env -> result PCUICEnvironment.global_env string)
           (params : extract_template_env_params)
           (Σ : Ast.Env.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := trans_global_env Σ in
  Σ <- pcuic_trans (PCUICProgram.trans_env_env Σ) ;;
  check_wf_and_extract params Σ seeds ignore.

Definition extract_template_env := extract_template_env_general ret.

Definition run_transforms_list (Σ : Ast.Env.global_env) (ts : list TemplateTransform) : TemplateMonad Ast.Env.global_env :=
  res <- tmEval lazy (compose_transforms ts Σ) ;;
  match res with
  | Ok Σ => ret Σ
  | Err s => tmFail s
  end.

Definition run_transforms (Σ : Ast.Env.global_env) (params : extract_template_env_params) : TemplateMonad Ast.Env.global_env :=
  let transforms := params.(template_transforms) in
  run_transforms_list Σ transforms.

Definition extract_template_env_certifying_passes
           (pcuic_trans : PCUICEnvironment.global_env -> result PCUICEnvironment.global_env string)
           (params : extract_template_env_params)
           (Σ : Ast.Env.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : TemplateMonad ExAst.global_env :=
  Σtrans <- run_transforms Σ params ;;
  mpath <- tmCurrentModPath tt;;
  gen_defs_and_proofs (Ast.Env.declarations Σ) (Ast.Env.declarations Σtrans) mpath "_cert_pass" seeds;;
  res <- tmEval lazy (extract_template_env_general pcuic_trans params Σtrans seeds ignore) ;;
  match res with
    | Ok env => ret env
    | Err e => tmFail e
  end.

(** MetaCoq's safe checker does not run from within Coq, only when extracting.
    To work around this we assume environments are well formed when extracting
    from within Coq. This is justified since our environments are produced by quoting
    and thus come directly from Coq, where they have already been type checked. *)
Axiom assume_env_wellformed : forall Σ, ∥wf Σ∥.

(** Extract an environment with some minimal checks. This assumes the environment
    is well-formed (to make it computable from within Coq) but furthermore checks that the
    erased context is closed, expanded and that the masks are valid before dearging.
    Suitable for extraction of programs **from within Coq**. *)
Definition extract_within_coq : extract_template_env_params :=
  {| template_transforms := [];
     check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true true true true] |} |}.

Definition extract_template_env_within_coq := extract_template_env extract_within_coq.

(** [get_projections] returns a list of constructor names and the name of the inductive associated *)
Definition get_projections (env : ExAst.global_env) : list (ident * ExAst.one_inductive_body) :=
  let get_projs (d : ExAst.global_decl) : list (ident * ExAst.one_inductive_body) :=
    match d with
    | ExAst.InductiveDecl mind =>
      (* We assume no mutually inductive definitions *)
      match mind.(ExAst.ind_bodies) with
      (* pair every constructor with the inductive's name *)
      | [oib] =>
        match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
        (* case 1-ind with primitive projections *)
        | [ctor],_::_ => map (fun '(na, _) => (na, oib)) oib.(ExAst.ind_projs)
        (* case 1-ind without primitive projections *)
        | [(_,ctor_args,_)],[] =>
          (* let is_named '(nm,_) := match nm with nNamed _ => true | _ => false end in *)
          (* let named_args := filter is_named ctor_args in *)
          map (fun '(na, _) => (string_of_name na, oib)) ctor_args
        | _,_ => []
        end
      | _ => []
      end
    | _ => []
    end in
  List.concat (List.map (fun p => get_projs p.2) env).
