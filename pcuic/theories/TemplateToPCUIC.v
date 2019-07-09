(* Distributed under the terms of the MIT license.   *)

Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.Template Require Import Ast WfInv Typing.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICGeneration.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module T := Template.Ast.

Fixpoint trans (t : T.term) : term :=
  match t with
  | T.tRel n => tRel n
  | T.tVar n => tVar n
  | T.tEvar ev args => tEvar ev (List.map trans args)
  | T.tSort u => tSort u
  | T.tConst c u => tConst c u
  | T.tInd c u => tInd c u
  | T.tConstruct c k u => tConstruct c k u
  | T.tLambda na T M => tLambda na (trans T) (trans M)
  | T.tApp u v => mkApps (trans u) (List.map trans v)
  | T.tProd na A B => tProd na (trans A) (trans B)
  | T.tCast c kind t => tApp (tLambda nAnon (trans t) (tRel 0)) (trans c)
  | T.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | T.tCase ind p c brs =>
    let brs' := List.map (on_snd trans) brs in
    tCase ind (trans p) (trans c) brs'
  | T.tProj p c => tProj p (trans c)
  | T.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | T.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  end.

Definition trans_decl (d : T.context_decl) :=
  let 'T.mkdecl na b t := d in
  {| decl_name := na;
     decl_body := option_map trans b;
     decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_one_ind_body (d : T.one_inductive_body) :=
  {| ind_name := d.(T.ind_name);
     ind_type := trans d.(T.ind_type);
     ind_kelim := d.(T.ind_kelim);
     ind_ctors := List.map (fun '(x, y, z) => (x, trans y, z)) d.(T.ind_ctors);
     ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(T.ind_projs) |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(T.cst_type); cst_body := option_map trans bd.(T.cst_body);
     cst_universes := bd.(T.cst_universes) |}.

Definition trans_minductive_body md :=
  {| ind_finite := md.(T.ind_finite);
     ind_npars := md.(T.ind_npars);
     ind_params := trans_local md.(T.ind_params);
     ind_bodies := map trans_one_ind_body md.(T.ind_bodies);
     ind_universes := md.(T.ind_universes) |}.

Definition trans_global_decl (d : T.global_decl) :=
  match d with
  | T.ConstantDecl kn bd => ConstantDecl kn (trans_constant_body bd)
  | T.InductiveDecl kn bd => InductiveDecl kn (trans_minductive_body bd)
  end.

Definition trans_global_decls d :=
  List.map trans_global_decl d.

Definition trans_global (Σ : T.global_env_ext) :=
  (trans_global_decls (fst Σ), snd Σ).
