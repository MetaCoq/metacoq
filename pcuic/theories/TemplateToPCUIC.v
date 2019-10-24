(* Distributed under the terms of the MIT license.   *)

Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils BasicAst Ast.
From MetaCoq.Checker Require Import WfInv Typing Weakening TypingWf.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICGeneration.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Fixpoint trans (t : Ast.term) : term :=
  match t with
  | Ast.tRel n => tRel n
  | Ast.tVar n => tVar n
  | Ast.tEvar ev args => tEvar ev (List.map trans args)
  | Ast.tSort u => tSort u
  | Ast.tConst c u => tConst c u
  | Ast.tInd c u => tInd c u
  | Ast.tConstruct c k u => tConstruct c k u
  | Ast.tLambda na T M => tLambda na (trans T) (trans M)
  | Ast.tApp u v => mkApps (trans u) (List.map trans v)
  | Ast.tProd na A B => tProd na (trans A) (trans B)
  | Ast.tCast c kind t => tApp (tLambda nAnon (trans t) (tRel 0)) (trans c)
  | Ast.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | Ast.tCase ind p c brs =>
    let brs' := List.map (on_snd trans) brs in
    tCase ind (trans p) (trans c) brs'
  | Ast.tProj p c => tProj p (trans c)
  | Ast.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | Ast.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  end.

Definition trans_decl (d : Ast.context_decl) :=
  let 'Ast.mkdecl na b t := d in
  {| decl_name := na;
     decl_body := option_map trans b;
     decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_one_ind_body (d : Ast.one_inductive_body) :=
  {| ind_name := d.(Ast.ind_name);
     ind_type := trans d.(Ast.ind_type);
     ind_kelim := d.(Ast.ind_kelim);
     ind_ctors := List.map (fun '(x, y, z) => (x, trans y, z)) d.(Ast.ind_ctors);
     ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(Ast.ind_projs) |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(Ast.cst_type); cst_body := option_map trans bd.(Ast.cst_body);
     cst_universes := bd.(Ast.cst_universes) |}.

Definition trans_minductive_body md :=
  {| ind_finite := md.(Ast.ind_finite);
     ind_npars := md.(Ast.ind_npars);
     ind_params := trans_local md.(Ast.ind_params);
     ind_bodies := map trans_one_ind_body md.(Ast.ind_bodies);
     ind_universes := md.(Ast.ind_universes) |}.

Definition trans_global_decl (d : Ast.global_decl) :=
  match d with
  | Ast.ConstantDecl kn bd => ConstantDecl kn (trans_constant_body bd)
  | Ast.InductiveDecl kn bd => InductiveDecl kn (trans_minductive_body bd)
  end.

Definition trans_global_decls d :=
  List.map trans_global_decl d.

Definition trans_global (Σ : Ast.global_env_ext) :=
  (trans_global_decls (fst Σ), snd Σ).
