(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
Set Equations Transparent.
From MetaCoq.Template Require Import config utils Kernames MCRelations Primitive.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive.
From MetaCoq.Erasure Require Import EAst EAstUtils EArities Extract Prelim EDeps ErasureProperties ErasureCorrectness.

Set Asymmetric Patterns.
Local Set Keyed Unification.
Import MCMonadNotation.
Implicit Types (cf : checker_flags).

Definition unquote_prim_model {t : prim_tag} (e : @prim_model E.term t) : @prim_model PCUICAst.term t :=
  match e in @prim_model _ x return prim_model _ x with
  | primIntModel i => primIntModel i
  | primFloatModel f => primFloatModel f
  end.
  
Definition unquote_prim_val (p : prim_val E.term) : PCUICAst.prim_val :=
  (p.π1; unquote_prim_model p.π2).

#[bypass_check(guard)]  
Fixpoint unquote (Σ : global_env) (t : term) (ty : PCUICAst.term) { struct t }: option PCUICAst.term :=
  match t with
  | tConstruct ind k args =>
    let (hd, tyargs) := PCUICAstUtils.decompose_app ty in
    match hd with
    | PCUICAst.tInd ind' u' => 
      '(mdecl, idecl, cdecl) <- PCUICAst.lookup_constructor Σ ind k ;;
      unqargs <- monad_map2 (unquote Σ) tt 
        (List.skipn mdecl.(PCUICEnvironment.ind_npars) args)
        (map decl_type cdecl.(PCUICEnvironment.cstr_args)) ;;
      let app := PCUICAst.mkApps (PCUICAst.tConstruct ind k u')
        (List.firstn mdecl.(PCUICEnvironment.ind_npars) tyargs ++ unqargs)
      in Some app
    | _ => None
    end
  | tPrim pv => ret (PCUICAst.tPrim (unquote_prim_val pv))
  | _ => None
  end.
