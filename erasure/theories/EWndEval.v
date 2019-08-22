From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils Ast.
From MetaCoq.Erasure Require Import EAst EInduction ELiftSubst ETyping.
From MetaCoq.Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Local Existing Instance config.default_checker_flags.

(** * 1-step non-deterministic weak reduction **)

Section Wnd.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

Inductive Wnd : term -> term -> Prop :=
 (*** contraction steps ***)
(** Constant unfolding *)
| wConst c decl body (isdecl: declared_constant Σ c decl):
   decl.(cst_body) = Some body -> Wnd (tConst c) body
(** Beta *)
| wBeta na a b: Wnd (tApp (tLambda na b) a) (subst10 a b)
(** Let *)
| wLet na b0 b1: Wnd (tLetIn na b0 b1) (subst10 b0 b1).



End Wnd.

(********************************  
| sConst: forall (s:string) (t:Term),
    LookupDfn s p t -> wndEval (TConst s) t
| sBeta: forall (nm:name) (bod arg:Term),
    wndEval (TApp (TLambda nm bod) arg) (whBetaStep bod arg)
(* note: [instantiate] is total *)
| sLetIn: forall (nm:name) (dfn bod:Term),
    wndEval (TLetIn nm dfn bod) (instantiate dfn 0 bod)
(* Case argument must be in Canonical form *)
(* n is the number of parameters of the datatype *)
| sCase: forall (ml:inductive * nat) (s mch:Term)
                (args ts:Terms) (brs:Brs) (n npars nargs:nat),
    canonicalP mch = Some (n, npars, nargs, args) ->
    tskipn (snd ml) args = Some ts ->
    whCaseStep n ts brs = Some s ->
    wndEval (TCase ml mch brs) s
| sFix: forall (dts:Defs) (m:nat) (arg:Term) (x:Term) (ix:nat),
    (** ix is index of recursive argument **)
    dnthBody m dts = Some (x, ix) ->
    wndEval (TApp (TFix dts m) arg) (pre_whFixStep x dts arg)
| sProofApp arg: wndEval (TApp TProof arg) TProof
| sProj: forall bod r npars nargs args arg x ind,
    canonicalP bod = Some (r, npars, nargs, args) ->
    List.nth_error args (npars + arg) = Some x ->
    wndEval (TProj (ind, npars, arg) bod) x          
(*** congruence steps ***)
(** no xi rules: sLambdaR, sLetInR,
 *** no congruence on Case branches ***)
| sAppFn:  forall (t r arg:Term),
    wndEval t r -> wndEval (TApp t arg) (TApp r arg)
| sAppArg: forall (t arg brg:Term),
    wndEval arg brg -> wndEval (TApp t arg) (TApp t brg)
| sLetInDef:forall (nm:name) (d1 d2 bod:Term),
    wndEval d1 d2 -> wndEval (TLetIn nm d1 bod) (TLetIn nm d2 bod)
| sCaseArg: forall (nl:inductive * nat) (mch can:Term) (brs:Brs),
    wndEval mch can -> wndEval (TCase nl mch brs) (TCase nl can brs)
| sProjBod: forall prj bod Bod,
    wndEval bod Bod -> wndEval (TProj prj bod) (TProj prj Bod).
Hint Constructors wndEval.


**********************)
