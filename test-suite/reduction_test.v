From Coq Require Import Recdef.
From MetaCoq.Template Require Import TemplateMonad bytestring Loader.
(* From MetaCoq.SafeChecker Require Import SafeTemplateChecker. *)
From MetaCoq.PCUIC Require Import PCUICEquality PCUICAst PCUICReflect PCUICSafeLemmata PCUICTyping PCUICNormal PCUICAstUtils PCUICSN TemplateToPCUIC PCUICToTemplate.
From Coq Require Import String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import utils config.
Import MCMonadNotation.
Unset MetaCoq Debug.
(* We're doing erasure assuming no Prop <= Type rule and lets can appear in constructor types. *)
#[local] Existing Instance extraction_checker_flags.

From MetaCoq.TestSuite Require hott_example.

(* MetaCoq Quote Recursively Definition qequiv_adjointify := @isequiv_adjointify. *)

From MetaCoq.SafeChecker Require Import PCUICEqualityDec PCUICWfReduction PCUICErrors PCUICSafeReduce PCUICTypeChecker PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl SafeTemplateChecker PCUICSafeConversion. 

Definition typecheck_template (cf := default_checker_flags)
  {nor : normalizing_flags} (p : Ast.Env.program)
   := 
  let p' := trans_program p in 
    match 
      infer_template_program (cf:=cf) p Monomorphic_ctx
    with CorrectDecl X => 
      X.π1
      (* PCUICPretty.print_env true 10 X.π2.π1.(wf_env_ext_referenced).(referenced_impl_env_ext) *)
    | _ => todo "foo"
  end.

Definition aa := Set.

Inductive Empty (A:Set) : Set := .

Definition dummy (n : nat) : nat := match n with 0 => 1 | S n => n end.

Set Primitive Projections. 

MetaCoq Quote Recursively Definition foo := 
  @hott_example.isequiv_adjointify.
(* plus. *)
(* (fun n m => n + m). *)
(* (forall (n:nat), nat).  *)
(* (fix f (n : nat) : nat := 0). *)
(* (fun t:nat => fun u : unit => t = t). *)
(* (match 100 with 0 => 1 | S n => n end). *)
(* (fun t => match t with tt => 0 end). *)
(* (match todo "foo" with 0 => 1 | S n => n end). *)
(* Set.  *)
(* ((fun x => x + 1) 4). *)

Definition default_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined. 

Time Definition bar := Eval lazy in @typecheck_template default_normal foo.

Unset MetaCoq Strict Unquote Universe Mode.
MetaCoq Unquote Definition unbar := (PCUICToTemplate.trans bar).

Program Definition eval_compute (cf := default_checker_flags) 
(nor : normalizing_flags)
(p : Ast.Env.program) φ  : Ast.term + string 
:= match infer_template_program (cf:=cf) p φ return Ast.term + string with
| CorrectDecl A =>
  let p' := trans_program p in 
  let Σ' := TemplateToPCUIC.trans_global_env p.1 in
  let redtm := reduce_term RedFlags.default 
    optimized_abstract_env_ext_impl (proj1_sig A.π2)
    [] p'.2 _ in 
  inl (PCUICToTemplate.trans redtm)
| EnvError Σ (AlreadyDeclared id) =>
  inr ("Already declared: " ^ id)
| EnvError Σ (IllFormedDecl id e) =>
  inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
end.
Next Obligation.
  sq. destruct H0 as [? [? H0]]. pose (typing_wf_local H0).
  econstructor. rewrite <- e. eauto.
Qed.  

Program Definition eval_compute_cheat (cf := default_checker_flags) 
(nor : normalizing_flags)
(p : Ast.Env.program) φ  : Ast.term
:= let p' := trans_program p in 
  let tm := reduce_term RedFlags.default 
     canonical_abstract_env_ext_impl 
    {| referenced_impl_env_ext := (p'.1 , φ);
       referenced_impl_ext_wf := (todo "wf") |}
    [] p'.2 (todo "welltyped") in
    PCUICToTemplate.trans tm.

Time Definition bar'' := Eval lazy in eval_compute default_normal foo Monomorphic_ctx.

MetaCoq Unquote Definition bar''' := (match bar'' with inl x => x | inr  _ => todo "" end).
