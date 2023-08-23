(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Transform config BasicAst.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
(* From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl. *)
From MetaCoq.Erasure Require EAstUtils EWellformed EEnvMap EWcbvEval.

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Transform.

Obligation Tactic := program_simpl.

Import EGlobalEnv EWellformed.

Definition eprogram := (EAst.global_context * EAst.term).
Definition eprogram_env := (EEnvMap.GlobalContextMap.t * EAst.term).

Import EEnvMap.GlobalContextMap (make, global_decls).

Global Arguments EWcbvEval.eval {wfl} _ _ _.

Definition wf_eprogram (efl : EEnvFlags) (p : eprogram) :=
  @wf_glob efl p.1 /\ @wellformed efl p.1 0 p.2.

Definition wf_eprogram_env (efl : EEnvFlags) (p : eprogram_env) :=
  @wf_glob efl p.1.(global_decls) /\ @wellformed efl p.1.(global_decls) 0 p.2.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) :=
  ∥ EWcbvEval.eval (wfl:=wfl) p.1 p.2 t ∥.

Definition closed_eprogram (p : eprogram) :=
  closed_env p.1 && ELiftSubst.closedn 0 p.2.

Definition closed_eprogram_env (p : eprogram_env) :=
  let Σ := p.1.(global_decls) in
  closed_env Σ && ELiftSubst.closedn 0 p.2.

Definition eval_eprogram_env (wfl : EWcbvEval.WcbvFlags) (p : eprogram_env) (t : EAst.term) :=
  ∥ EWcbvEval.eval (wfl:=wfl) p.1.(global_decls) p.2 t ∥.

Import EWellformed.

Lemma wf_glob_fresh {efl : EEnvFlags} Σ : wf_glob Σ -> EnvMap.EnvMap.fresh_globals Σ.
Proof.
  induction Σ. constructor; auto.
  intros wf; depelim wf. constructor; auto.
Qed.

Module TransformExt.
  Section Opt.
     Context {program program' : Type}.
     Context {value value' : Type}.
     Context {eval :  program -> value -> Prop}.
     Context {eval' : program' -> value' -> Prop}.
     Context (o : Transform.t program program' value value' eval eval').
     Context (extends : program -> program -> Prop).
     Context (extends' : program' -> program' -> Prop).

    Class t := preserves_obs : forall p p' (pr : o.(pre) p) (pr' : o.(pre) p'),
        extends p p' -> extends' (o.(transform) p pr) (o.(transform) p' pr').

  End Opt.

  Section Comp.
    Context {program program' program'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program -> value -> Prop}.
    Context {eval' : program' -> value' -> Prop}.
    Context {eval'' : program'' -> value'' -> Prop}.

    Context {extends : program -> program -> Prop}.
    Context {extends' : program' -> program' -> Prop}.
    Context {extends'' : program'' -> program'' -> Prop}.

    Local Obligation Tactic := idtac.
    #[global]
    Instance compose (o : Transform.t program program' value value' eval eval')
      (o' : Transform.t program' program'' value' value'' eval' eval'')
      (oext : t o extends extends')
      (o'ext : t o' extends' extends'')
      (hpp : (forall p, o.(post) p -> o'.(pre) p))
      : t (Transform.compose o o' hpp) extends extends''.
    Proof. red.
      intros p p' pr pr' ext.
      eapply o'ext. now apply oext.
    Qed.

  End Comp.

End TransformExt.
