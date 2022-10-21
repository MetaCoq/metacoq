
(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes utils BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICSigmaCalculus
     PCUICUnivSubst PCUICTyping PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICCumulativity PCUICPosition PCUICEquality
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICCasesContexts
     PCUICConfluence PCUICParallelReductionConfluence PCUICConversion PCUICContextConversion
     PCUICContextConversionTyp
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosed PCUICClosedTyp PCUICSubstitution PCUICContextSubst
     PCUICWellScopedCumulativity
     PCUICWeakeningConv PCUICWeakeningTyp PCUICGeneration PCUICUtils PCUICContexts
     PCUICArities PCUICSpine.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Inductive tele_inst {cf:checker_flags} Σ (Γ : context) : list term -> telescope -> Type :=
| tele_inst_empty : tele_inst Σ Γ [] []
| tele_inst_ass Δ s na t T :
  Σ ;;; Γ |- t : T ->
  tele_inst Σ Γ s (subst_telescope [t] 0 Δ) ->
  tele_inst Σ Γ (t :: s) (Δ ,, vass na T)
| tele_inst_def Δ s na t T :
  tele_inst Σ Γ s (subst_telescope [t] 0 Δ) ->
  tele_inst Σ Γ s (Δ ,, vdef na t T).


