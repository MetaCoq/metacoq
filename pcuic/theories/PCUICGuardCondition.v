(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICEquality PCUICTyping PCUICReduction PCUICSigmaCalculus
     PCUICNamelessDef PCUICRenameDef PCUICInstDef.

(* AXIOM postulate correctness of the guard condition checker *)

Class GuardCheckerCorrect :=
{
  guard_red1 b Σ Γ mfix mfix' idx :
      guard b Σ Γ mfix ->
      red1 Σ Γ ((if b then tFix else tCoFix) mfix idx)
               ((if b then tFix else tCoFix) mfix' idx) ->
      guard b Σ Γ mfix' ;

  guard_eq_term b Σ Γ mfix mfix' idx :
      guard b Σ Γ mfix ->
      upto_names ((if b then tFix else tCoFix) mfix idx)
                 ((if b then tFix else tCoFix) mfix' idx) ->
      guard b Σ Γ mfix' ;

  guard_extends b Σ Γ mfix Σ' :
    extends Σ.1 Σ'.1 ->
    guard b Σ Γ mfix ->
    guard b Σ' Γ mfix ;

  guard_context_cumulativity `{checker_flags} b Σ Γ Γ' mfix :
    All2_fold (cumul_decls cumulSpec0 Σ) Γ' Γ ->
    guard b Σ Γ mfix ->
    guard b Σ Γ' mfix ;

  guard_nl b Σ Γ mfix :
    let mfix' := map (map_def_anon nl nl) mfix in
    guard b Σ Γ mfix -> guard b (nlg Σ) (nlctx Γ) mfix' ;

  guard_subst_instance {cf:checker_flags} b Σ Γ mfix u univs :
    let mfix' := map (map_def (subst_instance u) (subst_instance u)) mfix in
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    guard b Σ Γ mfix ->
    guard b (Σ.1, univs) (subst_instance u Γ) mfix' ;

  guard_inst `{checker_flags} b Σ Γ Δ mfix σ :
     let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
     Σ ;;; Γ ⊢ σ : Δ ->
     guard b Σ Δ mfix ->
     guard b Σ Γ mfix' ;

  guard_rename b P Σ Γ Δ mfix f :
      let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
      urenaming P Γ Δ f ->
      guard b Σ Δ mfix ->
      guard b Σ Γ mfix' ;

}.

Axiom guard_checking_correct : GuardCheckerCorrect.
#[global] Existing Instance guard_checking_correct.

Definition fix_guard_red1 := guard_red1 Fix.
Definition fix_guard_eq_term := guard_eq_term Fix.
Definition fix_guard_subst_instance `{checker_flags} := guard_subst_instance Fix.
Definition fix_guard_extends := guard_extends Fix.
Definition fix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity Fix.
Definition fix_guard_nl := guard_nl Fix.
Definition fix_guard_inst `{checker_flags} := guard_inst Fix.
Definition fix_guard_rename := guard_rename Fix.

Definition cofix_guard_red1 := guard_red1 CoFix.
Definition cofix_guard_eq_term := guard_eq_term CoFix.
Definition cofix_guard_subst_instance `{checker_flags} := guard_subst_instance CoFix.
Definition cofix_guard_extends := guard_extends CoFix.
Definition cofix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity CoFix.
Definition cofix_guard_nl := guard_nl CoFix.
Definition cofix_guard_inst `{checker_flags} := guard_inst CoFix.
Definition cofix_guard_rename := guard_rename CoFix.
