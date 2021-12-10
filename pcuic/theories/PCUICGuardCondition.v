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

  guard_subst_instance {cf:checker_flags} b Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    guard b Σ Γ mfix ->
    guard b (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  guard_extends b Σ Γ mfix Σ' : 
    guard b Σ Γ mfix ->
    extends Σ.1 Σ'.1 ->
    guard b Σ' Γ mfix ;

  guard_context_cumulativity `{checker_flags} b Σ Γ Γ' mfix :
    All2_fold (cumul_decls Σ) Γ' Γ ->
    guard b Σ Γ mfix ->
    guard b Σ Γ' mfix ;

  guard_nl b Σ Γ mfix :
    guard b Σ Γ mfix -> guard b (nlg Σ) (nlctx Γ) (map (map_def_anon nl nl) mfix) ;
  
  guard_inst `{checker_flags} b Σ Γ Δ mfix σ :
     Σ ;;; Γ ⊢ σ : Δ ->
     let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
     guard b Σ Δ mfix ->
     guard b Σ Γ mfix' ;

  guard_rename b P Σ Γ Δ mfix f :
      urenaming P Γ Δ f ->
      let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
      guard b Σ Δ mfix ->
      guard b Σ Γ mfix' ;
                                   
}.

Axiom guard_checking_correct : GuardCheckerCorrect.
#[global] Existing Instance guard_checking_correct.

Definition fix_guard_red1 := guard_red1 true.
Definition fix_guard_eq_term := guard_eq_term true.
Definition fix_guard_subst_instance `{checker_flags} := guard_subst_instance true.
Definition fix_guard_extends := guard_extends true.
Definition fix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity true.
Definition fix_guard_nl := guard_nl true.
Definition fix_guard_inst `{checker_flags} := guard_inst true.
Definition fix_guard_rename := guard_rename true.

Definition cofix_guard_red1 := guard_red1 false.
Definition cofix_guard_eq_term := guard_eq_term false.
Definition cofix_guard_subst_instance `{checker_flags} := guard_subst_instance false.
Definition cofix_guard_extends := guard_extends false.
Definition cofix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity false.
Definition cofix_guard_nl := guard_nl false.
Definition cofix_guard_inst `{checker_flags} := guard_inst false.
Definition cofix_guard_rename := guard_rename false.
