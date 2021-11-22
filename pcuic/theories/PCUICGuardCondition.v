(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICEquality PCUICTyping PCUICNamelessDef PCUICSigmaCalculus
     PCUICRenameDef PCUICInstDef.

(* AXIOM postulate correctness of the guard condition checker *)

Class GuardCheckerCorrect := 
{
  fix_guard_red1 Σ Γ mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_eq_term Σ Γ mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      upto_names (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    fix_guard Σ Γ mfix ->
    fix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  fix_guard_extends Σ Γ mfix Σ' : 
    fix_guard Σ Γ mfix ->
    extends Σ.1 Σ'.1 ->
    fix_guard Σ' Γ mfix ;

  fix_guard_context_cumulativity `{checker_flags} Σ Γ Γ' mfix :
    All2_fold (cumul_decls Σ) Γ' Γ ->
    fix_guard Σ Γ mfix ->
    fix_guard Σ Γ' mfix ;

  fix_guard_nl Σ Γ mfix :
    fix_guard Σ Γ mfix -> fix_guard (nlg Σ) (nlctx Γ) (map (map_def_anon nl nl) mfix) ;
  
  fix_guard_inst `{checker_flags} Σ Γ Δ mfix σ :
     Σ ;;; Γ ⊢ σ : Δ ->
     let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
     fix_guard Σ Δ mfix ->
     fix_guard Σ Γ mfix' ;

  fix_guard_rename P Σ Γ Δ mfix f :
      urenaming P Γ Δ f ->
      let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
      fix_guard Σ Δ mfix ->
      fix_guard Σ Γ mfix' ;
  
  cofix_guard_red1 Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_eq_term Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    upto_names (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    cofix_guard Σ (Γ ,,, Γ') mfix ->
    cofix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  cofix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    cofix_guard Σ Γ mfix ->
    cofix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;
  
  cofix_guard_extends Σ Γ mfix Σ' : 
    cofix_guard Σ Γ mfix ->
    extends Σ.1 Σ'.1 ->
    cofix_guard Σ' Γ mfix;

  cofix_guard_context_cumulativity `{checker_flags} Σ Γ Γ' mfix :
    All2_fold (cumul_decls Σ) Γ' Γ ->
    cofix_guard Σ Γ mfix ->
    cofix_guard Σ Γ' mfix ;

  cofix_guard_nl Σ Γ mfix :
    cofix_guard Σ Γ mfix -> cofix_guard (nlg Σ) (nlctx Γ) (map (map_def_anon nl nl) mfix) ;

  cofix_guard_inst `{checker_flags} Σ Γ Δ mfix σ :
    Σ ;;; Γ ⊢ σ : Δ ->
    let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
    cofix_guard Σ Δ mfix ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_rename P Σ Γ Δ mcofix f :
      urenaming P Γ Δ f ->
      let mcofix' := map (map_def (rename f) (rename (shiftn (List.length mcofix) f))) mcofix in
      cofix_guard Σ Δ mcofix ->
      cofix_guard Σ Γ mcofix' ;                                        
}.

Axiom guard_checking_correct : GuardCheckerCorrect.
Existing Instance guard_checking_correct.
