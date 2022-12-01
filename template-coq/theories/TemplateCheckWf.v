From Coq Require Import List.
From MetaCoq.Template Require Import config Transform TemplateProgram Pretty EtaExpand All Loader.
Import ListNotations.
Import MCMonadNotation.
Import bytestring.
Open Scope bs_scope.

#[local] Existing Instance config.default_checker_flags.

Definition eta_expand p := 
  EtaExpand.eta_expand_program p.

Definition check_const_decl_def kn const_decl : TemplateMonad unit :=
  match const_decl.(cst_body) with
  | Some body => 
    tmMsg ("Unquoting eta-expanded " ++ string_of_kername kn)%bs ;;
    tmUnquote body ;;
    tmMsg ("Succeeded")
  | None => ret tt
  end.

Fixpoint check_mod_decl_def kn impl modtype {struct impl}:=
  match impl with
  | mi_struct sb => let _ := map (fun '(kn, sf) => check_structure_field_def kn sf) sb in ret tt
  | _ => ret tt
  end
with check_structure_field_def kn sf :=
  match sf with
  | sfconst cb => check_const_decl_def kn cb
  | sfmind _ => ret tt
  | sfmod (impl, modtype) => check_mod_decl_def kn impl modtype
  | sfmodtype sb => let _ := map (fun '(kn, sf) => check_structure_field_def kn sf) sb in ret tt
  end.

Definition check_def (d : kername × global_decl) : TemplateMonad unit :=
  match d.2 with
  | ConstantDecl cb => check_const_decl_def d.1 cb
  | InductiveDecl idecl => ret tt
  | ModuleDecl (impl, modtype) => check_mod_decl_def d.1 impl modtype
  | ModuleTypeDecl sb => let _ := map (fun '(kn,sf) => check_structure_field_def kn sf) sb in ret tt
  end.

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ :: _ => false
  end.

Fixpoint wfterm (t : term) : bool :=
  match t with
  | tRel i => true
  | tEvar ev args => List.forallb (wfterm) args
  | tLambda _ T M | tProd _ T M => wfterm T && wfterm M
  | tApp u v => wfterm u && List.forallb (wfterm) v && negb (isApp u) && negb (is_nil v)
  | tCast c kind t => wfterm c && wfterm t
  | tLetIn na b t b' => wfterm b && wfterm t && wfterm b'
  | tCase ind p c brs =>
    let p' := test_predicate (fun _ => true) (wfterm) (wfterm) p in
    let brs' := forallb (wfterm ∘ bbody) brs in
    p' && wfterm c && brs'
  | tProj p c => wfterm c
  | tFix mfix idx =>
    List.forallb (test_def wfterm wfterm) mfix
  | tCoFix mfix idx =>
    List.forallb (test_def wfterm wfterm) mfix
  | _ => true
  end.

From Coq Require Import ssrbool.

Fixpoint wf_module_decl_aux impl wf_modtype :=
  match impl with
  | mi_abstract => wf_modtype
  | mi_algebraic _ => wf_modtype
  | mi_struct sb => List.fold_left (fun acc kn_sf => acc && wf_structure_field kn_sf.2) sb true
  | mi_fullstruct => wf_modtype
  end
with wf_structure_field sf :=
match sf with
| sfconst cb => wfterm cb.(cst_type) && option_default wfterm cb.(cst_body) true
| sfmind _ => true
| sfmod (impl, modtype) =>
    wf_module_decl_aux impl (List.fold_left (fun acc kn_sf => acc && wf_structure_field kn_sf.2) modtype true)
| sfmodtype mt => List.fold_left (fun acc kn_sf => acc && wf_structure_field kn_sf.2) mt true
end.

Definition wf_global_decl d := 
  match d with
  | ConstantDecl cb => wfterm cb.(cst_type) && option_default wfterm cb.(cst_body) true
  | InductiveDecl idecl => true
  | ModuleDecl (impl, modtype) =>
      wf_module_decl_aux impl (List.fold_left (fun acc kn_sf => acc && wf_structure_field kn_sf.2) modtype true)
  | ModuleTypeDecl modtype => (List.fold_left (fun acc kn_sf => acc && wf_structure_field kn_sf.2) modtype true)
  end.
Definition wf_global_declarations : global_declarations -> bool := forallb (wf_global_decl ∘ snd).
Definition wf_global_env (g : global_env) := wf_global_declarations g.(declarations).
Definition wf_program p := wf_global_env p.1 && wfterm p.2.

Definition check_wf (g : Ast.Env.program) : TemplateMonad unit :=
  monad_map check_def g.1.(declarations) ;; 
  tmMsg "Wellformed global environment" ;; ret tt.
  
Axiom assume_wt_template_program : forall p : Ast.Env.program, ∥ wt_template_program p ∥.

Definition check_wf_eta (p : Ast.Env.program) : TemplateMonad unit :=
  monad_map check_def (eta_expand (make_template_program_env p (assume_wt_template_program p))).1.(declarations) ;; 
  tmMsg "Wellformed eta-expanded global environment" ;; ret tt.

(* To test that a program's eta-expansion is indeed well-typed according to Coq's kernel use: 
 
  MetaCoq Run (tmQuoteRec wf_program >>= check_wf_eta). *)
