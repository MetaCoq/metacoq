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

Fixpoint check_mod_impl_def kn impl {struct impl}:=
  match impl with
  | mi_struct sb => check_structure_body_def kn sb ;; ret tt
  | _ => ret tt
  end
with check_structure_field_def kn id sf :=
  let kn' := ((MPdot kn.1 kn.2), id) in
  match sf with
  | sfconst cb => check_const_decl_def kn' cb
  | sfmind _ => ret tt
  | sfmod impl modtype => check_mod_impl_def kn' impl ;; check_structure_body_def kn' modtype
  | sfmodtype sb => check_structure_body_def kn' sb
  end
with check_structure_body_def kn sb :=
  match sb with
  | sb_nil => ret tt
  | sb_cons id sf sb' => check_structure_field_def kn id sf ;; check_structure_body_def kn sb'
  end.

Definition check_modtype_def := check_structure_body_def.
Definition check_mod_decl_def kn m := check_mod_impl_def kn m.1 ;; check_modtype_def kn m.2.

Definition check_def (d : kername × global_decl) : TemplateMonad unit :=
  match d.2 with
  | ConstantDecl cb =>
    match cb.(cst_body) with
    | Some body =>
      tmMsg ("Unquoting eta-expanded " ++ string_of_kername d.1)%bs ;;
      tmUnquote body ;;
      tmMsg ("Succeeded")
    | None => ret tt
    end
  | InductiveDecl idecl => ret tt
  | ModuleDecl m => check_mod_decl_def d.1 m
  | ModuleTypeDecl sb => check_modtype_def d.1 sb
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

Definition wf_constant_body cb := wfterm cb.(cst_type) && option_default wfterm cb.(cst_body) true.

Fixpoint wf_module_impl impl :=
  match impl with
  | mi_struct sb => wf_structure_body sb
  | _ => true
  end
with wf_structure_field sf :=
  match sf with
  | sfconst cb => wf_constant_body cb
  | sfmind _ => true
  | sfmod impl modtype => wf_module_impl impl && wf_structure_body modtype
  | sfmodtype mt => wf_structure_body mt
  end
with wf_structure_body sb :=
  match sb with
  | sb_nil => true
  | sb_cons kn sf sb' => wf_structure_field sf && wf_structure_body sb'
  end.

Definition wf_module_type := wf_structure_body.
Definition wf_module_decl m := wf_module_impl m.1 && wf_structure_body m.2.

Definition wf_global_decl d :=
  match d with
  | ConstantDecl cb => wf_constant_body cb
  | InductiveDecl idecl => true
  | ModuleDecl m => wf_module_decl m
  | ModuleTypeDecl modtype => wf_module_type modtype
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
