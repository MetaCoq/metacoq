From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import utils Kernames EnvMap.
From MetaCoq.Erasure Require Import EAst EGlobalEnv EAstUtils EGlobalEnv EAstUtils.
Import MCMonadNotation.

Module GlobalContextMap.
  Record t := 
  { global_decls :> global_declarations; 
    map : EnvMap.t global_decl;
    repr : EnvMap.repr global_decls map;
    wf : EnvMap.fresh_globals global_decls }.
  
  Definition lookup_minductive Σ kn : option mutual_inductive_body :=
    decl <- EnvMap.lookup kn Σ.(map);; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive Σ kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive Σ (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).
  
  Definition lookup_inductive_pars Σ kn : option nat := 
    mdecl <- lookup_minductive Σ kn ;;
    ret mdecl.(ind_npars).

  Lemma lookup_inductive_pars_spec Σ kn : lookup_inductive_pars Σ kn = EGlobalEnv.lookup_inductive_pars Σ kn.
  Proof.
    rewrite /lookup_inductive_pars /EGlobalEnv.lookup_inductive_pars.
    rewrite /lookup_inductive /EGlobalEnv.lookup_inductive.
    rewrite /lookup_minductive /EGlobalEnv.lookup_minductive.
    rewrite (EnvMap.lookup_spec Σ.(global_decls)).
    eapply wf. eapply repr. reflexivity.
  Qed.

  Program Definition make (g : global_declarations) (Hg : EnvMap.fresh_globals g): t :=
    {| global_decls := g;
       map := EnvMap.of_global_env g |}.

End GlobalContextMap.

Coercion GlobalContextMap.global_decls : GlobalContextMap.t >-> global_declarations.
