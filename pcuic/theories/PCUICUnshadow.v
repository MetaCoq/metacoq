    (* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPretty PCUICAlphaWcbvEval.

Section env.
    Context (Σ : global_env_ext).

    Definition unshadow_defs (unshadow : list ident -> term -> term) Γ ctx := let NAMES := fold_right (fun x names => let na' := (fresh_name Σ (names ++ Γ) x.(dname).(binder_name) (Some x.(dtype))) in
                                                    (na' :: names)) [] ctx in
                                fold_right (fun x '(names, l) => let na' := (fresh_name Σ (names ++ Γ) x.(dname).(binder_name) (Some x.(dtype))) in
                                           (na' :: names,
                                            {| dname := map_binder_annot (fun _ => nNamed na') x.(dname) ; 
                                               dbody := unshadow (NAMES ++ Γ) x.(dbody) ; 
                                               dtype := unshadow (NAMES ++ Γ) x.(dtype) ;
                                               rarg := x.(rarg) |} :: l)) 
                                              ([], []) ctx.
          
    Fixpoint unshadow (Γ : list ident) (t : term) {struct t} : term :=
     let unshadow_context := fold_right (fun x '(names, l) => let na' := (fresh_name Σ (names ++ Γ) x.(decl_name).(binder_name) (Some x.(decl_type))) in
                                          (na' :: names, {| decl_name := map_binder_annot (fun _ => nNamed na') x.(decl_name) ; 
                                                            decl_body := option_map (unshadow (na' :: names ++ Γ)) x.(decl_body) ; 
                                                            decl_type := unshadow (names ++ Γ) x.(decl_type) |} :: l)) ([], []) in
      match t with
    | tEvar ev args => tEvar ev (map (unshadow Γ) args)
    | tProd na dom codom =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
      tProd (map_binder_annot (fun _ => nNamed na') na) (unshadow Γ dom) (unshadow (na' :: Γ) codom)
    | tLambda na dom body =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
      tLambda (map_binder_annot (fun _ => nNamed na') na) (unshadow Γ dom) (unshadow (na' :: Γ) body)
    | tLetIn na def dom body =>
      let na' := fresh_name Σ Γ na.(binder_name) (Some dom) in
      tLetIn (map_binder_annot (fun _ => nNamed na') na) (unshadow Γ def) (unshadow Γ dom) (unshadow (na' :: Γ) body)
    | tApp f l =>
      tApp (unshadow Γ f) (unshadow Γ l)
    | tCase ind p t brs =>
       tCase
        ind
        (map_predicate id (unshadow Γ) (unshadow Γ) (snd ∘ unshadow_context) p)
        (unshadow Γ t)
        (map (fun b => let (names, ctx) := unshadow_context b.(bcontext) in {| bbody := (unshadow (names ++ Γ) b.(bbody)) ; bcontext := ctx |}) brs)
    | tProj p c =>
       tProj p (unshadow Γ c)
    | tFix mfix n => 
       tFix (snd (unshadow_defs unshadow Γ mfix)) n
    | tCoFix mfix n => 
       tCoFix (snd (unshadow_defs unshadow Γ mfix)) n
    | t => t
    end.

End env.

Definition unshadow_env_ext (Σ : global_env_ext) :=
  ({| retroknowledge := Σ.(retroknowledge) ; universes := Σ.(universes) ; declarations := map (on_snd (fun d => match d with ConstantDecl b => ConstantDecl (map_constant_body (unshadow Σ []) b) | x => x end)) Σ.(declarations) |}, snd Σ).
