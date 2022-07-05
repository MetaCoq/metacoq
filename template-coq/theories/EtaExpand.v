(** * Eta-expansion and proof generation **)

(** We perform eta-expansion of template-coq terms and generate proofs that
    we terms are equal to the originals. Since eta-conversion is part of the
    Coq's conversion, the proof is essentially [eq_refl].
    All dependencies are also expanded.*)


From Coq Require Import List PeanoNat Bool Lia.
From MetaCoq.Template Require Export
     utils (* Utility functions *)
     monad_utils   (* Monadic notations *)
     uGraph        (* The graph of universes *)
     BasicAst      (* The basic AST structures *)
     Ast           (* The term AST *)
     AstUtils      (* Utilities on the AST *)
     Induction     (* Induction *)
     LiftSubst     (* Lifting and substitution for terms *)
     UnivSubst     (* Substitution of universe instances *)
     Typing        (* Typing judgment *)
     config        (* Typing configuration *).


Open Scope nat.
Open Scope bs.

Import Template.Ast.
Import ListNotations.

Section Eta.
   Context (Σ : global_declarations).

(* 
  Fixpoint remove_top_prod (t : Ast.term) (n : nat) :=
    match n,t with
    | O, _  => t
    | S m, tProd nm ty1 ty2 => remove_top_prod ty2 m
    | _, _ => t
    end.
 *)
(*   Fixpoint to_ctx names types : context :=
    match names, types with
    | n :: names, t :: types => {| decl_body := None; decl_name := n ; decl_type := t |} :: to_ctx names types
    | _, _ => []
    end. *)

  (** Eta-expands the given term of the form [(t args)].

      [t] -- a term;
      [args] -- arguments to which the term is applied;
      [ty] -- the term's type;
      [count] -- number of arguments *)
  Definition eta_single (t : Ast.term) (args : list Ast.term) (ty : Ast.term) (count : nat): term :=
    let needed := count - #|args| in
    let prev_args := map (lift0 needed) args in
    let eta_args := rev_map tRel (seq 0 needed) in
    let remaining := firstn needed (skipn #|args| (rev (smash_context [] (decompose_prod_assum [] ty).1))) in
    let remaining_subst := subst_context (rev args) 0 remaining in 
    fold_right (fun d b => Ast.tLambda d.(decl_name) d.(decl_type) b) (mkApps (lift0 needed t) (prev_args ++ eta_args)) remaining_subst.
  
  Definition eta_constructor (ind : inductive) c u args :=
      match lookup_global Σ ind.(inductive_mind) with
        | Some (InductiveDecl mind) => 
           match nth_error mind.(ind_bodies) ind.(inductive_ind) with
           | Some idecl => 
              match nth_error idecl.(ind_ctors) c with
              | Some cdecl =>
                 let ty := (type_of_constructor mind cdecl (ind, c) u) in
                 let n := (ind_npars mind + context_assumptions (cstr_args cdecl)) in
                 Some (eta_single (Ast.tConstruct ind c u) args ty n)
              | _ => None
              end
          | _ => None
           end
         | _ => None
      end.
  
  Definition eta_fixpoint (def : mfixpoint term) (i : nat) d (args : list term) :=
    eta_single (tFix def i) args (d.(dtype)) (1 + d.(rarg)).

  Definition lift_ctx n k (Γ : list (option (nat * term))) :=
    rev (mapi (fun i x => option_map (on_snd (lift n (k + i))) x) (rev Γ)).

  Definition up (Γ : list (option (nat * term))) := None :: Γ.

  Fixpoint eta_expand (Γ : list (option (nat * term))) (t : term) : term :=
    match t with
    | tVar _ | tSort _ | tProd _ _ _ | tConst _ _ | tInd _ _ => t
    | tRel n => match nth_error Γ n with
                | Some (Some (c, ty)) => eta_single (tRel n) [] (lift0 (S n) ty) c
                | _ => tRel n
                end
  
    | tApp hd args =>
      match hd with
      | tConstruct ind c u =>
        match eta_constructor ind c u (map (eta_expand Γ) args) with 
        | Some res => res
        | None => tVar ("Error: lookup of an inductive failed for "
                       ++ string_of_kername ind.(inductive_mind))
        end
      | tFix def i => 
        let def' := 
          map (fun d => 
            let ctx := List.rev (mapi (fun (i : nat) d => Some (1 + d.(rarg), (lift0 i (dtype d)))) def) in
            {| dname := dname d ; dtype := dtype d ; dbody := eta_expand (ctx ++  Γ) d.(dbody) ; rarg := rarg d |}) 
            def
        in 
        match nth_error def' i with
        | Some d => eta_fixpoint def' i d (map (eta_expand Γ) args)
        | None => tVar ("Error: lookup of a fixpoint failed for "
                          ++ string_of_term t)
        end
      | tRel n => 
        match nth_error Γ n with
        | Some (Some (c, ty)) => eta_single (tRel n) (map (eta_expand Γ) args) (lift0 (S n) ty) c 
        | Some None => mkApps (tRel n) (map (eta_expand Γ) args)
        | _ => tRel n
        end
      | _ => mkApps (eta_expand Γ hd) (map (eta_expand Γ) args)
    end
    | tEvar n ts => tEvar n (map (eta_expand Γ) ts)
    | tLambda na ty body => tLambda na ty (eta_expand (up Γ) body)
    | tLetIn na val ty body => tLetIn na (eta_expand Γ val) ty (eta_expand (up Γ) body)
    | tCase ci p disc brs =>
        let p' := map_predicate id (eta_expand Γ) id p in
        let brs' := map (fun b => {| bcontext := bcontext b; bbody := eta_expand (repeat None #|b.(bcontext)| ++ Γ) b.(bbody) |}) brs in 
        tCase ci p' (eta_expand Γ disc) brs'
    | tProj p t => tProj p (eta_expand Γ t)
    | tFix def i => let def' := (map (fun d =>  
                                         let ctx := List.rev (mapi (fun (i : nat) d => Some (1 + d.(rarg), (lift0 i (dtype d)))) def) in
                                        {| dname := dname d ; dtype := dtype d ; dbody := eta_expand (ctx ++  Γ) d.(dbody) ; rarg := rarg d |}) def) in 
                      match nth_error def' i with
                      | Some d => eta_fixpoint def' i d []
                      | None => tVar ("Error: lookup of a fixpoint failed for "
                                       ++ string_of_term t)
                      end
    | tCoFix def i => tCoFix (map (map_def id (eta_expand (repeat None (#|def|) ++ Γ))) def) i
    (* NOTE: we know that constructors and constants are not applied at this point,
       since applications are captured by the previous cases *)
    | tConstruct ind c u =>
        match eta_constructor ind c u [] with 
        | Some res => res
        | None => tVar ("Error: lookup of an inductive failed for "
                       ++ string_of_kername ind.(inductive_mind))
        end
    | tCast t1 k t2 => tCast (eta_expand Γ t1) k (eta_expand Γ t2)
    end.

End Eta.

Definition eta_global_decl Σ cb := 
  {| cst_type := eta_expand Σ [] cb.(cst_type) ; 
     cst_universes := cb.(cst_universes) ;
     cst_body := match cb.(cst_body) with
                | Some b => Some (eta_expand Σ [] b)
                | None => None
                end;
    cst_relevance := cb.(cst_relevance) |}.
    
Definition map_decl_body {term : Type} (f : term -> term) decl := 
  {| decl_name := decl.(decl_name); 
     decl_type := decl.(decl_type);
     decl_body := option_map f decl.(decl_body) |}.

Fixpoint fold_context_k_defs {term : Type} (f : nat -> term -> term) (Γ: list (BasicAst.context_decl term)) :=
  match Γ with
  | [] => []
  | d :: Γ => map_decl_body (f #|Γ|) d :: fold_context_k_defs f Γ
  end.

Lemma context_assumptions_fold_context_k_defs {f : _ -> term -> term} {Γ} : 
  context_assumptions (fold_context_k_defs f Γ) = context_assumptions Γ.
Proof.
  induction Γ; cbn; auto. destruct a as [? [b|] ty]; cbn; auto.
Qed.

Lemma fold_context_k_defs_length {f : _ -> term -> term} Γ : #|fold_context_k_defs f Γ| = #|Γ|.
Proof.
  induction Γ; cbn; auto.
Qed.

Definition eta_context Σ Γ ctx :=
   (* map_context (eta_expand Σ []) ctx. *)
  fold_context_k_defs (fun n => eta_expand Σ (repeat None (n + Γ))) ctx.

Definition eta_constructor_decl Σ mdecl cdecl :=
  {| cstr_name := cdecl.(cstr_name);
     cstr_args := eta_context Σ (#|mdecl.(ind_params)| + #|mdecl.(ind_bodies)|) cdecl.(cstr_args);
     cstr_indices := map (eta_expand Σ []) cdecl.(cstr_indices);
     cstr_type := eta_expand Σ (repeat None #|mdecl.(ind_bodies)|) cdecl.(cstr_type);
     cstr_arity := cdecl.(cstr_arity) |}.
    
Definition eta_inductive_decl Σ mdecl idecl :=
  {| ind_name := idecl.(ind_name);
	   ind_indices := idecl.(ind_indices);
     ind_sort := idecl.(ind_sort);
     ind_type := idecl.(ind_type);
     ind_kelim := idecl.(ind_kelim);
     ind_ctors := map (eta_constructor_decl Σ mdecl) idecl.(ind_ctors);
     ind_projs := idecl.(ind_projs);
     ind_relevance := idecl.(ind_relevance) |}.

Definition eta_minductive_decl Σ mdecl :=
  {| ind_finite := mdecl.(ind_finite);
     ind_params := eta_context Σ 0 mdecl.(ind_params);
     ind_npars := mdecl.(ind_npars);
     ind_bodies := map (eta_inductive_decl Σ mdecl) mdecl.(ind_bodies);
     ind_universes := mdecl.(ind_universes);
     ind_variance := mdecl.(ind_variance); |}.

Definition eta_global_declaration (Σ : global_declarations) decl : global_decl :=
  match decl with
  | ConstantDecl cb => ConstantDecl (eta_global_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (eta_minductive_decl Σ idecl)
  end.

Fixpoint eta_global_declarations (Σ : global_declarations) :=
  match Σ with
  | [] => []
  | (kn, decl) :: Σ => (kn, eta_global_declaration Σ decl) :: eta_global_declarations Σ
  end.

Definition eta_expand_global_env (Σ : global_env) :=
  {| universes := Σ.(universes); declarations := eta_global_declarations Σ.(declarations) |}.

(*
Inductive tree := T : list tree -> tree.
Fixpoint tmap (f : tree -> tree) (t : tree) := match t with T l => T (map (tmap f) l) end.

From MetaCoq.Template Require Import Loader Pretty.
MetaCoq Quote Recursively Definition p := ltac:(let x := eval unfold tmap in tmap in exact (x)). 
MetaCoq Unquote Definition q := (eta_expand p.1.(declarations) [] p.2). 
Print q. 

Eval lazy in let x := print_term (p.1, Monomorphic_ctx) [] true (eta_expand p.1.(declarations) [] p.2) in 
             let y := print_term (p.1, Monomorphic_ctx) [] true p.2 in
 (x,y).

Print q.

*)

Definition isConstruct t :=
    match t with tConstruct _ _ _ => true | _ => false end.
Definition isFix t :=
    match t with tFix _ _ => true | _ => false end.
Definition isRel t :=
    match t with tRel _ => true | _ => false end.

Section expanded.

Variable Σ : global_env.

Local Unset Elimination Schemes.

Inductive expanded (Γ : list nat): term -> Prop :=
| expanded_tRel (n : nat) : nth_error Γ n = Some 0 -> expanded Γ (tRel n)
| expanded_tRel_app (n : nat) args m : nth_error Γ n = Some m -> m <= #|args| -> Forall (expanded Γ) args -> expanded Γ (tApp (tRel n) args)
| expanded_tVar (id : ident) : expanded Γ (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall (expanded Γ) args -> expanded Γ (tEvar ev args)
| expanded_tSort (s : Universe.t) : expanded Γ (tSort s)
| expanded_tCast (t : term) (kind : cast_kind) (v : term) : expanded Γ t -> expanded Γ v -> expanded Γ (tCast t kind v)
| expanded_tProd (na : aname) (ty : term) (body : term) : (* expanded Γ ty -> expanded Γ body -> *) expanded Γ (tProd na ty body)
| expanded_tLambda (na : aname) (ty : term) (body : term) : (* expanded Γ ty -> *) expanded (0 :: Γ) body -> expanded Γ (tLambda na ty body)
| expanded_tLetIn (na : aname) (def : term) (def_ty : term) (body : term) : expanded Γ def (* -> expanded Γ def_ty *) -> expanded (0 :: Γ) body -> expanded Γ (tLetIn na def def_ty body)
| expanded_tApp (f : term) (args : list term) : negb (isConstruct f || isFix f || isRel f) -> expanded Γ f -> Forall (expanded Γ) args -> expanded Γ (tApp f args)
| expanded_tConst (c : kername) (u : Instance.t) : expanded Γ (tConst c u)
| expanded_tInd (ind : inductive) (u : Instance.t) : expanded Γ (tInd ind u)
| expanded_tConstruct (ind : inductive) (idx : nat) (u : Instance.t) mind idecl cdecl :
    declared_constructor Σ (ind, idx) mind idecl cdecl ->
    ind_npars mind + context_assumptions (cstr_args cdecl) = 0 ->
    expanded Γ (tConstruct ind idx u)
| expanded_tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term)) :     
    expanded Γ discr ->
    Forall (expanded Γ) type_info.(pparams) ->
    Forall (fun br => expanded (repeat 0 #|br.(bcontext)| ++ Γ) br.(bbody)) branches -> 
    expanded Γ (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded Γ t -> expanded Γ (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d : 
  d.(rarg) < context_assumptions (decompose_prod_assum []  d.(dtype)).1 ->
  Forall (fun d => isLambda d.(dbody) /\
           let ctx := List.rev (mapi (fun (i : nat) d => 1 + d.(rarg)) mfix) in
          expanded (ctx ++ Γ) d.(dbody)) mfix ->
  Forall (expanded Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  expanded Γ (tApp (tFix mfix idx) args)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : 
  Forall (fun d => expanded (repeat 0 #|mfix| ++ Γ) d.(dbody)) mfix ->
  expanded Γ (tCoFix mfix idx)
| expanded_tConstruct_app ind c u mind idecl cdecl args :
    declared_constructor Σ (ind, c) mind idecl cdecl ->
    #|args| >= (ind_npars mind + context_assumptions (cstr_args cdecl)) ->
    Forall (expanded Γ) args ->
    expanded Γ (tApp (tConstruct ind c u) args).

End expanded.

Lemma expanded_ind :
forall (Σ : global_env) (P : list nat -> term -> Prop),
(forall Γ, forall n : nat, nth_error Γ n = Some 0 -> P Γ (tRel n)) ->
(forall Γ, forall n : nat, forall args, forall m, nth_error Γ n = Some m -> forall Heq :  m <= #|args|, Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (tApp (tRel n) args)) ->
(forall Γ, forall id : ident, P Γ (tVar id)) ->
(forall Γ, forall (ev : nat) (args : list term), Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (tEvar ev args)) ->
(forall Γ, forall s : Universe.t, P Γ (tSort s)) ->
(forall Γ, forall (t : term) (kind : cast_kind) (v : term),
 expanded Σ Γ t -> P Γ t -> expanded Σ Γ v -> P Γ v -> P Γ (tCast t kind v)) ->
(forall Γ, forall (na : aname) (ty body : term), P Γ (tProd na ty body)) ->
(forall Γ, forall (na : aname) (ty body : term), expanded Σ (0 :: Γ) body -> P (0 :: Γ) body -> P Γ (tLambda na ty body)) ->
(forall Γ (na : aname) (def def_ty body : term),
 expanded Σ Γ def ->
 P Γ def ->
 expanded Σ (0 :: Γ) body -> P (0 :: Γ) body -> P Γ (tLetIn na def def_ty body)) ->
(forall Γ, forall (f7 : term) (args : list term),
 negb (isConstruct f7 || isFix f7 || isRel f7) -> ~ isRel f7 ->
 expanded Σ Γ f7 -> P Γ f7 -> Forall (expanded Σ Γ) args -> Forall (P Γ) args -> P Γ (tApp f7 args)) ->
(forall Γ (c : kername) (u : Instance.t), P Γ (tConst c u)) ->
(forall Γ, forall (ind : inductive) (u : Instance.t), P Γ (tInd ind u)) ->
(forall Γ, forall (ind : inductive) (idx : nat) (u : Instance.t)
   (mind : mutual_inductive_body) (idecl : one_inductive_body)
   (cdecl : constructor_body),
 declared_constructor Σ (ind, idx) mind idecl cdecl ->
 ind_npars mind + context_assumptions (cstr_args cdecl) = 0 ->
 P Γ (tConstruct ind idx u)) ->
(forall Γ (ci : case_info) (type_info : predicate term) 
   (discr : term) (branches : list (branch term)),
 expanded Σ Γ discr ->
 P Γ discr ->
 Forall (expanded Σ Γ) type_info.(pparams) ->
 Forall (P Γ) type_info.(pparams) ->
 Forall (fun br : branch term => expanded Σ (repeat 0 #|br.(bcontext)| ++ Γ) (bbody br)) branches ->
 Forall (fun br : branch term => P (repeat 0 #|br.(bcontext)| ++ Γ)%list (bbody br)) branches ->
 P Γ (tCase ci type_info discr branches)) ->
(forall Γ (proj : projection) (t : term),
 expanded Σ Γ t -> P Γ t -> P Γ (tProj proj t)) ->
(forall Γ (mfix : mfixpoint term) (idx : nat) d args, 
  d.(rarg) < context_assumptions (decompose_prod_assum []  d.(dtype)).1 ->
  Forall (fun d => isLambda d.(dbody) /\ let ctx := List.rev (mapi (fun (i : nat) d => 1 + d.(rarg)) mfix) in expanded Σ (ctx ++ Γ) d.(dbody)) mfix -> 
  Forall (fun d => let ctx := List.rev (mapi (fun (i : nat) d => 1 + d.(rarg)) mfix) in P (ctx ++ Γ)%list d.(dbody)) mfix -> 
  Forall (expanded Σ Γ) args ->
  Forall (P Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  P Γ (tApp (tFix mfix idx) args)) ->
(forall Γ (mfix : mfixpoint term) (idx : nat), 
  Forall (fun d => expanded Σ (repeat 0 #|mfix| ++ Γ) d.(dbody)) mfix -> 
  Forall (fun d => P (repeat 0 #|mfix| ++ Γ)%list d.(dbody)) mfix -> 
  P Γ (tCoFix mfix idx)) ->
(forall Γ (ind : inductive) (c : nat) (u : Instance.t)
   (mind : mutual_inductive_body) (idecl : one_inductive_body)
   (cdecl : constructor_body) (args : list term),
 declared_constructor Σ (ind, c) mind idecl cdecl ->
 #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
 Forall (expanded Σ Γ) args ->
 Forall (P Γ) args ->
 P Γ(tApp (tConstruct ind c u) args)) -> forall Γ, forall t : term, expanded Σ Γ t -> P Γ t.
Proof.
  intros Σ P HRel HRel_app HVar HEvar HSort HCast HProd HLamdba HLetIn HApp HConst HInd HConstruct HCase HProj HFix HCoFix HConstruct_app.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  all: match goal with [H : Forall _ _ |- _] => let all := fresh "all" in rename H into all end.
  - eapply HRel_app; eauto. clear - f all. induction all; econstructor; eauto.
  - eapply HEvar; eauto. clear - f all. induction all; econstructor; eauto.
  - eapply HApp; eauto.  destruct f0; cbn in *; eauto. 
    clear - f all; induction all; econstructor; eauto.
  - eapply HCase; eauto.
    induction H; econstructor; eauto.
    induction all; econstructor; eauto.
  - assert (Forall (P Γ) args). { clear - f all. induction all; econstructor; eauto. }
    eapply HFix; eauto.
    revert H0. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; intuition eauto; split.
  - eapply HCoFix; eauto.
    revert all. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct_app; eauto.
    clear - all f. induction all; econstructor; eauto.
Qed.

Local Hint Constructors expanded : core.

Record expanded_constant_decl Σ (cb : Ast.Env.constant_body) : Prop :=
  { expanded_body : on_Some_or_None (expanded Σ []) cb.(Ast.Env.cst_body); }.
    (* expanded_type : expanded Σ [] cb.(Ast.Env.cst_type) }. *)

Definition expanded_context Σ Γ ctx :=
  ∥ All_fold (fun Δ d => ForOption (expanded Σ (repeat 0 #|Δ| ++ Γ)) d.(decl_body)) ctx ∥.

Record expanded_constructor_decl Σ mdecl cdecl :=
  { expanded_cstr_args : expanded_context Σ (repeat 0 (#|mdecl.(ind_params)| + #|mdecl.(ind_bodies)|)) cdecl.(cstr_args);
    (* expanded_cstr_indices : All (expanded Σ []) cdecl.(cstr_indices); *)
    expanded_cstr_type : expanded Σ (repeat 0 #|mdecl.(ind_bodies)|) cdecl.(cstr_type) }.
    
Record expanded_inductive_decl Σ mdecl idecl :=
  { (* expanded_ind_type : expanded Σ [] idecl.(ind_type); *)
    expanded_ind_ctors : Forall (expanded_constructor_decl Σ mdecl) idecl.(ind_ctors) }.

Record expanded_minductive_decl Σ mdecl :=
  { expanded_params : expanded_context Σ [] mdecl.(ind_params);
    expanded_ind_bodies : Forall (expanded_inductive_decl Σ mdecl) mdecl.(ind_bodies) }.

Definition expanded_decl Σ d :=
  match d with
  | Ast.Env.ConstantDecl cb => expanded_constant_decl Σ cb
  | Ast.Env.InductiveDecl idecl => expanded_minductive_decl Σ idecl
  end.
    
Inductive expanded_global_declarations (univs : ContextSet.t) : forall (Σ : Ast.Env.global_declarations), Prop :=
| expanded_global_nil : expanded_global_declarations univs []
| expanded_global_cons decl Σ : expanded_global_declarations univs Σ -> 
  expanded_decl {| Ast.Env.universes := univs; Ast.Env.declarations := Σ |} decl.2 ->
  expanded_global_declarations univs (decl :: Σ).

Definition expanded_global_env (g : Ast.Env.global_env) :=
  expanded_global_declarations g.(Ast.Env.universes) g.(Ast.Env.declarations).

Definition expanded_program (p : Ast.Env.program) :=
  expanded_global_env p.1 /\ expanded p.1 [] p.2.

Definition eta_expand_program (p : Ast.Env.program) : Ast.Env.program :=
  let Σ' := eta_expand_global_env p.1 in 
  (Σ', eta_expand p.1.(declarations) [] p.2).
  
Definition isFix_app t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition isRel_app t :=
  match fst (decompose_app t) with
  | tRel _ => true
  | _ => false
  end.
  
Lemma expanded_fold_lambda Σ Γ t l :
  expanded Σ Γ
    (fold_right (fun d (b : term) => tLambda d.(decl_name) d.(decl_type) b) t l) <->   expanded Σ (repeat 0 #|l| ++ Γ) t.
Proof.
  induction l as [ | []] in t, Γ |- *; cbn - [repeat] in *.
  - reflexivity.
  - replace (S #|l|) with (#|l| + 1) by lia.
    rewrite repeat_app. cbn. rewrite <- app_assoc. cbn.
    split.
    + inversion 1; subst. now eapply IHl.
    + intros. econstructor. now eapply IHl.
Qed.

Lemma expanded_mkApps_tConstruct Σ Γ mind idecl cdecl ind idx u args :
  declared_constructor Σ (ind, idx) mind idecl cdecl ->
  #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
  Forall (expanded Σ Γ) args ->
  expanded Σ Γ (mkApps (tConstruct ind idx u) args).
Proof.
  intros Hdecl Heq. unfold mkApps.
  destruct args eqn:E.
  - econstructor; eauto. cbn in *. lia.
  - eapply expanded_tConstruct_app; eauto.
Qed.

Lemma expanded_mkApps_tFix Σ Γ mfix idx d args :
  d.(rarg) < context_assumptions (decompose_prod_assum []  d.(dtype)).1 ->
  nth_error mfix idx = Some d ->
  #|args| >= S (d.(rarg)) ->
  Forall (fun d0 : def term => isLambda d0.(dbody) /\
    let ctx := List.rev (mapi (fun (_ : nat) (d1 : def term) => 1 + rarg d1) mfix) in expanded Σ (ctx ++ Γ) (dbody d0)) mfix ->
  Forall (expanded Σ Γ) args ->
  args <> [] ->
  expanded Σ Γ (mkApps (tFix mfix idx) args).
Proof.
  intros Hdecl Heq. unfold mkApps.
  destruct args eqn:E.
  - congruence.
  - intros. eapply expanded_tFix; eauto.
Qed.
  
Lemma expanded_mkApps_tFix_inv Σ Γ mfix idx args :
  expanded Σ Γ (mkApps (tFix mfix idx) args) ->
  Forall (fun d0 : def term => isLambda d0.(dbody) /\ let ctx := List.rev (mapi (fun (_ : nat) (d1 : def term) => 1 + rarg d1) mfix) in expanded Σ (ctx ++ Γ) (dbody d0)) mfix.
Proof.
  induction args.
  - cbn. inversion 1.
  - cbn. inversion 1; subst; cbn in *; try congruence.
Qed.

Lemma expanded_tApp_args Σ Γ t args :
  expanded Σ Γ (tApp t args) ->
  Forall (expanded Σ Γ) args.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma expanded_tApps_inv Σ Γ t args :
  expanded Σ Γ (tApp t args) ->
  forall args', #|args'| >= #|args| ->
  Forall (expanded Σ Γ) args' ->
  expanded Σ Γ (tApp t args').
Proof.
  intros. invs H.
  - econstructor; eauto. lia.
  - eauto.
  - eapply expanded_tFix; eauto.
    destruct args, args'; cbn in *; lia || congruence.
    lia.
  - eapply expanded_tConstruct_app; eauto.
    lia.
Qed.

Lemma expanded_mkApps_inv Σ Γ t args :
  expanded Σ Γ (mkApps t args) ->
  forall args', #|args'| >= #|args| ->
  Forall (expanded Σ Γ) args' ->
  expanded Σ Γ (mkApps t args').
Proof.
  intros.
  destruct args' in t, args, H, H0, H1 |- *.
  - destruct args; cbn in *; try lia. eauto.
  - destruct args; cbn in *.
    + destruct t; try now (eapply expanded_tApps_inv; eauto).
      * invs H. econstructor; eauto.
      * eapply expanded_tApps_inv. eauto. len; lia.
        eapply app_Forall; eauto. eapply expanded_tApp_args; eauto.
      * invs H. eapply expanded_tConstruct_app; eauto. cbn; lia.
    + destruct t; try now (eapply expanded_tApps_inv; eauto).
      eapply expanded_tApps_inv. eauto. len; lia.
      eapply app_Forall; eauto. eapply expanded_tApp_args in H.
      eapply Forall_app in H. eapply H.
Qed.

Lemma expanded_mkApps Σ Γ f args :
  expanded Σ Γ f -> Forall (expanded Σ Γ) args ->
  expanded Σ Γ (mkApps f args).
Proof.
  intros. 
  eapply expanded_mkApps_inv with (args := []); cbn; eauto. lia.
Qed.

Local Hint Rewrite repeat_length combine_length : len.
Local Hint Rewrite <- app_assoc : list.

Lemma apply_expanded Σ Γ Γ' t t' :
  expanded Σ Γ t -> Γ = Γ' -> t = t' -> expanded Σ Γ' t'.
Proof. intros; now subst. Qed.

Lemma ext_lift n m n' m' t :
  n' = n -> m' = m -> lift n m t = lift n' m' t.
Proof. intros; now subst. Qed.    

Lemma decompose_prod_lift t n m :
  #|(decompose_prod t).1.1| = #|(decompose_prod (lift n m t)).1.1|.
Proof.
  induction t in n, m |- *; cbn; try lia.
  destruct (decompose_prod t2) as [[]]; cbn in *.
  specialize (IHt2 n (S m)).
  destruct (decompose_prod (lift n (S m) t2)) as [[]]; cbn in *. lia.
Qed.

Lemma context_assumptions_lift' t Γ Γ' n m :
context_assumptions Γ = context_assumptions Γ' ->
context_assumptions (decompose_prod_assum Γ t).1 = 
context_assumptions (decompose_prod_assum Γ'  (lift n m t)).1.
Proof.
  intros Hlen.
  induction t in Γ, Γ', Hlen, n, m |- *; cbn; try lia.
  - eapply IHt2. cbn; lia.
  - eapply IHt3. cbn; lia.
Qed.

Lemma context_assumptions_lift t n m :
context_assumptions (decompose_prod_assum [] t).1 = 
context_assumptions (decompose_prod_assum [] (lift n m t)).1.
Proof.
  now eapply context_assumptions_lift'.
Qed.

Lemma isLambda_unlift n k t : isLambda (lift n k t) -> isLambda t.
Proof.
  destruct t; auto.
Qed.

Lemma expanded_unlift {Σ : global_env} Γ' Γ'' Γ t Γgoal :
  expanded Σ (Γ' ++ Γ'' ++ Γ) (lift #|Γ''| #|Γ'| t) ->
  (Γ' ++ Γ)%list = Γgoal ->
  expanded Σ Γgoal t.
Proof.
  intros Hexp <-.
  remember (Γ' ++ Γ'' ++ Γ)%list as Γ_.
  remember ((lift #|Γ''| #|Γ'| t)) as t_.
  induction Hexp in Γ', Γ'', Γ, HeqΓ_, Heqt_, t |- *; cbn; subst; destruct t; invs Heqt_; eauto.
  - rename n0 into n. econstructor. destruct (Nat.leb_spec #|Γ'| n).
    + rewrite !nth_error_app2 in H |- *; try lia.
      rewrite !nth_error_app2 in H; try lia. rewrite <- H. f_equal. lia.
    + rewrite nth_error_app1 in H |- *; try lia. eauto.
  - destruct t; invs H3. econstructor. 3:{ eapply Forall_map_inv in H0, H1. solve_all. }
    revert H. len. intros H. destruct (Nat.leb_spec #|Γ'| n0).
    + rewrite !nth_error_app2 in H |- *; try lia.
      rewrite !nth_error_app2 in H; try lia. rewrite <- H. f_equal. lia.
    + rewrite nth_error_app1 in H |- *; try lia. eauto.
    + revert Heq. len. lia.
  - econstructor. solve_all.
  - econstructor. rewrite app_comm_cons. eapply IHHexp; try reflexivity.
  - econstructor; eauto. rewrite app_comm_cons. eapply IHHexp2. 2: now simpl_list. eauto.  
  - econstructor; eauto. destruct t; cbn in *; eauto.
    solve_all.
  - econstructor; eauto. solve_all. cbn in H0.
    eapply All_map_inv in H0; solve_all. solve_all.
    specialize (b (repeat 0 #|bcontext x| ++ Γ')%list Γ'' Γ).
    autorewrite with list len in b. now  eapply b.
  - destruct t; invs H8.
    rewrite !nth_error_map in H5. destruct (nth_error mfix0 idx0) eqn:EE; cbn in H5; invs H5.
    eapply expanded_tFix. 
    + shelve.
    + eapply Forall_map_inv in H0, H1, H3. cbn in *. 
      solve_all. now apply isLambda_unlift in H0. rewrite app_assoc.      
      eapply b. autorewrite with list. f_equal. f_equal.
      rewrite mapi_map. eapply mapi_ext. intros. cbn. reflexivity.
      f_equal. now len.
    + solve_all.
    + destruct args0; cbn in *; congruence.
    + eauto.
    + revert H6. len. lia.
     Unshelve. revert H6. len. cbn in *. rewrite <- context_assumptions_lift in H. lia.
  - econstructor. solve_all. rewrite app_assoc.
    eapply b. autorewrite with len list. reflexivity. now len.
  - destruct t; invs H4.
    eapply expanded_tConstruct_app; eauto. revert H0.
    now len. solve_all.
Qed.

Lemma expanded_lift {Σ : global_env} Γ' Γ'' Γ t :
  expanded Σ (Γ' ++ Γ) t ->
  expanded Σ (Γ' ++ Γ'' ++ Γ) (lift #|Γ''| #|Γ'| t).
Proof.
  remember (Γ' ++ Γ)%list as Γ_.
  induction 1 in Γ', Γ'', Γ, HeqΓ_ |- *; cbn; eauto; subst.
  - econstructor. destruct (Nat.leb_spec #|Γ'| n).
    + rewrite !nth_error_app2 in H |- *; try lia.
      rewrite !nth_error_app2; try lia. rewrite <- H. f_equal. lia.
    + rewrite nth_error_app1 in H |- *; try lia. eauto.
  - econstructor. 3: solve_all.
    destruct (Nat.leb_spec #|Γ'| n).
    + rewrite !nth_error_app2 in H |- *; try lia.
      rewrite nth_error_app2; try lia. rewrite <- H.
      f_equal. lia.
    + rewrite nth_error_app1 in H |- *; try lia; eauto.
    + len. lia. 
  - econstructor; solve_all.
  - econstructor. rewrite app_comm_cons. eapply IHexpanded. now simpl_list.
  - econstructor; eauto. rewrite app_comm_cons. eapply IHexpanded2. now simpl_list.
  - econstructor; eauto. destruct f7; cbn in *; eauto.
    solve_all.
  - econstructor; eauto. solve_all. cbn; solve_all.
    solve_all. specialize (a (repeat 0 #|bcontext x| ++ Γ')%list Γ'' Γ).
    autorewrite with list len in a. now  eapply a.
  - eapply expanded_tFix. 
    + shelve.
    + solve_all. eapply apply_expanded. eapply a.
      now rewrite app_assoc. 
      autorewrite with list. f_equal. f_equal.
      rewrite mapi_map. eapply mapi_ext. intros. cbn. reflexivity.
      f_equal. now len.
    + solve_all.
    + destruct args; cbn in *; congruence.
    + now rewrite !nth_error_map, H5.
    + len. lia.
    Unshelve. cbn.
    rewrite <- !context_assumptions_lift. lia.
  - econstructor. solve_all.
    unshelve epose proof (a (_ ++ _)%list _ _ _). 5: now rewrite <- app_assoc.
    shelve. autorewrite with len list in H |- *. eapply H.
  - eapply expanded_tConstruct_app; eauto.
    now len. solve_all.
Qed.

Lemma expanded_lift' {Σ : global_env} Γ' Γ'' Γ t Γassum Γgoal n m :
  (Γ' ++ Γ)%list = Γassum ->
  (Γ' ++ Γ'' ++ Γ)%list = Γgoal ->
  #|Γ''| = n -> #|Γ'| = m ->
  expanded Σ Γassum t ->
  expanded Σ Γgoal (lift n m t).
Proof.
  intros. subst. now eapply expanded_lift.
Qed.

Lemma Forall_typing_spine_Forall {cf : config.checker_flags} Σ Γ (P : term -> Prop) t_ty l t' s :
  Forall_typing_spine Σ Γ
       (fun t _ : term => P t) t_ty l t' s ->
  Forall P l.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma nth_map' {A B} (f : A -> B) n l d d' :
  (d' = f d) ->
  nth n (map f l) d' = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Lemma decompose_prod12 t : 
  #| (decompose_prod t).1.1| = #|(decompose_prod t).1.2|.
Proof.
  induction t; cbn; try lia.
  do 2 destruct decompose_prod as [[]]. cbn in *. lia.
Qed.

Lemma mkApps_tRel:
forall (n : nat) (l : list term), l <> nil ->
mkApps (tRel n) (l) = tApp (tRel n) (l).
Proof.
  destruct l; cbn; try congruence.
Qed.

Lemma expanded_eta_single_tRel_app Σ0 n l n0 Γ' T :
  expanded Σ0
    (map
      (fun x : option (nat × term) =>
        match x with
        | Some p => let (n1, _) := p in n1
        | None => 0
        end) Γ') (eta_single (tRel n) [] T n0) ->
        Forall (expanded Σ0 
        (map
        (fun x : option (nat × term) =>
        match x with
        | Some p => let (n1, _) := p in n1
        | None => 0
        end) Γ')) l ->
        n0 <= context_assumptions (decompose_prod_assum [] T).1 ->
  expanded Σ0
    (map
      (fun x : option (nat × term) =>
        match x with
        | Some p => let (n1, _) := p in n1
        | None => 0
        end) Γ') (eta_single (tRel n) l T n0).
Proof.
  intros H Hl Hlen. unfold eta_single in *.
  rewrite expanded_fold_lambda in H |- *.
  rewrite Nat.sub_0_r in H. cbn in H.
  destruct n0.
  - cbn in *. invs H. simpl_list. eapply expanded_mkApps.
    eauto. solve_all.
    now rewrite lift0_id.
  - rewrite mkApps_tRel in H. 2:
    { replace (S n0) with (n0 + 1) by lia. rewrite rev_map_spec.
      rewrite seq_app, map_app, rev_app_distr. cbn. congruence. }
    invs H; cbn - [rev_map seq] in H2; try congruence.
    autorewrite with len list in H2 |- *.
    rewrite !firstn_length in H2 |- *.
    rewrite !List.skipn_length.
    (* rewrite nth_error_app2 in H2. 2: { len. destruct context_assumptions; lia. } *)
    autorewrite with len in H2 |- *.
    replace ((Init.Nat.min (S n0)
    (#|[]| + context_assumptions (decompose_prod_assum [] T).1))) with (S n0) in H2. 2:{
        len. rewrite rev_map_spec in H3. autorewrite with len in H3. cbn in H3.
        rewrite seq_length in H3. destruct context_assumptions; try lia.
    } cbn in H2.
    unfold lift0 at 1.
    rewrite mkApps_tRel. 2:{ destruct l; cbn - [rev_map]; try congruence. rewrite rev_map_spec. cbn. clear. destruct List.rev; cbn; try congruence. }
    econstructor.
    {
      replace ((Init.Nat.min (S n0 - #|l|)
      (#|[]| + context_assumptions (decompose_prod_assum [] T).1 - #|l|))) with (S n0 - #|l|). 2:{ len. destruct #|l|; lia. }
    assert (0 <=? n = true) as -> by now destruct n.
    rewrite <- H2.
    rewrite !nth_error_app2. 2,3: rewrite repeat_length; lia.
    f_equal. rewrite !repeat_length. lia.
    }
    revert H3. len. rewrite !seq_length. destruct l; cbn; lia.
    eapply app_Forall.
    + Opaque minus. solve_all. eapply @expanded_lift' with (Γ' := []). cbn; reflexivity.
      cbn; reflexivity. 2: reflexivity. len. lia. eauto.
    + change ((0 :: seq 1 n0)) with (seq 0 (S n0)) in *.
      assert (S n0 > #|l| \/ S n0 <= #|l|) as [HH | HH] by lia.
      assert (S n0 = S n0 - #|l| + #|l|) as EE by lia.
      2:{ replace (S n0 - #|l|) with 0 by lia. cbn. econstructor. }
      rewrite EE in H4.
      rewrite seq_app, rev_map_spec, map_app, rev_app_distr in H4.
      eapply Forall_app in H4 as []. rewrite Min.min_l. 2: len; lia.
      rewrite <- EE in H0.
    revert H0. len. rewrite !firstn_length, Min.min_l. 2:len;lia.
    rewrite rev_map_spec. intros.
    rewrite Forall_forall in H0 |- *. intros.
    specialize (H0 _ H1). rewrite <- in_rev in H1.
    eapply in_map_iff in H1 as (? & <- & [_ ?] % in_seq). 
    invs H0.
    econstructor. rewrite nth_error_app1. 2: rewrite repeat_length; lia.
    eapply nth_error_repeat. lia.
Qed.

 Lemma to_extended_list_k_map_subst:
  forall n (k : nat) (c : context) k',
    #|c| + k' <= k ->
    to_extended_list_k c k' = map (subst n k) (to_extended_list_k c k').
Proof.
  intros n k c k'.
  pose proof (to_extended_list_k_spec c k').
  symmetry. solve_all.
  destruct H as [x' [-> Hx']]. intuition. simpl.
  destruct (leb_spec_Set k x').
  - lia.
  - reflexivity.
Qed.

 Lemma subst_cstr_concl_head ind u mdecl (arity : context) args :
 let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
 let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
 inductive_ind ind < #|ind_bodies mdecl| ->
 subst s (#|arity| + #|ind_params mdecl|)
       (subst_instance u (mkApps head (to_extended_list_k (ind_params mdecl) #|arity| ++ args)))
 = mkApps (tInd ind u) (to_extended_list_k (ind_params mdecl) #|arity| ++
                       map (subst s (#|arity| + #|ind_params mdecl|)) (map (subst_instance u) args)).
Proof.
 intros.
 rewrite subst_instance_mkApps, subst_mkApps.
 f_equal.
 - subst head. unfold subst_instance. cbn[subst_instance_constr].
   rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)); cbn; try lia; auto.
   subst s. rewrite inds_spec, rev_mapi, nth_error_mapi.
   elim nth_error_spec.
   + intros. simpl.
     f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
   + rewrite List.rev_length. lia.
 - rewrite !map_app. f_equal.
   rewrite map_subst_instance_to_extended_list_k.
   erewrite to_extended_list_k_map_subst at 2.
   + now rewrite Nat.add_comm.
   + lia.
Qed.

Lemma decompose_type_of_constructor :
  forall cf: config.checker_flags
, forall Σ0: global_env_ext
, forall wfΣ: wf Σ0.1
, forall ind: inductive
, forall i: nat
, forall u: Instance.t
, forall mdecl: mutual_inductive_body
, forall idecl: one_inductive_body
, forall cdecl: constructor_body
, forall isdecl': declared_constructor Σ0.1 (ind, i) mdecl idecl cdecl, 
context_assumptions
     (decompose_prod_assum [] (type_of_constructor mdecl cdecl (ind, i) u)).1 = ind_npars mdecl + context_assumptions (cstr_args cdecl).
Proof.
  intros. red in wfΣ.
  unfold type_of_constructor.
  destruct isdecl' as [[Hmdecl Hidecl] Hcdecl]. red in Hmdecl.
  eapply lookup_on_global_env in Hmdecl; eauto.
  destruct Hmdecl as (Σ' & wfΣ' & Hext & [Hind Hparam Hnpars Hvar]).
  unfold type_of_constructor.
  eapply nth_error_alli in Hind; eauto.
  destruct Hind.
  red in onConstructors.
  eapply All2_nth_error_Some in onConstructors; eauto.
  destruct onConstructors as (univs & Hnth & H).
  destruct H.
  rewrite cstr_eq. cbn.
  rewrite !subst_instance_it_mkProd_or_LetIn.
  rewrite !subst_it_mkProd_or_LetIn.
  rewrite <- it_mkProd_or_LetIn_app.
  rewrite !decompose_prod_assum_it_mkProd.
  - cbn. rewrite app_nil_r, !context_assumptions_app. now len.
  - unfold cstr_concl, cstr_concl_head. rewrite Nat.add_0_r. len.
    rewrite subst_cstr_concl_head. 
    eapply is_ind_app_head_mkApps.
    eapply nth_error_Some_length; eauto.
Qed.

Lemma wf_fixpoint_rarg :
  forall cf: config.checker_flags
, forall Σ0: global_env_ext
, forall wfΣ: wf Σ0.1
, forall mfix: list (def term)
, forall decl: def term
, forall H2: wf_fixpoint Σ0.1 mfix, In decl mfix ->
decl.(rarg) < context_assumptions (decompose_prod_assum []  decl.(dtype)).1.
Proof.
  intros.
  unfold wf_fixpoint in H2.
  eapply andb_and in H2. destruct H2 as [_ H2].
  destruct map_option_out eqn:E; try congruence.
  destruct l eqn:E2; try congruence.
  rewrite <- E2 in *. clear E2 H2 k l0.
  induction mfix in l, E, H |- *.
  - inversion H.
  - cbn in E. destruct (check_one_fix a) eqn:Ea; try congruence.
    destruct H as [-> | H].
    + unfold check_one_fix in Ea. destruct decl; cbn.
      destruct (decompose_prod_assum) eqn:Eprod; try congruence. unfold destInd in Ea.
      destruct nth_error eqn:Enth; try congruence.
      eapply nth_error_Some_length in Enth.
      revert Enth. now len.
    + destruct map_option_out eqn:?; try congruence. eapply IHmfix; eauto.
Qed.

From Equations Require Import Equations.

Lemma typing_wf_fixpoint {cf : config.checker_flags} Σ0 Γ0 mfix idx t_ty  :
   Σ0;;; Γ0 |- tFix mfix idx : t_ty -> wf_fixpoint Σ0 mfix.
Proof.
  intros H.
  depind H; eauto.
Qed.

Lemma isLambda_eta_expand Σ Γ t : 
  isLambda t -> isLambda (eta_expand Σ Γ t).
Proof. destruct t; auto. Qed.

(* Lemma context_assumptions_decompose t :
context_assumptions (decompose_prod_assum [] t).1 <=
#|(decompose_prod t).1.2|.
Proof.
  setoid_rewrite <- Nat.add_0_r at 2. rewrite Nat.add_comm.
  change 0 with (context_assumptions []).
  generalize (@nil context_decl).
  induction t; cbn; intros; try lia; len. 
  - destruct (decompose_prod t2) as [[]]; cbn in *.
    rewrite IHt2. cbn; lia.
  - rewrite IHt3. cbn. lia. *)
    

Lemma eta_expand_expanded {cf : config.checker_flags} {Σ : global_env_ext} Γ Γ' t T :
  wf Σ ->
  typing Σ Γ t T ->
  Forall2 (fun x y => match x with Some (n, t) => y.(decl_type) = t /\ context_assumptions (decompose_prod_assum [] y.(decl_type)).1 >= n | None => True end) Γ' Γ ->
  expanded Σ (map (fun x => match x with Some (n, _) => n | None => 0 end ) Γ') (eta_expand Σ.1.(declarations) Γ' t).
Proof.
  intros wf Hty. revert Γ'.
  eapply @typing_ind_env with (t := t) (Σ := Σ) (P := fun Σ Γ t T => forall Γ',  Forall2 (fun (x : option (nat × term)) (y : context_decl) => match x with
                                                               | Some (_, t0) => decl_type y = t0 /\ _
                                                               | None => True
                                                               end) Γ' Γ ->
  expanded Σ (map (fun x : option (nat × term) => match x with
                                                  | Some (n, _) => n
                                                  | None => 0
                                                  end) Γ') (eta_expand (declarations Σ) Γ' t)
                                                ) (PΓ := fun _ _ _ => True); intros; try now (cbn; eauto).
  - cbn. eapply Forall2_nth_error_Some_r in H1 as (? & ? & ?); eauto.
    rewrite H1.
    destruct x as [[] | ]. 
    + destruct H2. unfold eta_single. cbn.
      eapply expanded_fold_lambda.
      rewrite !Nat.sub_0_r. len. rewrite firstn_length. len.
      destruct n0.
      * cbn. econstructor. now rewrite nth_error_map, H1. 
      * rewrite seq_S,rev_map_spec, map_app, rev_app_distr. subst.
         rewrite <- context_assumptions_lift, !Min.min_l; try lia.
        econstructor.
        -- rewrite nth_error_app2. 2: rewrite repeat_length; lia.
           rewrite repeat_length. replace (S n0 + n - S n0) with n by lia.
           now rewrite nth_error_map,  H1. 
        -- len. now rewrite seq_length.
        -- eapply Forall_forall. intros x [ | (? & <- & [_ ?] % in_seq) % in_rev % in_map_iff]; subst.
           all: econstructor; rewrite nth_error_app1; [eapply nth_error_repeat; lia | rewrite repeat_length; lia].
    + econstructor. now rewrite nth_error_map, H1.
  - cbn. econstructor. eapply (H2 (up Γ')); econstructor; eauto.
  - cbn. econstructor. eauto. eapply (H3 (up Γ')); econstructor; eauto.
  - specialize (H _ H2).
    assert (Forall(fun t : term => expanded Σ0 (map
    (fun x : option (nat × term) =>
     match x with
     | Some p => let (n, _) := p in n
     | None => 0
     end) Γ') (eta_expand Σ0.(declarations) Γ' t)) l). { 
       clear H1. clear X. induction X0; econstructor; eauto. }
    destruct t0; cbn.
    all: try now eapply expanded_mkApps; [ eauto | solve_all ].
    + cbn in H.
      destruct (nth_error Γ' n) eqn:E; eauto.
      destruct o; eauto.
      destruct p. cbn in *.
      eapply expanded_eta_single_tRel_app; eauto. solve_all.
      eapply Forall2_nth_error_Some_l in H2 as (? & ? & ?). 2: eauto. 
      cbn in *. 
      destruct H4.
      rewrite <- context_assumptions_lift. subst. lia.
      cbn. eapply expanded_mkApps. constructor.
      now rewrite nth_error_map, E; cbn.
      solve_all.
    + cbn in H. unfold eta_constructor in *.
      destruct lookup_global as [[] | ] eqn:E1; eauto.
      destruct nth_error eqn:E2; eauto.
      destruct (nth_error (ind_ctors o) idx) eqn:E3; eauto. 
      unfold eta_single in H. eapply expanded_fold_lambda.
      rewrite Nat.sub_0_r in H.
      unfold mkApps in H. destruct (ind_npars m + context_assumptions (cstr_args c)) eqn:EE.
      * cbn in H. inversion H; subst. cbn.
        simpl_list. destruct l.
        -- cbn. econstructor; eauto.
        -- cbn. eapply expanded_tConstruct_app; eauto. cbn. now rewrite H8.
           rewrite lift0_id. setoid_rewrite map_ext. 3: eapply lift0_p. rewrite map_id.
           eapply Forall_typing_spine_Forall in X0.
           rewrite <- map_cons. revert X0. generalize (t0 :: l). intros l' X0.
           solve_all. eapply H4. solve_all. reflexivity.
      * eapply expanded_mkApps_tConstruct. split. split. red. all: eauto.
        rewrite rev_map_spec. simpl_list. rewrite EE. lia. eapply Forall_typing_spine_Forall in X0.
        assert ((context_assumptions
        (decompose_prod_assum [] (type_of_constructor m c (ind, idx) u)).1) = ind_npars m + context_assumptions (cstr_args c)) as E. { 
          eapply decompose_type_of_constructor; eauto.
          split. split. red. all: eauto. }
        eapply app_Forall.
        -- Opaque minus. solve_all. eapply @expanded_lift' with (Γ' := []). 2: reflexivity. reflexivity.
           2: reflexivity. len.
           { rewrite !firstn_length, !List.skipn_length. len.
             rewrite E, EE. lia.
           }
           cbn. eauto.
        -- rewrite rev_map_spec. eapply Forall_rev. 
           eapply Forall_forall. intros ? (? & <- & ?) % in_map_iff. econstructor.
           eapply in_seq in H4 as [_ H4].
           len. rewrite nth_error_app1. 2: len.
           eapply nth_error_repeat. cbn in *.
           rewrite !firstn_length, !List.skipn_length. len. rewrite E, EE.
           rewrite map_length in H4. lia.
           rewrite !firstn_length, !List.skipn_length. len. rewrite E, EE.
           rewrite map_length in H4. lia.
    + cbn in H. unfold eta_fixpoint in *.
      rewrite nth_error_map in H |- *.
      destruct (nth_error mfix idx) eqn:Eid; eauto.
      cbn in *. 
      eapply expanded_fold_lambda. 
      
      eapply expanded_mkApps_tFix; fold lift.
      2:{rewrite !nth_error_map, Eid. reflexivity. }
      ++ cbn. rewrite <- context_assumptions_lift. 
        eapply wf_fixpoint_rarg; eauto. 2: eapply nth_error_In; eauto.
        clear - X. depind X; eauto.
      ++ len. rewrite seq_length. lia.
      ++ unfold eta_single in H.
         rewrite expanded_fold_lambda in H. cbn. simpl_list.
         cbn-[lift] in H. rewrite Nat.sub_0_r in H.
         unfold lift in H. fold lift in H.
         eapply expanded_mkApps_tFix_inv in H.
         eapply Forall_forall.
         intros ? (? & <- & (? & <- & ?) % in_map_iff) % in_map_iff. cbn.
         
         
         eapply Forall_forall in H. 2:{ 
         eapply in_map_iff. eexists. split. reflexivity. eapply in_map_iff. eexists. split. cbn. reflexivity. eauto. }
         cbn in H.
         revert H. len. intros [Hl H]. split.
         { eapply isLambda_unlift in Hl. now eapply isLambda_lift. }

         eapply typing_wf_fixpoint in X. eapply wf_fixpoint_rarg in X. 2: eauto. 2: eapply nth_error_In; eauto.

         assert (#|l| > S (rarg d) \/ #|l| <= S (rarg d) )  as [He | He] by lia.
         { replace ((S (rarg d) - #|l|)) with 0 by lia. cbn. rewrite lift0_id.
          eapply expanded_unlift. 2: reflexivity.
          eapply apply_expanded; eauto; len. 2:{ f_equal. instantiate (1 := repeat 0 (S (rarg d))). now len. }
          simpl_list. rewrite !app_assoc. f_equal. f_equal.
          2:{ f_equal. rewrite !firstn_length. len.
              destruct context_assumptions; lia.
           }
          f_equal.  rewrite !mapi_map. now eapply mapi_ext. }

         eapply expanded_unlift with (Γ'' :=  repeat 0 #|l|). 2: now rewrite <- app_assoc.
         rewrite simpl_lift. 2:{ len. rewrite !firstn_length, !List.skipn_length. lia. }
         2:{ len. lia. }
         eapply apply_expanded. eauto.
         simpl_list. f_equal. f_equal.
         ** rewrite !mapi_map. now eapply mapi_ext.
         ** rewrite !firstn_length, !List.skipn_length.
            rewrite app_assoc. f_equal.
            rewrite <- repeat_app. f_equal. len.
            destruct context_assumptions;
            lia.
         ** f_equal. len. lia.
      ++ eapply Forall_typing_spine_Forall in X0. eapply app_Forall.
         ** solve_all. eapply @expanded_lift' with (Γ' := []). all: try now reflexivity. 2: eauto.
            len. rewrite !firstn_length, !List.skipn_length.
            eapply typing_wf_fixpoint in X.
            eapply wf_fixpoint_rarg in X. 2: eauto. 2: eapply nth_error_In; eauto.
            len. lia.
         ** rewrite rev_map_spec. eapply Forall_rev. 
            eapply Forall_forall. intros ? (? & <- & ?) % in_map_iff. econstructor.
            eapply in_seq in H4 as [_ H4]. autorewrite with len in H4 |- *.
            rewrite !firstn_length, !List.skipn_length.
            rewrite nth_error_app1. eapply nth_error_repeat.
            -- len. 
               eapply Nat.lt_le_trans. eauto. cbn.
               eapply typing_wf_fixpoint in X.
               eapply wf_fixpoint_rarg in X. 2: eauto. 2: eapply nth_error_In; eauto.
               lia.
            -- len. 
               eapply Nat.lt_le_trans. eauto. cbn.
               eapply typing_wf_fixpoint in X.
               eapply wf_fixpoint_rarg in X. 2: eauto. 2: eapply nth_error_In; eauto.
               lia.
      ++ destruct l; cbn in *; try congruence. 
      ++ cbn. eauto.
  - cbn. pose proof isdecl as isdecl'. destruct isdecl as [[]]. red in H2.
    unfold lookup_env in H2.
    unfold eta_constructor. unfold fst_ctx in *. cbn in *. rewrite H2, H3, H4.
    eapply expanded_fold_lambda. rewrite Nat.sub_0_r.
    eapply expanded_mkApps_tConstruct; eauto.
    rewrite rev_map_spec. now simpl_list. rewrite rev_map_spec, <- List.map_rev.
    eapply Forall_forall. intros ? (? & <- & ?) % in_map_iff. econstructor.
    eapply in_rev, in_seq in H5 as [_ ?]. cbn in *. len.
    rewrite !firstn_length. len.
    assert ((context_assumptions
    (decompose_prod_assum []
       (type_of_constructor mdecl cdecl (ind, i) u)).1) = ind_npars mdecl + context_assumptions (cstr_args cdecl)) as ->. {
      eapply decompose_type_of_constructor; eauto.
    }
    rewrite nth_error_app1. now rewrite nth_error_repeat. rewrite repeat_length. lia.
  - cbn. econstructor; eauto.
    * unfold map_branches. solve_all.
      clear -X1 H9.
      set (Γ'' := map _ Γ'). cbn.
      enough (All (expanded Σ0 Γ'') (map (eta_expand (declarations Σ0) Γ') (pparams p ++ indices))).
      now rewrite map_app in X; eapply All_app in X as [].
      eapply All_map.
      induction X1.
      + constructor.
      + constructor; auto. eapply t0. solve_all.
      + auto.
      
    * solve_all.
      specialize (b (repeat None #|bcontext y| ++ Γ'))%list.
      rewrite map_app, map_repeat in b. eapply b.
      eapply Forall2_app; solve_all.
      
      assert (#| (case_branch_context_gen (ci_ind ci) mdecl (pparams p) 
      (puinst p) (bcontext y) x)| = #|bcontext y|). { clear - a0.
        unfold case_branch_context_gen. rewrite map2_length.
        rewrite Min.min_l; try lia. eapply All2_length in a0.
        unfold inst_case_context. unfold subst_context.
        unfold subst_instance, subst_instance_context, map_context.
        rewrite fold_context_k_length, map_length. unfold aname. lia.
      } revert H10. generalize ((case_branch_context_gen (ci_ind ci) mdecl (pparams p) 
      (puinst p) (bcontext y) x)). clear.
      induction #|bcontext y|; intros []; cbn; intros; try congruence; econstructor; eauto.
    - cbn. rewrite nth_error_map, H0. cbn. unfold eta_fixpoint. unfold fst_ctx in *. cbn in *.
    eapply expanded_fold_lambda.
    assert (#|(decompose_prod (dtype decl)).1.1| = #|(decompose_prod (dtype decl)).1.2|) as E1. { eapply decompose_prod12. }
    assert (rarg decl < context_assumptions (decompose_prod_assum [] (dtype decl)).1) as E2. { eapply wf_fixpoint_rarg; eauto. now eapply nth_error_In. }
    eapply expanded_mkApps_tFix.
    + shelve.
    + fold lift. rewrite !nth_error_map, H0. cbn. len. reflexivity.
    + len. rewrite seq_length. lia.
    + fold lift. len.
      assert (Forall (fun x => isLambda (dbody x)) mfix).
      { apply andb_and in H2. destruct H2 as [isl _]. solve_all. }
      solve_all.
      { now eapply isLambda_lift, isLambda_eta_expand. }
      destruct a as ((((Hbo1 & Hbo2) & mk) & _) & tt & s & e & Hs1 & Hs2).
      rewrite !firstn_length. rewrite !Nat.min_l; try lia.
      eapply expanded_lift'.
      5: eapply Hbo2. 2: reflexivity. 2: now len.
      2: now len.
      { rewrite map_app. f_equal. rewrite map_rev. f_equal. now rewrite !mapi_map, map_mapi. }
      eapply Forall2_app; solve_all.
      subst types. unfold Typing.fix_context.
      eapply All2_rev. eapply All2_mapi. eapply All_All2_refl, Forall_All, Forall_forall.
      intros. split. reflexivity. cbn.
      rewrite <- context_assumptions_lift.
      eapply wf_fixpoint_rarg in H4; eauto. len; lia.
      Unshelve. cbn.  rewrite <- context_assumptions_lift. lia.
    + cbn - [rev_map seq]. rewrite rev_map_spec. eapply Forall_rev.
      eapply Forall_forall. intros ? (? & <- & ?) % in_map_iff. econstructor.
      eapply in_seq in H4 as [_ ?]. cbn in *. len.
      rewrite !firstn_length.
      rewrite nth_error_app1. eapply nth_error_repeat.
      len; lia.
      rewrite repeat_length. len; lia.
    + cbn - [rev_map seq]. rewrite rev_map_spec. cbn. rewrite Nat.sub_0_r. cbn. destruct List.rev; cbn; congruence.
  - cbn. econstructor; eauto. eapply All_Forall, All_map, All_impl. eapply X. intros ? ((((Hbo1 & Hbo2) & mk) & _) & tt & s & e & Hs1 & Hs2). cbn.
     specialize (Hbo2 (repeat None #|mfix| ++ Γ'))%list.
     rewrite map_app, map_repeat in Hbo2. len. eapply Hbo2.
     eapply Forall2_app; eauto. unfold types.
     assert (#|Typing.fix_context mfix| = #|mfix|). { unfold Typing.fix_context. now len. }
     revert H4. generalize (Typing.fix_context mfix). clear.
     induction #|mfix|; intros []; cbn; intros; try congruence; econstructor; eauto.
  - eapply typing_wf_local; eauto.
Qed.

Arguments tVar _%bs.

Require Import ssreflect.
Open Scope bs_scope.

Fixpoint lookup_global_env (Σ : global_declarations) (kn : kername) {struct Σ} : option (global_decl × global_declarations)  :=
  match Σ with
  | [] => None
  | d :: tl => if kn == d.1 then Some (d.2, tl) else lookup_global_env tl kn
  end.

Lemma lookup_lookup_global_env Σ kn decl : 
  lookup_global Σ kn = Some decl -> ∑ Σ', lookup_global_env Σ kn = Some (decl, Σ').
Proof.
  induction Σ => // /=.
  case: eqb_specT => eq.
  intros [= <-]. subst kn.
  now eexists.
  auto.
Qed.

Lemma lookup_global_env_lookup Σ kn dΣ : 
  lookup_global_env Σ kn = Some dΣ -> lookup_global Σ kn = Some dΣ.1.
Proof.
  induction Σ => // /=.
  case: eqb_specT => eq.
  intros [= <-]. subst kn.
  reflexivity.
  auto.
Qed.

Lemma lookup_lookup_global_env_None Σ kn : 
  lookup_global Σ kn = None <-> lookup_global_env Σ kn = None.
Proof.
  induction Σ => // /=.
  case: eqb_specT => eq //.
Qed.

Lemma eta_lookup_global Σ kn decl :
  lookup_global Σ kn = Some decl ->
  ∑ Σ', lookup_global (eta_global_declarations Σ) kn = Some (eta_global_declaration Σ' decl).
Proof.
  move/lookup_lookup_global_env => [] Σ' hl.
  exists Σ'. move: hl.
  induction Σ; cbn => //.
  destruct a as [kn' []] => /=.
  case: eqb_spec. intros ->. intros [= <- <-] => //.
  intros neq. auto.
  case: eqb_spec. intros ->. intros [= <- <-] => //.
  intros neq. auto.
Qed.

Lemma eta_lookup_global_error Σ ind :
   lookup_global (eta_global_declarations Σ) (inductive_mind ind) = None -> 
   lookup_global Σ (inductive_mind ind) = None.
Proof.
  induction Σ; cbn => //.
  destruct a as [kn []] => /=.
  destruct (eqb_spec (inductive_mind ind) kn) => //.
  destruct (eqb_spec (inductive_mind ind) kn) => //.
Qed.

Lemma eta_declared_constructor {Σ ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  ∑ Σ', 
    (* extends_decls Σ' Σ × *)
    declared_constructor (eta_expand_global_env Σ) ind (eta_minductive_decl Σ' mdecl) 
    (eta_inductive_decl Σ' mdecl idecl) (eta_constructor_decl Σ' mdecl cdecl).
Proof.
  rewrite /declared_constructor.
  intros [[] ?].
  move: H. rewrite /declared_inductive /declared_minductive /lookup_env /=.
  destruct (lookup_global Σ.(declarations) _) eqn:heq => //.
  move: (eta_lookup_global Σ.(declarations) (inductive_mind ind.1) g heq) => [Σ'] hl.
  intros [= ->]. exists Σ'. rewrite hl; split => //.
  split => //. rewrite nth_error_map H0 //.
  rewrite nth_error_map H1 //.
Qed.

Lemma expanded_env_irrel univs decls Γ t : 
  let Σ := {| universes := univs; declarations := decls |} in
  expanded Σ Γ t -> 
  let Σ' := {| universes := univs; declarations := eta_global_declarations decls |} in
  expanded Σ' Γ t.
Proof.
  intros Σ exp Σ'.
  move: exp.
  induction 1 using expanded_ind.
  all: try solve [constructor; auto].
  - eapply expanded_tRel_app; tea.
  - eapply eta_declared_constructor in H as [Σ'' decl'].
    eapply expanded_tConstruct. tea. cbn.
    unfold eta_context.
    rewrite context_assumptions_fold_context_k_defs //.
  - eapply expanded_tFix; tea. solve_all.
  - eapply eta_declared_constructor in H as [Σ'' decl'].
    eapply expanded_tConstruct_app; tea. cbn.
    rewrite context_assumptions_fold_context_k_defs //.
Qed.

Lemma expanded_context_env_irrel univs decls Γ t : 
  let Σ := {| universes := univs; declarations := decls |} in
  expanded_context Σ Γ t -> 
  let Σ' := {| universes := univs; declarations := eta_global_declarations decls |} in
  expanded_context Σ' Γ t.
Proof.
  intros Σ exp Σ'.
  move: exp. unfold expanded_decl.
  unfold expanded_context.
  intros []; split. eapply All_fold_impl; tea; cbn => ?? []; constructor.
  eapply expanded_env_irrel; tea.
Qed.

Lemma expanded_decl_env_irrel univs decls t : 
  let Σ := {| universes := univs; declarations := decls |} in
  expanded_decl Σ t -> 
  let Σ' := {| universes := univs; declarations := eta_global_declarations decls |} in
  expanded_decl Σ' t.
Proof.
  intros Σ exp Σ'.
  move: exp. unfold expanded_decl.
  destruct t => //.
  intros []. constructor.
  destruct (cst_body c) => //. cbn in *.
  now eapply expanded_env_irrel.
  intros []. split.
  eapply expanded_context_env_irrel; tea.
  solve_all.
  destruct H. constructor.
  solve_all. destruct H; split.
  eapply expanded_context_env_irrel; tea.
  eapply expanded_env_irrel; tea.
Qed.

Coercion wf_ext_wf : wf_ext >-> wf.
Implicit Types (cf : checker_flags).
Lemma All_fold_fold_context_k_defs P (f : nat -> term -> term) Γ :
  All_fold P (fold_context_k_defs f Γ) <~>
  All_fold (fun Γ d => P (fold_context_k_defs f Γ) (map_decl_body (f #|Γ|) d)) Γ.
Proof.
  split.
  - induction Γ; auto.
    * intros; constructor.
    * cbn. intros H; depelim H. constructor; auto.
  - induction Γ; auto.
    * intros; constructor.
    * intros H; depelim H. constructor; auto.
Qed.

#[export] Hint Rewrite @fold_context_k_defs_length @context_assumptions_fold_context_k_defs : len.

Existing Class Typing.wf_ext.

Lemma eta_expand_context {cf} {Σ ctx} {wfΣ : Typing.wf_ext Σ} :
  on_context (lift_typing typing) Σ ctx -> 
  expanded_context Σ [] (eta_context Σ.(declarations) 0 ctx).
Proof.
  unfold on_context.
  red. intros wf. sq.
  rewrite /eta_context.
  eapply All_fold_fold_context_k_defs.
  induction wf; cbn; auto; try constructor; auto.
  cbn. constructor.
  cbn. constructor.
  len. rewrite app_nil_r.
  destruct t0 as ((t0 & _) & t1).
  forward (eta_expand_expanded (Σ := Σ) Γ (repeat None #|Γ|) _ _ wfΣ t0).
  clear. induction Γ; cbn; constructor; auto.
  now rewrite map_repeat.
Qed.

Lemma eta_expand_context_sorts {cf} {Σ ctx ctx' cunivs} {wfΣ : Typing.wf_ext Σ} :
  sorts_local_ctx (lift_typing typing) Σ ctx ctx' cunivs -> 
  expanded_context Σ (repeat 0 #|ctx|) (eta_context Σ.(declarations) #|ctx| ctx').
Proof.
  intros hs. constructor.
  eapply All_fold_fold_context_k_defs. cbn. len. 
  induction ctx' in hs, cunivs |- *; cbn; auto.
  constructor; eauto.
  cbn in hs. destruct a as [na [b|] ty]; try destruct hs as [hs ((Hb&mk)& u&e&Ht)].
  specialize (IHctx' cunivs hs). constructor; auto.
  constructor. len. rewrite repeat_app.
  epose proof (eta_expand_expanded (Σ := Σ) _ (repeat None (#|ctx'| + #|ctx|)) _ _ wfΣ Hb).
  forward H.
  clear. rewrite -app_context_length.
  induction (_ ,,, _); cbn; constructor; auto.
  now rewrite map_repeat !repeat_app in H.
  destruct cunivs => //. destruct hs.
  constructor; eauto. constructor.
Qed.

Lemma eta_context_length g n ctx : #|eta_context g n ctx| = #|ctx|.
Proof. now rewrite /eta_context; len. Qed.
#[export] Hint Rewrite @eta_context_length : len.

Lemma eta_expand_global_decl_expanded {cf : checker_flags} g kn d :
  Typing.wf_ext g ->
  on_global_decl cumul_gen (lift_typing typing) g kn d ->
  expanded_decl g (eta_global_declaration g.(declarations) d).
Proof.
  intros wf ond.
  destruct d; cbn in *.
  - destruct ond as (onbo & onty).
    destruct c as [na body ty rel]; cbn in *.
    destruct body. constructor => //; cbn.
    apply (eta_expand_expanded (Σ := g) [] [] t na wf onbo.1). constructor.
    destruct onty as (s & e & Hs). constructor => //.
  - destruct ond as [onI onP onN onV].
    constructor. cbn.
    eapply eta_expand_context => //.
    solve_all. cbn. eapply All_map, Alli_All; tea => n idecl oni.
    constructor.
    cbn. solve_all.
    pose proof oni.(onConstructors).
    red in X.
    eapply All2_All_left; tea; cbn => cdecl cunivs onc.
    constructor. cbn. len.
    pose proof onc.(on_cargs).
    eapply eta_expand_context_sorts in X0. now len in X0.
    len. len. 
    pose proof onc.(on_ctype). destruct X0 as (_ & s & e & Hs).
    epose proof (eta_expand_expanded (Σ := g) _ (repeat None #|ind_bodies m|) _ _ wf Hs).
    forward H. rewrite -arities_context_length.
    clear. induction (arities_context _); constructor; auto.
    now rewrite map_repeat in H.
Qed.

Lemma eta_expand_global_env_expanded {cf : checker_flags} g :
  Typing.wf g ->
  expanded_global_env (eta_expand_global_env g).
Proof.
  destruct g as [univs Σ]; cbn.
  unfold expanded_global_env. cbn.
  unfold Typing.wf, Typing.on_global_env. intros [onu ond].
  cbn in *.
  induction ond; cbn; constructor; auto.
  set (Σ' := {| universes := univs; declarations := Σ |}).
  cbn. epose proof (eta_expand_global_decl_expanded (Σ', udecl) kn d).
  cbn in H.
  eapply expanded_decl_env_irrel, H.
  split => //. exact o0.
Qed.
