(** * Eta-expansion and proof generation **)

(** We perform eta-expansion of template-coq terms and generate proofs that
    we terms are equal to the originals. Since eta-conversion is part of the
    Coq's conversion, the proof is essentially [eq_refl].
    All dependencies are also expanded.*)

From Coq Require Import List PeanoNat Bool Ascii String.
From MetaCoq.Template Require Import Kernames All Ast Typing.

Open Scope string.
Open Scope nat.

Import Template.Ast.
Import ListNotations.

From ReductionEffect Require Import PrintingEffect.

Section Eta.
   Context (Σ : global_env).

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
    let remaining := skipn #|args| (decompose_prod ty).1.2 in
    let remaining_names := skipn #|args| (decompose_prod ty).1.1 in
    let remaining_subst := mapi (subst (rev args)) remaining in 
    fold_right (fun '(nm,ty) b => Ast.tLambda nm ty b) (mkApps t (prev_args ++ eta_args)) (combine remaining_names remaining_subst). 

    (* 
 Definition eta_single' (t : Ast.term) (args : list Ast.term) (ty : Ast.term) (count : nat): term :=
    let needed := count - #|args| in
    let prev_args := map (lift0 needed) args in
    let eta_args := rev_map tRel (seq 0 needed) in
    let cut_ty := remove_top_prod ty #|args| in
    let subst_ty := subst (rev args) 0 cut_ty in
    let remaining := (decompose_prod subst_ty).1.2 in
    let print := print remaining in
    let remaining_names := (decompose_prod subst_ty).1.1 in
    fold_right (fun '(nm,ty) b => Ast.tLambda nm ty b) (mkApps t (prev_args ++ eta_args)) (combine remaining_names remaining). *)
  
  Definition eta_constructor (ind : inductive) c u args :=
      match lookup_env Σ ind.(inductive_mind) with
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
  
  Fixpoint eta_expand (t : term) : term :=
    match t with
    | tApp hd args =>
      match hd with
      | tConstruct ind c u =>
        match eta_constructor ind c u args with 
        | Some res => res
        | None => tVar ("Error: lookup of an inductive failed for "
                       ++ string_of_kername ind.(inductive_mind))
        end
      | _ => mkApps (eta_expand hd) (map eta_expand args)
    end
    | tEvar n ts => tEvar n (map eta_expand ts)
    | tLambda na ty body => tLambda na ty (eta_expand body)
    | tLetIn na val ty body => tLetIn na (eta_expand val) ty (eta_expand body)
    | tCase p ty disc brs =>
      tCase p ty (eta_expand disc) (map_branches eta_expand brs)
    | tProj p t => tProj p (eta_expand t)
    | tFix def i => tFix (map (map_def eta_expand eta_expand) def) i
    | tCoFix def i => tCoFix (map (map_def eta_expand eta_expand) def) i
    (* NOTE: we know that constructors and constants are not applied at this point,
       since applications are captured by the previous cases *)
    | tConstruct ind c u =>
        match eta_constructor ind c u [] with 
        | Some res => res
        | None => tVar ("Error: lookup of an inductive failed for "
                       ++ string_of_kername ind.(inductive_mind))
        end
    | t => t
    end.

End Eta.

Fixpoint map_constants_global_env (f : constant_body -> constant_body) (Σ : global_env) : global_env :=
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' => (kn, ConstantDecl (f cb)) :: map_constants_global_env f Σ'
  | gd :: Σ' => gd :: map_constants_global_env f Σ'
  end.

Definition eta_global_env (Σ : global_env) :=
  let f cb :=
     {| cst_type := eta_expand Σ cb.(cst_type) ; 
        cst_universes := cb.(cst_universes) ;
        cst_body := match cb.(cst_body) with
                    | Some b => Some (eta_expand Σ b)
                    | None => None
                    end |} in
  map_constants_global_env f Σ.

(* MetaCoq Quote Recursively Definition p := (@pair).
MetaCoq Unquote Definition q := (eta_expand p.1 p.2).
Print q.
*)

Definition isConstruct t :=
    match t with tConstruct _ _ _ => true | _ => false end.

Section expanded.

Variable Σ : global_env.

Local Unset Elimination Schemes.

Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : expanded (tEvar ev args)
| expanded_tSort (s : Universe.t) : expanded (tSort s)
| expanded_tCast (t : term) (kind : cast_kind) (v : term) : expanded t -> expanded v -> expanded (tCast t kind v)
| expanded_tProd (na : aname) (ty : term) (body : term) : expanded ty -> expanded body -> expanded (tProd na ty body)
| expanded_tLambda (na : aname) (ty : term) (body : term) : expanded ty -> expanded body -> expanded (tLambda na ty body)
| expanded_tLetIn (na : aname) (def : term) (def_ty : term) (body : term) : expanded def -> expanded def_ty -> expanded body -> expanded (tLetIn na def def_ty body)
| expanded_tApp (f : term) (args : list term) : ~ isConstruct f -> expanded f -> Forall expanded args -> expanded (tApp f args)
| expanded_tConst (c : kername) (u : Instance.t) : expanded (tConst c u)
| expanded_tInd (ind : inductive) (u : Instance.t) : expanded (tInd ind u)
| expanded_tConstruct (ind : inductive) (idx : nat) (u : Instance.t) mind idecl cdecl :
    declared_constructor Σ (ind, idx) mind idecl cdecl ->
    ind_npars mind + context_assumptions (cstr_args cdecl) = 0 ->
    expanded (tConstruct ind idx u)
| expanded_tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term)) : expanded discr -> Forall (fun br => expanded br.(bbody)) branches -> expanded (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) : 
  Forall (fun d => expanded d.(dtype) /\ expanded d.(dbody)) mfix ->
  expanded (tFix mfix idx)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : 
  Forall (fun d => expanded d.(dtype) /\ expanded d.(dbody)) mfix ->
  expanded (tCoFix mfix idx)
| expanded_tInt (i : Int63.int) : expanded (tInt i)
| expanded_tFloat (f : PrimFloat.float) : expanded (tFloat f)
| expanded_tConstruct_app ind c u mind idecl cdecl args :
    declared_constructor Σ (ind, c) mind idecl cdecl ->
    #|args| >= (ind_npars mind + context_assumptions (cstr_args cdecl)) ->
    expanded (tApp (tConstruct ind c u) args).

End expanded.

Lemma expanded_ind :
forall (Σ : global_env) (P : term -> Prop),
(forall n : nat, P (tRel n)) ->
(forall id : ident, P (tVar id)) ->
(forall (ev : nat) (args : list term), P (tEvar ev args)) ->
(forall s : Universe.t, P (tSort s)) ->
(forall (t : term) (kind : cast_kind) (v : term),
 expanded Σ t -> P t -> expanded Σ v -> P v -> P (tCast t kind v)) ->
(forall (na : aname) (ty body : term),
 expanded Σ ty -> P ty -> expanded Σ body -> P body -> P (tProd na ty body)) ->
(forall (na : aname) (ty body : term),
 expanded Σ ty -> P ty -> expanded Σ body -> P body -> P (tLambda na ty body)) ->
(forall (na : aname) (def def_ty body : term),
 expanded Σ def ->
 P def ->
 expanded Σ def_ty ->
 P def_ty -> expanded Σ body -> P body -> P (tLetIn na def def_ty body)) ->
(forall (f7 : term) (args : list term),
 ~ isConstruct f7 ->
 expanded Σ f7 -> P f7 -> Forall (expanded Σ) args -> Forall P args -> P (tApp f7 args)) ->
(forall (c : kername) (u : Instance.t), P (tConst c u)) ->
(forall (ind : inductive) (u : Instance.t), P (tInd ind u)) ->
(forall (ind : inductive) (idx : nat) (u : Instance.t)
   (mind : mutual_inductive_body) (idecl : one_inductive_body)
   (cdecl : constructor_body),
 declared_constructor Σ (ind, idx) mind idecl cdecl ->
 ind_npars mind + context_assumptions (cstr_args cdecl) = 0 ->
 P (tConstruct ind idx u)) ->
(forall (ci : case_info) (type_info : predicate term) 
   (discr : term) (branches : list (branch term)),
 expanded Σ discr ->
 P discr ->
 Forall (fun br : branch term => expanded Σ (bbody br)) branches ->
 Forall (fun br : branch term => P (bbody br)) branches ->
 P (tCase ci type_info discr branches)) ->
(forall (proj : projection) (t : term),
 expanded Σ t -> P t -> P (tProj proj t)) ->
(forall (mfix : mfixpoint term) (idx : nat), 
  Forall (fun d => expanded Σ d.(dtype) /\ expanded Σ d.(dbody)) mfix -> 
  Forall (fun d => P d.(dtype) /\ P d.(dbody)) mfix -> 
  P (tFix mfix idx)) ->
(forall (mfix : mfixpoint term) (idx : nat), 
  Forall (fun d => expanded Σ d.(dtype) /\ expanded Σ d.(dbody)) mfix -> 
  Forall (fun d => P d.(dtype) /\ P d.(dbody)) mfix -> 
  P (tCoFix mfix idx)) ->
(forall i : PrimInt63.int, P (tInt i)) ->
(forall f16 : PrimFloat.float, P (tFloat f16)) ->
(forall (ind : inductive) (c : nat) (u : Instance.t)
   (mind : mutual_inductive_body) (idecl : one_inductive_body)
   (cdecl : constructor_body) (args : list term),
 declared_constructor Σ (ind, c) mind idecl cdecl ->
 #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
 P (tApp (tConstruct ind c u) args)) -> forall t : term, expanded Σ t -> P t.
Proof.
  intros. revert t H18.
  fix f 2.
  intros t Hexp. destruct Hexp; eauto.
  - assert (Forall P args) by (induction H19; econstructor; eauto).
    destruct f0; eauto.
  - eapply H11; eauto. induction H18; econstructor; eauto.
  - eapply H13; eauto. induction H18 as [ | ? ? []]; econstructor; cbn in *; eauto; split.
  - eapply H14; eauto. induction H18 as [ | ? ? []]; econstructor; cbn in *; eauto; split.
Qed.
