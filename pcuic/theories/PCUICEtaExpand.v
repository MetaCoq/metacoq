From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.

Definition isConstruct t :=
   match t with tConstruct _ _ _ => true | _ => false end.

 Definition isFix t :=
  match t with tFix _ _ => true | _ => false end.

Section expanded.

Variable Σ : global_env.

Local Unset Elimination Schemes.

Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall expanded args -> expanded (tEvar ev args)
| expanded_tSort (s : Universe.t) : expanded (tSort s)
| expanded_tProd (na : aname) (ty : term) (body : term) : (* expanded ty -> expanded body -> *) expanded (tProd na ty body)
| expanded_tLambda (na : aname) (ty : term) (body : term) : (* expanded ty ->  *)expanded body -> expanded (tLambda na ty body)
| expanded_tLetIn (na : aname) (def : term) (def_ty : term) (body : term) : expanded def -> (* expanded def_ty ->  *)expanded body -> expanded (tLetIn na def def_ty body)
| expanded_mkApps (f : term) (args : list term) : ~ isConstruct f -> expanded f -> Forall expanded args -> expanded (mkApps f args)
| expanded_tConst (c : kername) (u : Instance.t) : expanded (tConst c u)
| expanded_tInd (ind : inductive) (u : Instance.t) : expanded (tInd ind u)
| expanded_tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term)) : expanded discr -> Forall (fun br => expanded br.(bbody)) branches -> expanded (tCase ci type_info discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d : 
  Forall (fun d => expanded d.(dtype) /\ expanded d.(dbody)) mfix ->
  Forall expanded args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  expanded (mkApps (tFix mfix idx) args)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) :   Forall (fun d => expanded d.(dtype) /\ expanded d.(dbody)) mfix -> expanded (tCoFix mfix idx)
| expanded_tConstruct_app ind c u mind idecl cdecl args :
    declared_constructor Σ (ind, c) mind idecl cdecl ->
    #|args| >= (ind_npars mind + context_assumptions (cstr_args cdecl)) ->
    Forall expanded args ->
    expanded (mkApps (tConstruct ind c u) args).

End expanded.

Lemma expanded_ind :
forall (Σ : global_env) (P : term -> Prop),
(forall n : nat, P (tRel n)) ->
(forall id : ident, P (tVar id)) ->
(forall (ev : nat) (args : list term), Forall (expanded Σ) args -> Forall P args -> P (tEvar ev args)) ->
(forall s : Universe.t, P (tSort s)) ->
(forall (na : aname) (ty body : term),
(*  expanded Σ ty -> P ty -> expanded Σ body -> P body -> *) P (tProd na ty body)) ->
(forall (na : aname) (ty body : term),
(*  expanded Σ ty -> P ty -> *) expanded Σ body -> P body -> P (tLambda na ty body)) ->
(forall (na : aname) (def def_ty body : term),
 expanded Σ def ->
 P def ->
 (* expanded Σ def_ty -> 
 P def_ty -> *) expanded Σ body -> P body -> P (tLetIn na def def_ty body)) ->
(forall (f6 : term) (args : list term),
 ~ isConstruct f6 ->
 expanded Σ f6 -> P f6 -> Forall (expanded Σ) args -> Forall P args -> P (mkApps f6 args)) ->
(forall (c : kername) (u : Instance.t), P (tConst c u)) ->
(forall (ind : inductive) (u : Instance.t), P (tInd ind u)) ->
(forall (ci : case_info) (type_info : predicate term) 
   (discr : term) (branches : list (branch term)),
 expanded Σ discr ->
 P discr ->
 Forall (fun br : branch term => expanded Σ (bbody br)) branches ->
 Forall (fun br : branch term => P (bbody br)) branches ->
 P (tCase ci type_info discr branches)) ->
 (forall (proj : projection) (t : term),
 expanded Σ t -> P t -> P (tProj proj t)) -> 
 (forall (mfix : mfixpoint term) (idx : nat) d args, 
 Forall (fun d => expanded Σ d.(dtype) /\ expanded Σ d.(dbody)) mfix -> 
 Forall (fun d => P d.(dtype) /\ P d.(dbody)) mfix -> 
 Forall (expanded Σ) args ->
 Forall P args ->
 args <> [] ->
 nth_error mfix idx = Some d ->
 #|args| > d.(rarg) ->
 expanded Σ (mkApps (tFix mfix idx) args) ->
 P (mkApps (tFix mfix idx) args)) ->
 
(forall (mfix : mfixpoint term) (idx : nat), 
 Forall (fun d => expanded Σ d.(dtype) /\ expanded Σ d.(dbody)) mfix -> 
 Forall (fun d => P d.(dtype) /\ P d.(dbody)) mfix -> 
 P (tCoFix mfix idx)) ->
(forall (ind : inductive) (c : nat) (u : Instance.t)
   (mind : mutual_inductive_body) (idecl : one_inductive_body)
   (cdecl : constructor_body) (args : list term),
 declared_constructor Σ (ind, c) mind idecl cdecl ->
 #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl) ->
 Forall (expanded Σ) args ->
 Forall P args ->
 P (mkApps (tConstruct ind c u) args)) ->
forall t : term, expanded Σ t -> P t.
Proof.
  intros. revert t H14.
  fix f 2.
  intros t Hexp. destruct Hexp; eauto.
  - eapply H1; eauto. induction H14; econstructor; eauto.
  - assert (Forall P args) by (induction H15; econstructor; eauto).
    destruct f0; eauto.
  - eapply H9; eauto. induction H14; econstructor; eauto.
  - eapply H11; eauto. 3: eapply expanded_tFix; eauto. clear -H14 f. induction H14; econstructor; firstorder. clear - H15 f. induction H15; econstructor; firstorder.
  - eapply H12; eauto. induction H14 as [ | ? ? []]; econstructor; cbn in *; eauto; split.
  - eapply H13; eauto. clear - f H16. induction H16; econstructor; cbn in *; eauto; split.
Qed.