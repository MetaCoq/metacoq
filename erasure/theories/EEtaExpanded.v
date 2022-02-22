From MetaCoq.Template Require Import config utils BasicAst Universes.
From MetaCoq.Erasure Require Import EAst ETyping EAstUtils.

Section expanded.

Variable Σ : global_declarations.

Local Unset Elimination Schemes.

Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : expanded (tEvar ev args)
| expanded_tLambda (na : name) (body : term) : expanded body -> expanded (tLambda na body)
| expanded_tLetIn (na : name) (def : term)(body : term) : expanded def -> expanded body -> expanded (tLetIn na def body)
| expanded_mkApps (f : term) (args : list term) : ~ isConstruct f -> expanded f -> Forall expanded args -> expanded (mkApps f args)
| expanded_tConst (c : kername) : expanded (tConst c)
| expanded_tCase (ind : inductive) (pars : nat) (discr : term) (branches : list (list name × term)) : 
    expanded discr -> Forall (fun br => expanded br.2) branches -> expanded (tCase (ind, pars) discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) :  Forall (fun d => expanded d.(dbody)) mfix -> expanded (tFix mfix idx)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : Forall (fun d => expanded d.(dbody)) mfix -> expanded (tCoFix mfix idx)
| expanded_tPrim (prim : PCUICPrimitive.prim_val term) : expanded (tPrim prim)
| expanded_tConstruct_app ind idx mind idecl cname c args :
    declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
    #|args| >= ind_npars mind + c -> 
    expanded (mkApps (tConstruct ind idx) args)
| expanded_tBox : expanded tBox.

End expanded.

Lemma expanded_ind :
forall (Σ : global_declarations) (P : term -> Prop),
(forall n : nat, P (tRel n)) ->
(forall id : ident, P (tVar id)) ->
(forall (ev : nat) (args : list term), P (tEvar ev args)) ->
(forall (na : name) (body : term),
 expanded Σ body -> P body -> P (tLambda na body)) ->
(forall (na : name) (def body : term),
 expanded Σ def ->
 P def -> expanded Σ body -> P body -> P (tLetIn na def body)) ->
(forall (f4 : term) (args : list term),
 ~ isConstruct f4 ->
 expanded Σ f4 -> P f4 -> Forall (expanded Σ) args -> P (mkApps f4 args)) ->
(forall c : kername, P (tConst c)) ->
(forall (ind : inductive) (pars : nat) (discr : term)
   (branches : list (list name × term)),
 expanded Σ discr ->
 P discr ->
 Forall (fun br : list name × term => expanded Σ br.2) branches ->
 P (tCase (ind, pars) discr branches)) ->
(forall (proj : projection) (t : term),
 expanded Σ t -> P t -> P (tProj proj t)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix  -> P (tFix mfix idx)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix ->
 P (tCoFix mfix idx)) ->
(forall prim, P (tPrim prim)) ->
(forall (ind : inductive) (idx : nat) (mind : mutual_inductive_body)
   (idecl : one_inductive_body) (cname : ident) (c : nat) 
   (args : list term),
 declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
 #|args| >= ind_npars mind + c -> P (mkApps (tConstruct ind idx) args)) ->
(P tBox) ->
forall t : term, expanded Σ t -> P t.
Proof. 
  intros. revert t H13.
  fix f 2.
  intros t Hexp. destruct Hexp; eauto.
  - eapply H8; eauto. induction H13; econstructor; cbn in *; eauto.
  - eapply H9; eauto. induction H13; econstructor; cbn in *; eauto. 
Qed.