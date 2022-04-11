(* Distributed under the terms of the MIT license. *)

(* Eta expanded constructors only, see EEtaExpandedFix for the more involved definition where fixpoints are also eta-expanded. *)

From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.

From MetaCoq.SafeChecker Require Import PCUICWfEnv.
     
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EArities Extract Prelim
    EGlobalEnv EWellformed ELiftSubst ESpineView ECSubst EWcbvEvalInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Coq Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors Ee.eval : core.

Set Warnings "-notation-overridden".
Import E.
Set Warnings "+notation-overridden".

Import MCList (map_InP, map_InP_elim, map_InP_spec).

Equations discr_construct (t : term) : Prop :=
discr_construct (tConstruct ind n) := False ;
discr_construct _ := True.

Inductive construct_view : term -> Type :=
| view_construct : forall ind n, construct_view (tConstruct ind n)
| view_other : forall t, discr_construct t -> construct_view t.

Equations construct_viewc t : construct_view t :=
construct_viewc (tConstruct ind n) := view_construct ind n ;
construct_viewc t := view_other t I.

Ltac toAll := 
    repeat match goal with 
      | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
    end.

Import ECSubst.

Class EtaExpFlag := mkEtaExpFlags { strict_eta : bool }.
Definition strong_eta_flag := {| strict_eta := true |}.
Definition weak_eta_flag := {| strict_eta := false |}.

Section isEtaExp.
  Context {etafl : EtaExpFlag}.
  Context (Σ : global_declarations).
  
  Definition isEtaExp_app ind c k :=
    match EGlobalEnv.lookup_constructor_pars_args Σ ind c with
    | Some (npars, nargs) =>
      (if strict_eta then eqb else leb) (npars + nargs) k
    | None => false
    end.
    
  Import TermSpineView.

  Equations? isEtaExp (e : EAst.term) : bool
    by wf e (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel i => true
    | tEvar ev args => forallb_InP args (fun x H => isEtaExp x)
    | tLambda na M => isEtaExp M
    | tApp u v napp nnil with construct_viewc u := 
      { | view_construct ind i => isEtaExp_app ind i (List.length v) && forallb_InP v (fun x H => isEtaExp x)
        | view_other _ _ => isEtaExp u && forallb_InP v (fun x H => isEtaExp x) }
    | tLetIn na b b' => isEtaExp b && isEtaExp b'
    | tCase ind c brs => isEtaExp c && forallb_InP brs (fun x H => isEtaExp x.2)
    | tProj p c => isEtaExp c
    | tFix mfix idx => forallb_InP mfix (fun x H => isLambda x.(dbody) && isEtaExp x.(dbody))
    | tCoFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
    | tBox => true
    | tVar _ => true
    | tConst _ => true
    | tConstruct ind i => isEtaExp_app ind i 0 }.
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    all:try lia.
    - now apply (In_size id size). 
    - rewrite size_mkApps.
      change (fun x => size (id x)) with size in H. cbn.
      now apply (In_size id size).
    - now eapply size_mkApps_f.
    - change (fun x => size (id x)) with size in H.
      eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in H. 
      pose proof (size_mkApps_l napp nnil). lia.
    - eapply (In_size snd size) in H. cbn in H; lia.
  Qed.

End isEtaExp.

Global Hint Rewrite @forallb_InP_spec : isEtaExp.
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

Section isEtaExp.
  Context {efl : EtaExpFlag}.
  Context (Σ : global_context).
  Notation isEtaExp := (isEtaExp Σ).

  Lemma isEtaExp_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    isEtaExp (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb isEtaExp v
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn. destruct (construct_viewc f); cbn; simp isEtaExp => //.
  Qed.

  Lemma isEtaExp_mkApps_napp f v : ~~ isApp f ->
    isEtaExp (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb isEtaExp v
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof.
    intros napp.
    destruct v using rev_case; simp_eta.
    - destruct construct_viewc; rewrite andb_true_r //.
    - rewrite isEtaExp_mkApps_nonnil //.
  Qed.

  Lemma isEtaExp_Constructor ind i v :
    isEtaExp (mkApps (EAst.tConstruct ind i) v) = isEtaExp_app Σ ind i #|v| && forallb isEtaExp v.
  Proof.
    rewrite isEtaExp_mkApps_napp //.
  Qed.


  Lemma isEtaExp_mkApps f u : isEtaExp (mkApps f u) -> 
    let (hd, args) := decompose_app (mkApps f u) in
    match construct_viewc hd with
    | view_construct kn c => isEtaExp_app Σ kn c #|args| && forallb isEtaExp args
    | view_other u discr => isEtaExp hd && forallb isEtaExp args
    end.
  Proof.
    destruct decompose_app eqn:da.
    rewrite (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l. cbn -[isEtaExp].
    intros eq; rewrite eq.
    destruct (construct_viewc t) => //. simp isEtaExp in eq; now rewrite eq.
    assert (t0 :: l <> []) by congruence.
    revert da H0. generalize (t0 :: l). clear t0 l; intros l.
    intros da nnil.
    rewrite isEtaExp_mkApps_napp //.
  Qed.

  Arguments EEtaExpanded.isEtaExp : simpl never.

  Lemma isEtaExp_mkApps_intro_notConstruct t l : ~~ isConstruct (head t) ->
     isEtaExp t -> All isEtaExp l -> isEtaExp (mkApps t l).
  Proof.
    revert t; induction l using rev_ind; auto.
    intros t isc et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et isc *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. simp_eta.
    - rewrite isEtaExp_mkApps_napp //.
      destruct construct_viewc eqn:vc => //. cbn.
      rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
    - rewrite isEtaExp_mkApps_napp in et => //.
      destruct construct_viewc.
      rewrite head_mkApps in isc => //.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps_napp //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma isEtaExp_tApp {f u} : isEtaExp (EAst.tApp f u) -> 
    let (hd, args) := decompose_app (EAst.tApp f u) in
    match construct_viewc hd with
    | view_construct kn c =>
      args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
      isEtaExp_app Σ kn c #|args| && forallb isEtaExp args
    | view_other _ discr => 
      [&& isEtaExp hd, forallb isEtaExp args, isEtaExp f & isEtaExp u]
    end.
  Proof.
    move/(isEtaExp_mkApps f [u]).
    cbn -[decompose_app]. destruct decompose_app eqn:da.
    destruct construct_viewc eqn:cv => //.
    intros ->.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
    rewrite mkApps_app in H. noconf H.
    rewrite remove_last_app last_last. intuition auto.
    destruct l; cbn in *; congruence.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. destruct t => //.
    rewrite mkApps_app in H. noconf H.
    move=> /andP[] etat. rewrite forallb_app => /andP[] etal /=.
    rewrite andb_true_r => etaa. rewrite etaa andb_true_r.
    rewrite etat etal. cbn. rewrite andb_true_r.
    eapply isEtaExp_mkApps_intro_notConstruct; auto; solve_all.
    destruct t => //.
  Qed.

End isEtaExp.

Section WeakEtaExp.
  Context (efl := weak_eta_flag).
  Existing Instance efl.
  Context (Σ : global_context).
  Notation isEtaExp := (isEtaExp Σ).

  Lemma isEtaExp_app_mon ind c i i' : i <= i' -> isEtaExp_app Σ ind c i -> isEtaExp_app Σ ind c i'.
  Proof.
    intros le.
    unfold isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|]=> //.
    cbn.
    do 2 elim: Nat.leb_spec => //. lia.
  Qed.

  Lemma isEtaExp_mkApps_intro t l : isEtaExp t -> All isEtaExp l -> isEtaExp (mkApps t l).
  Proof.
    revert t; induction l using rev_ind; auto.
    intros t et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. simp_eta.
    - rewrite isEtaExp_mkApps_napp //.
      destruct construct_viewc. cbn. len.
      rtoProp; repeat solve_all. cbn in et. simp isEtaExp in et.
      eapply isEtaExp_app_mon; tea; lia.
      eapply All_app_inv; eauto. rewrite et forallb_app /=.
      rtoProp; repeat solve_all.
    - rewrite isEtaExp_mkApps_napp in et => //.
      destruct construct_viewc.
      rewrite -mkApps_app. rewrite isEtaExp_Constructor.
      cbn. cbn. rtoProp; solve_all.
      eapply isEtaExp_app_mon; tea. cbn. len. lia. now depelim H1.
      depelim H1. solve_all. eapply All_app_inv => //.
      eapply All_app_inv => //. eauto.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps_napp //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma etaExp_csubst a k b : 
    isEtaExp a -> isEtaExp b -> isEtaExp (ECSubst.csubst a k b).
  Proof.
    funelim (isEtaExp b); cbn -[isEtaExp]; try simp_eta; eauto;
      try toAll; repeat solve_all.
    - intros. simp isEtaExp ; cbn. destruct Nat.compare => //. simp_eta in H.
    - move/andP: H2 => [] etab etab'.
      apply/andP. split; eauto.
    - rtoProp. intuition eauto.
      solve_all.
    - move/andP: b => [] etaexp h.
      apply/andP; split.
      now eapply isLambda_csubst.
      eapply a0 => //.
    - move/andP: H1 => [] etaexp h.
      rewrite csubst_mkApps /=.
      rewrite isEtaExp_Constructor. solve_all.
      rewrite map_length. rtoProp; solve_all. solve_all.
    - rewrite csubst_mkApps /=.
      move/andP: H2 => [] eu ev.
      specialize (H _ k H1 eu).
      eapply isEtaExp_mkApps_intro => //. solve_all.
  Qed.
  
  Lemma isEtaExp_substl s t : 
    forallb isEtaExp s -> isEtaExp t ->
    isEtaExp (substl s t).
  Proof.
    induction s in t |- *; simpl; auto. rtoProp; intuition eauto using etaExp_csubst.
  Qed.

  Lemma isEtaExp_iota_red pars args br :
    forallb isEtaExp args ->
    isEtaExp br.2 ->
    isEtaExp (EGlobalEnv.iota_red pars args br).
  Proof.
    intros etaargs etabr.
    unfold EGlobalEnv.iota_red.
    rewrite isEtaExp_substl // forallb_rev forallb_skipn //.
  Qed.
  
  Lemma isEtaExp_fix_subst mfix : 
    forallb (fun d => isLambda (dbody d) && isEtaExp (dbody d)) mfix ->
    forallb isEtaExp (EGlobalEnv.fix_subst mfix).
  Proof.
    unfold EGlobalEnv.fix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.

  Lemma isEtaExp_cofix_subst mfix : 
    forallb (isEtaExp ∘ dbody) mfix ->
    forallb isEtaExp (EGlobalEnv.cofix_subst mfix).
  Proof.
    unfold EGlobalEnv.cofix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.
  
  Lemma isEtaExp_cunfold_fix mfix idx n f : 
    forallb (fun d => isLambda (dbody d) && isEtaExp (dbody d)) mfix ->
    EGlobalEnv.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof.
    intros heta.
    unfold EGlobalEnv.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_fix_subst.
    eapply forallb_nth_error in heta; tea.
    erewrite heq in heta. now move/andP: heta.
  Qed.
  
  Lemma isEtaExp_cunfold_cofix mfix idx n f : 
    forallb (isEtaExp ∘ dbody) mfix ->
    EGlobalEnv.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof.
    intros heta.
    unfold EGlobalEnv.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_cofix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.

End WeakEtaExp.

Definition isEtaExp_constant_decl Σ cb := 
  option_default (isEtaExp Σ) cb.(cst_body) true.

Definition isEtaExp_decl Σ d :=
  match d with
  | ConstantDecl cb => isEtaExp_constant_decl Σ cb
  | InductiveDecl idecl => true
  end.

Fixpoint isEtaExp_env (Σ : global_declarations) := 
  match Σ with 
  | [] => true
  | decl :: Σ => isEtaExp_decl Σ decl.2 && isEtaExp_env Σ
  end.

Lemma isEtaExp_lookup_ext {Σ} {kn d}: 
  isEtaExp_env Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends Σ' Σ × isEtaExp_decl Σ' d.
Proof.
  induction Σ; cbn.
  - move=> _; rewrite /declared_constant /lookup_env /= //.
  - move=> /andP[] etaa etaΣ.
    destruct a as [kn' d']; cbn in *.
    rewrite /declared_constant /=.
    case:eqb_specT => //.
    * intros e; subst kn'. move=> [=]. intros ->.
      exists Σ. split => //. now exists [(kn, d)].
    * intros ne. move=> Hl. destruct (IHΣ etaΣ Hl) as [Σ' [ext eta]].
      exists Σ'; split => //.
      destruct ext as [Σ'' ->].
      now exists ((kn', d')::Σ'').
Qed.

Lemma isEtaExp_app_extends {efl : EEnvFlags} Σ Σ' ind k n :
  extends Σ Σ' ->
  wf_glob Σ' -> 
  isEtaExp_app Σ ind k n ->
  isEtaExp_app Σ' ind k n.
Proof.
  rewrite /isEtaExp_app.
  rewrite /lookup_constructor_pars_args /lookup_constructor /lookup_inductive /lookup_minductive.
  move=> ext wf.
  destruct (lookup_env Σ _) eqn:hl => //.
  rewrite (extends_lookup wf ext hl) /= //.
Qed.

From MetaCoq.Erasure Require Import ELiftSubst.

Lemma isEtaExp_extends {efl : EEnvFlags} Σ Σ' t : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp Σ t ->
  isEtaExp Σ' t.
Proof.
  intros ext wf.
  funelim (isEtaExp Σ t); simp_eta => //; rtoProp; intuition eauto; rtoProp; intuition auto.
  - eapply In_All in H; solve_all.
  - eapply isEtaExp_app_extends; tea.
  - eapply In_All in H0. solve_all.
  - eapply In_All in H; solve_all.
    move/andP: b => [] -> /=. eauto.
  - eapply In_All in H; solve_all.
  - eapply In_All in H; solve_all.
    rewrite isEtaExp_Constructor //. rtoProp; intuition auto.
    eapply isEtaExp_app_extends; tea.
    solve_all.
  - eapply In_All in H0. apply isEtaExp_mkApps_intro; eauto. solve_all.
Qed.

Lemma isEtaExp_extends_decl {efl : EEnvFlags} {Σ Σ' t} : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp_decl Σ t ->
  isEtaExp_decl Σ' t.
Proof.
  intros ext wf; destruct t; cbn => //.
  rewrite /isEtaExp_constant_decl; destruct (cst_body c) => /= //.
  now eapply isEtaExp_extends.
Qed.

Lemma isEtaExp_lookup {efl : EEnvFlags} {Σ kn d}: 
  isEtaExp_env Σ -> wf_glob Σ ->
  lookup_env Σ kn = Some d ->
  isEtaExp_decl Σ d.
Proof.
  move=> etaΣ wfΣ.
  move/(isEtaExp_lookup_ext etaΣ) => [Σ' []] ext hd.
  now eapply isEtaExp_extends_decl.
Qed.

From MetaCoq.Template Require Import config utils BasicAst Universes.
From MetaCoq.Erasure Require Import EAst EGlobalEnv EAstUtils.

Section expanded.

Variable Σ : global_declarations.

Local Unset Elimination Schemes.

Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall expanded args -> expanded (tEvar ev args)
| expanded_tLambda (na : name) (body : term) : expanded body -> expanded (tLambda na body)
| expanded_tLetIn (na : name) (def : term)(body : term) : expanded def -> expanded body -> expanded (tLetIn na def body)
| expanded_mkApps (f : term) (args : list term) : ~ isConstruct f -> args <> [] -> expanded f -> Forall expanded args -> expanded (mkApps f args)
| expanded_tConst (c : kername) : expanded (tConst c)
| expanded_tCase (ind : inductive) (pars : nat) (discr : term) (branches : list (list name × term)) : 
    expanded discr -> Forall (fun br => expanded br.2) branches -> expanded (tCase (ind, pars) discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) :  
  Forall (fun d => isLambda d.(dbody) /\ expanded d.(dbody)) mfix -> expanded (tFix mfix idx)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : Forall (fun d => expanded d.(dbody)) mfix -> expanded (tCoFix mfix idx)
| expanded_tConstruct_app ind idx mind idecl cname c args :
    declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
    #|args| >= ind_npars mind + c -> 
    Forall expanded args ->
    expanded (mkApps (tConstruct ind idx) args)
| expanded_tBox : expanded tBox.

End expanded.
Derive Signature for expanded.

Lemma expanded_ind :
forall (Σ : global_declarations) (P : term -> Prop),
(forall n : nat, P (tRel n)) ->
(forall id : ident, P (tVar id)) ->
(forall (ev : nat) (args : list term), Forall (expanded Σ) args -> Forall P args -> P (tEvar ev args)) ->
(forall (na : name) (body : term),
 expanded Σ body -> P body -> P (tLambda na body)) ->
(forall (na : name) (def body : term),
 expanded Σ def ->
 P def -> expanded Σ body -> P body -> P (tLetIn na def body)) ->
(forall (f4 : term) (args : list term),
 ~ isConstruct f4 ->
 expanded Σ f4 -> P f4 -> args <> [] -> Forall (expanded Σ) args -> Forall P args -> P (mkApps f4 args)) ->
(forall c : kername, P (tConst c)) ->
(forall (ind : inductive) (pars : nat) (discr : term)
   (branches : list (list name × term)),
 expanded Σ discr ->
 P discr ->
 Forall (fun br : list name × term => expanded Σ br.2) branches ->
 Forall (fun br : list name × term => P br.2) branches ->
 P (tCase (ind, pars) discr branches)) ->
(forall (proj : projection) (t : term),
 expanded Σ t -> P t -> P (tProj proj t)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => isLambda (dbody d) /\ expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix  -> P (tFix mfix idx)) ->
(forall (mfix : mfixpoint term) (idx : nat),
 Forall (fun d : def term => expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix ->
 P (tCoFix mfix idx)) ->
(forall (ind : inductive) (idx : nat) (mind : mutual_inductive_body)
   (idecl : one_inductive_body) (cname : ident) (c : nat) 
   (args : list term),
 declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
 #|args| >= ind_npars mind + c -> Forall (expanded Σ) args -> Forall P args -> P (mkApps (tConstruct ind idx) args)) ->
(P tBox) ->
forall t : term, expanded Σ t -> P t.
Proof. 
  intros. revert t H12.
  fix f 2.
  intros t Hexp. destruct Hexp; eauto.
  - eapply H1; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H4; eauto. clear H13. induction H14; econstructor; cbn in *; eauto.
  - eapply H6; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H8; eauto. induction H12; econstructor; cbn in *; intuition eauto.
  - eapply H9; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H10; eauto. clear - H14 f. induction H14; econstructor; cbn in *; eauto.
Qed.

Local Hint Constructors expanded : core.

Definition expanded_constant_decl Σ (cb : constant_body) : Prop :=
  on_Some_or_None (expanded Σ) cb.(cst_body).
    
Definition expanded_decl Σ d :=
  match d with
  | ConstantDecl cb => expanded_constant_decl Σ cb
  | InductiveDecl idecl => True
  end.
    
Inductive expanded_global_declarations : forall (Σ : global_declarations), Prop :=
| expanded_global_nil : expanded_global_declarations []
| expanded_global_cons decl Σ : expanded_global_declarations Σ -> 
  expanded_decl Σ decl.2 -> expanded_global_declarations (decl :: Σ).

Definition expanded_global_env := expanded_global_declarations.

Definition expanded_eprogram_cstrs (p : eprogram) := 
  EEtaExpanded.isEtaExp_env p.1 && EEtaExpanded.isEtaExp p.1 p.2.

Definition expanded_eprogram_env_cstrs (p : eprogram_env) := 
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpanded.isEtaExp_env decls && EEtaExpanded.isEtaExp decls p.2.


Lemma isEtaExp_app_expanded Σ ind idx n :
   isEtaExp_app Σ ind idx n = true <->
   exists mind idecl cname c,
   declared_constructor Σ (ind, idx) mind idecl (cname, c) /\ n ≥ ind_npars mind + c.
Proof.
  unfold isEtaExp_app, lookup_constructor_pars_args, lookup_constructor, lookup_inductive, lookup_minductive.
  split.
  - intros H.
    destruct lookup_env as [[| mind] | ] eqn:E; cbn in H; try congruence.
    destruct nth_error as [ idecl | ] eqn:E2; cbn in H; try congruence.
    destruct (nth_error (E.ind_ctors idecl) idx) as [ [cname ?] | ] eqn:E3; cbn in H; try congruence.
    repeat esplit.
    red. all: eauto. eapply leb_iff in H. lia.
  - intros (? & ? & ? & ? & [[]] & Hle).
    rewrite H. cbn. rewrite H0. cbn. rewrite H1. cbn.
    eapply leb_iff. eauto.
Qed.

Lemma expanded_isEtaExp_app_ Σ ind idx n  mind idecl cname c :
   declared_constructor Σ (ind, idx) mind idecl (cname, c) -> n ≥ ind_npars mind + c ->
   isEtaExp_app Σ ind idx n = true.
Proof.
  intros. eapply isEtaExp_app_expanded. eauto 8.
Qed.

Lemma isEtaExp_expanded Σ t :
  isEtaExp Σ t -> expanded Σ t.
Proof.
  funelim (isEtaExp Σ t); intros; solve_all; eauto.
  - rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. eapply In_All in H.
    econstructor. solve_all.
  - eapply andb_true_iff in H1 as []; eauto.
  - eapply isEtaExp_app_expanded in H as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app with (args := []); eauto.
  - eapply andb_true_iff in H1 as []. destruct ind. econstructor; eauto.
    rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2. 
    eapply In_All in H0. solve_all.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. 
    eapply In_All in H. rtoProp; intuition auto; solve_all.
    all: move/andP: b. 2:{ now intros []. }
    intuition auto.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. 
    eapply In_All in H. solve_all.
  - eapply andb_true_iff in H0 as []. eapply In_All in H.
    rewrite forallb_InP_spec in H1. eapply forallb_Forall in H1.
    eapply isEtaExp_app_expanded in H0 as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app; eauto. solve_all.
  - eapply andb_true_iff in H1 as []. rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2.
    econstructor.
    + destruct u; inv Heq; eauto.
    + eauto.
    + eauto.
    + eapply In_All in H0. solve_all.
Qed.

Lemma expanded_isEtaExp Σ t :
  expanded Σ t -> isEtaExp Σ t.
Proof.
  induction 1; simp_eta; eauto.
  all: try now (
    (try (eapply andb_true_iff; split; eauto));
    (try eapply forallb_Forall); 
    eauto).
  - eapply isEtaExp_mkApps_intro; eauto. solve_all.
  - solve_all. now rewrite b H.
  - rewrite isEtaExp_Constructor. eapply andb_true_iff.
    split. 2: eapply forallb_Forall.
    2: solve_all. eapply expanded_isEtaExp_app_; eauto.
Qed.

Lemma expanded_global_env_isEtaExp_env {Σ} : expanded_global_env Σ -> isEtaExp_env Σ.
Proof.
  intros e; induction e; cbn => //.
  rewrite IHe andb_true_r.
  red in H; red. destruct decl as [kn []] => /= //.
  cbn in H. red in H. unfold isEtaExp_constant_decl.
  destruct (cst_body c); cbn in * => //.
  now eapply expanded_isEtaExp.
Qed.

Lemma isEtaExp_env_expanded_global_env {Σ} : isEtaExp_env Σ -> expanded_global_env Σ.
Proof.
  induction Σ; cbn => /= //.
  - constructor.
  - move/andP=> [] etad etae; constructor; eauto. now apply IHΣ.
    move: etad. destruct a.2; cbn in * => //. unfold isEtaExp_constant_decl, expanded_constant_decl.
    destruct (cst_body c) => /= //. apply isEtaExp_expanded.
Qed.

Lemma solve_discr_args {t f args} : ~~ isApp t -> t = mkApps f args -> args = [] /\ f = t.
Proof.
  intros napp ->.
  induction args using rev_ind; cbn in *; auto.
  rewrite mkApps_app in napp. now cbn in napp.
Qed.

Ltac solve_discr_args := 
  match goal with [ H : ?t = mkApps ?f ?args |- _ ] =>
    destruct (@solve_discr_args t f args eq_refl H) as [-> ->] ||
    destruct (@solve_discr_args t f args eq_refl H) as [-> ?]
  end.

Lemma expanded_mkApps_expanded {Σ f args} : 
  expanded Σ f -> All (expanded Σ) args ->
  expanded Σ (mkApps f args).
Proof.
  intros.
  destruct (isConstruct f) eqn:eqc.
  destruct f => //.
  - depelim H; try solve_discr_args => //.
    noconf H3.
    eapply expanded_tConstruct_app; tea. cbn in H0. lia. solve_all.
  - destruct args using rev_ind; cbn => //.
    eapply expanded_mkApps => //. now rewrite eqc. solve_all.
Qed.

From MetaCoq.Erasure Require Import EEtaExpandedFix.

Local Ltac simp_eta ::= simp isEtaExp; rewrite -?isEtaExp_equation_1 -?EEtaExpanded.isEtaExp_equation_1.

Lemma isEtaExpFix_isEtaExp Σ Γ t : EEtaExpandedFix.isEtaExp Σ Γ t -> EEtaExpanded.isEtaExp Σ t.
Proof.
  funelim (isEtaExp Σ Γ t); try solve [simp_eta => //].
  - simp_eta.
    intros Ha. eapply In_All in H. solve_all.
  - simp_eta. rtoProp; intuition auto.
  - simp_eta. rtoProp; intuition auto.
    eapply In_All in H0; solve_all.
  - eapply In_All in H. simp_eta; rtoProp; intuition auto. solve_all.
  - eapply In_All in H. simp_eta; rtoProp; intuition auto.
    rewrite EEtaExpanded.isEtaExp_Constructor. apply/andP; split. exact H1.
    solve_all.
  - eapply In_All in H, H0. simp_eta.
    move => /andP[] /andP[] etafix etamfix etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro. simp_eta.
    clear -H etamfix. solve_all. rtoProp; intuition eauto.
    solve_all.
  - eapply In_All in H. simp_eta.
    move=> /andP[] etarel etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro. simp_eta. solve_all.
  - eapply In_All in H0. simp_eta.
    move=> /andP[] etau etav.
    eapply EEtaExpanded.isEtaExp_mkApps_intro; auto. solve_all.
Qed.

Lemma isEtaExpFix_env_isEtaExp_env Σ : isEtaExp_env Σ -> EEtaExpanded.isEtaExp_env Σ.
Proof.
  induction Σ; cbn; auto.
  move/andP => [] etaa etaΣ.
  rewrite IHΣ // andb_true_r.
  move: etaa. rewrite /isEtaExp_decl /EEtaExpanded.isEtaExp_decl.
  destruct a.2 => //.
  rewrite /isEtaExp_constant_decl /EEtaExpanded.isEtaExp_constant_decl.
  destruct (E.cst_body c) => // /=.
  eapply isEtaExpFix_isEtaExp.
Qed.

