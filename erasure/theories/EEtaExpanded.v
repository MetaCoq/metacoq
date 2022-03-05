(* Distributed under the terms of the MIT license. *)
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
    ELiftSubst ESpineView ECSubst.

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

Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite mkApps_app /= IHl.
  now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
Qed.

Section AllInP.
  Context {A : Type}.

  Equations forallb_InP (l : list A) (H : forall x : A, In x l -> bool) : bool :=
  | nil, _ := true ;
  | (cons x xs), H := (H x _) && (forallb_InP xs (fun x inx => H x _)).
End AllInP.

Lemma forallb_InP_spec {A} (f : A -> bool) (l : list A) :
  forallb_InP l (fun x _ => f x) = List.forallb f l.
Proof.
  remember (fun x _ => f x) as g.
  funelim (forallb_InP l g) => //; simpl. f_equal.
  now rewrite (H0 f).
Qed.

Section MapInP.
  Context {A B : Type}.

  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

Lemma In_size {A B} {x : A} {l : list A} (proj : A -> B) (size : B -> nat) : 
  In x l -> size (proj x) < S (list_size (size ∘ proj) l).
Proof.
  induction l; cbn => //.
  intros [->|hin]. lia. specialize (IHl hin); lia.
Qed.

Equations discr_construct (t : term) : Prop :=
discr_construct (tConstruct ind n) := False ;
discr_construct _ := True.

Inductive construct_view : term -> Type :=
| view_construct : forall ind n, construct_view (tConstruct ind n)
| view_other : forall t, discr_construct t -> construct_view t.

Equations construct_viewc t : construct_view t :=
construct_viewc (tConstruct ind n) := view_construct ind n ;
construct_viewc t := view_other t I.
Lemma In_All {A} {P : A -> Type} l : 
    (∀ x : A, In x l -> P x) -> All P l.
Proof.
  induction l; cbn; constructor; auto.
Qed.
  
Ltac toAll := 
    repeat match goal with 
      | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
    end.

Import ECSubst.

Section isEtaExp.
  Context (Σ : global_declarations).
  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- ETyping.lookup_env Σ kn;; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).
  
  Definition lookup_inductive_pars kn : option nat := 
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_npars).
  
  Definition lookup_constructor_pars_args kn c : option (nat * nat) := 
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl.(ind_npars), cdecl.2).
    
  Definition isEtaExp_app ind c k :=
    match lookup_constructor_pars_args ind c with
    | Some (npars, nargs) => leb (npars + nargs) k
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
    | tFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
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
  
  Lemma isEtaExp_app_mon ind c i i' : i <= i' -> isEtaExp_app ind c i -> isEtaExp_app ind c i'.
  Proof.
    intros le.
    unfold isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|]=> //.
    do 2 elim: Nat.leb_spec => //. lia.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.


  Lemma isEtaExp_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    isEtaExp (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app ind i #|v| && forallb isEtaExp v
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn. destruct (construct_viewc f); cbn; simp isEtaExp => //.
  Qed.

  Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
  Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.
  
  Lemma isEtaExp_mkApps f v : ~~ isApp f ->
    isEtaExp (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app ind i #|v| && forallb isEtaExp v
      | view_other t discr => isEtaExp f && forallb isEtaExp v
    end.
  Proof.
    intros napp.
    destruct v using rev_case; simp_eta.
    - destruct construct_viewc; rewrite andb_true_r //.
    - rewrite isEtaExp_mkApps_nonnil //. now destruct v; cbn; congruence.
  Qed.

  Lemma isEtaExp_Constructor ind i v :
    isEtaExp (mkApps (EAst.tConstruct ind i) v) = isEtaExp_app ind i #|v| && forallb isEtaExp v.
  Proof.
    rewrite isEtaExp_mkApps //.
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
    - rewrite isEtaExp_mkApps //.
      destruct construct_viewc. cbn. len.
      rtoProp; repeat solve_all. cbn in et. simp isEtaExp in et.
      eapply isEtaExp_app_mon; tea; lia.
      eapply All_app_inv; eauto. rewrite et forallb_app /=.
      rtoProp; repeat solve_all.
    - rewrite isEtaExp_mkApps in et => //.
      destruct construct_viewc.
      rewrite -mkApps_app. rewrite isEtaExp_Constructor.
      cbn. cbn. rtoProp; solve_all.
      eapply isEtaExp_app_mon; tea. cbn. len. lia. now depelim H1.
      depelim H1. solve_all. eapply All_app_inv => //.
      eapply All_app_inv => //. eauto.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma etaExp_csubst a k b : 
    isEtaExp a -> isEtaExp b -> isEtaExp (ECSubst.csubst a k b).
  Proof.
    funelim (isEtaExp b); try simp_eta; eauto;
      try toAll; repeat solve_all.
    - intros. simp isEtaExp ; cbn. destruct Nat.compare => //. simp_eta in H.
    - move/andP: H2 => [] etab etab'.
      apply/andP. split; eauto.
    - rtoProp. intuition eauto.
      solve_all.
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
    isEtaExp (ETyping.iota_red pars args br).
  Proof.
    intros etaargs etabr.
    unfold ETyping.iota_red.
    rewrite isEtaExp_substl // forallb_rev forallb_skipn //.
  Qed.
  
  Lemma isEtaExp_fix_subst mfix : 
    forallb (isEtaExp ∘ dbody) mfix ->
    forallb isEtaExp (ETyping.fix_subst mfix).
  Proof.
    unfold ETyping.fix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.

  Lemma isEtaExp_cofix_subst mfix : 
    forallb (isEtaExp ∘ dbody) mfix ->
    forallb isEtaExp (ETyping.cofix_subst mfix).
  Proof.
    unfold ETyping.cofix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; simp_eta; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.
  
  Lemma isEtaExp_cunfold_fix mfix idx n f : 
    forallb (isEtaExp ∘ dbody) mfix ->
    Ee.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof.
    intros heta.
    unfold Ee.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_fix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.
  
  Lemma isEtaExp_cunfold_cofix mfix idx n f : 
    forallb (isEtaExp ∘ dbody) mfix ->
    Ee.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp f.
  Proof.
    intros heta.
    unfold Ee.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_cofix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.

End isEtaExp.
Global Hint Rewrite @forallb_InP_spec : isEtaExp.

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

  Lemma lookup_inductive_pars_spec Σ kn : lookup_inductive_pars Σ kn = EEtaExpanded.lookup_inductive_pars Σ kn.
  Proof.
    rewrite /lookup_inductive_pars /EEtaExpanded.lookup_inductive_pars.
    rewrite /lookup_inductive /EEtaExpanded.lookup_inductive.
    rewrite /lookup_minductive /EEtaExpanded.lookup_minductive.
    rewrite (EnvMap.lookup_spec Σ.(global_decls)).
    eapply wf. eapply repr. reflexivity.
  Qed.

  Program Definition make (g : global_declarations) (Hg : EnvMap.fresh_globals g): t :=
    {| global_decls := g;
       map := EnvMap.of_global_env g |}.

End GlobalContextMap.
Coercion GlobalContextMap.global_decls : GlobalContextMap.t >-> global_declarations.

(* 
Section AllInP.
  Context {A : Type}.

  Equations forallb_InP (l : list A) (H : forall x : A, In x l -> bool) : bool :=
  | nil, _ := true ;
  | (cons x xs), H := (H x _) && (forallb_InP xs (fun x inx => H x _)).
End AllInP.

Lemma forallb_InP_spec {A} (f : A -> bool) (l : list A) :
  forallb_InP l (fun x _ => f x) = List.forallb f l.
Proof.
  remember (fun x _ => f x) as g.
  funelim (forallb_InP l g) => //; simpl. f_equal.
  now rewrite (H0 f).
Qed.

Section MapInP.
  Context {A B : Type}.

  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

Lemma In_size {A B} {x : A} {l : list A} (proj : A -> B) (size : B -> nat) : 
  In x l -> size (proj x) < S (list_size (size ∘ proj) l).
Proof.
  induction l; cbn => //.
  intros [->|hin]. lia. specialize (IHl hin); lia.
Qed.

Equations discr_construct (t : term) : Prop :=
discr_construct (tConstruct ind n) := False ;
discr_construct _ := True.

Inductive construct_view : term -> Type :=
| view_construct : forall ind n, construct_view (tConstruct ind n)
| view_other : forall t, discr_construct t -> construct_view t.

Equations construct_viewc t : construct_view t :=
construct_viewc (tConstruct ind n) := view_construct ind n ;
construct_viewc t := view_other t I.

Section isEtaExp.
  Context (Σ : global_context).
  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- ETyping.lookup_env Σ kn;; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).
  
  Definition lookup_inductive_pars kn : option nat := 
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_npars).
  
  Definition lookup_constructor_pars_args kn c : option (nat * nat) := 
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl.(ind_npars), cdecl.2).
    
  Definition isEtaExp_app ind c k :=
    match lookup_constructor_pars_args ind c with
    | Some (npars, nargs) => leb (npars + nargs) k
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
    | tFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
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
  
  Lemma isEtaExp_app_mon ind c i i' : i <= i' -> isEtaExp_app ind c i -> isEtaExp_app ind c i'.
  Proof.
    intros le.
    unfold isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|]=> //.
    do 2 elim: Nat.leb_spec => //. lia.
  Qed.

End isEtaExp.
Global Hint Rewrite @forallb_InP_spec : isEtaExp.

Opaque isEtaExp.

Lemma In_All {A} {P : A -> Type} l : 
(∀ x : A, In x l -> P x) -> All P l.
Proof.
induction l; cbn; constructor; auto.
Qed.

Ltac toAll := 
repeat match goal with 
  | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
end.

Section something.

Context (Σ : global_context).

Hint Rewrite @forallb_InP_spec : isEtaExp.
Transparent isEtaExp_unfold_clause_1.

Lemma isEtaExp_mkApps_nonnil f v :
  ~~ isApp f -> v <> [] ->
  isEtaExp Σ (mkApps f v) = match construct_viewc f with 
    | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v
    | view_other t discr => isEtaExp Σ f && forallb (isEtaExp Σ) v
  end.
Proof.
  rewrite isEtaExp_equation_1.
  intros napp hv.
  destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
  cbn. destruct (construct_viewc f); cbn; simp isEtaExp => //.
Qed.

Lemma isEtaExp_mkApps f v : ~~ isApp f ->
  isEtaExp Σ (mkApps f v) = match construct_viewc f with 
    | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v
    | view_other t discr => isEtaExp Σ f && forallb (isEtaExp Σ) v
  end.
Proof.
  intros napp.
  destruct v using rev_case; cbn.
  - destruct construct_viewc; rewrite andb_true_r //.
  - rewrite isEtaExp_mkApps_nonnil //. now destruct v; cbn; congruence.
Qed.

Lemma isEtaExp_Constructor ind i v :
  isEtaExp Σ (mkApps (tConstruct ind i) v) = isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v.
Proof.
  rewrite isEtaExp_mkApps //.
Qed.

Lemma isEtaExp_mkApps_intro t l : isEtaExp Σ t -> All (isEtaExp Σ) l -> isEtaExp Σ (mkApps t l).
Proof.
  revert t; induction l using rev_ind; auto.
  intros t et a; eapply All_app in a as [].
  depelim a0. clear a0.
  destruct (decompose_app t) eqn:da.
  rewrite (decompose_app_inv da) in et *.
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l0. cbn.
  - rewrite isEtaExp_mkApps //.
    destruct construct_viewc. cbn. len.
    rtoProp; repeat solve_all. cbn in et. simp isEtaExp in et.
    eapply isEtaExp_app_mon; tea; lia.
    eapply All_app_inv; eauto. rewrite et forallb_app /=.
    rtoProp; repeat solve_all.
  - rewrite isEtaExp_mkApps in et => //.
    destruct construct_viewc.
    rewrite -mkApps_app. rewrite isEtaExp_Constructor.
    cbn. cbn. rtoProp; solve_all.
    eapply isEtaExp_app_mon; tea. cbn. len. lia. now depelim H1.
    depelim H1. solve_all. eapply All_app_inv => //.
    eapply All_app_inv => //. eauto.
    rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
    destruct (construct_viewc t0) => //.
    move/andP: et => [] -> /=. rtoProp; solve_all.
    rewrite forallb_app. rtoProp; repeat solve_all.
    eapply All_app_inv; eauto.
Qed.

Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite mkApps_app /= IHl.
  now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
Qed.

Lemma etaExp_csubst a k b : 
  isEtaExp Σ a -> isEtaExp Σ b -> isEtaExp Σ (ECSubst.csubst a k b).
Proof.
  funelim (isEtaExp Σ b); cbn; simp isEtaExp; rewrite -?isEtaExp_equation_1; eauto;
    toAll; repeat solve_all.
  - intros. destruct Nat.compare => //.
  - move/andP: H2 => [] etab etab'.
    apply/andP. split; eauto.
  - rtoProp. intuition eauto.
    solve_all.
  - move/andP: H1 => [] etaexp h.
    rewrite csubst_mkApps /=.
    rewrite isEtaExp_Constructor. solve_all.
    rewrite map_length. rtoProp; solve_all. solve_all.
  - rewrite csubst_mkApps /=.
    move/andP: H2 => [] eu ev.
    specialize (H _ k H1 eu).
    eapply isEtaExp_mkApps_intro => //. solve_all.
Qed.

End something.

Definition isEtaExp_constant_decl Σ cb := 
  option_default (isEtaExp Σ) cb.(cst_body) true.

Definition isEtaExp_decl Σ d :=
  match d with
  | ConstantDecl cb => isEtaExp_constant_decl Σ cb
  | InductiveDecl idecl => true
  end.

Fixpoint isEtaExp_env (Σ : EAst.global_declarations) := 
  match Σ with 
  | [] => true
  | decl :: Σ => isEtaExp_decl Σ decl.2 && isEtaExp_env Σ
  end.

(* Lemma strip_extends Σ Σ' : extends Σ Σ' ->
  strip Σ t = strip Σ' t. *)

Lemma isEtaExp_tApp Σ f u : isEtaExp Σ (mkApps f u) -> 
  let (hd, args) := decompose_app (mkApps f u) in
  match construct_viewc hd with
  | view_construct kn c => isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args
  | view_other u discr => isEtaExp Σ hd && forallb (isEtaExp Σ) args
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
  rewrite isEtaExp_mkApps //.
Qed. *)

From MetaCoq.Template Require Import config utils BasicAst Universes.
From MetaCoq.Erasure Require Import EAst ETyping EAstUtils.

Section expanded.

Variable Σ : global_declarations.

Local Unset Elimination Schemes.

Inductive expanded : term -> Prop :=
| expanded_tRel (n : nat) : expanded (tRel n)
| expanded_tVar (id : ident) : expanded (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall expanded args -> expanded (tEvar ev args)
| expanded_tLambda (na : name) (body : term) : expanded body -> expanded (tLambda na body)
| expanded_tLetIn (na : name) (def : term)(body : term) : expanded def -> expanded body -> expanded (tLetIn na def body)
| expanded_mkApps (f : term) (args : list term) : ~ isConstruct f -> expanded f -> Forall expanded args -> expanded (mkApps f args)
| expanded_tConst (c : kername) : expanded (tConst c)
| expanded_tCase (ind : inductive) (pars : nat) (discr : term) (branches : list (list name × term)) : 
    expanded discr -> Forall (fun br => expanded br.2) branches -> expanded (tCase (ind, pars) discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded t -> expanded (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) :  Forall (fun d => expanded d.(dbody)) mfix -> expanded (tFix mfix idx)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : Forall (fun d => expanded d.(dbody)) mfix -> expanded (tCoFix mfix idx)
| expanded_tConstruct_app ind idx mind idecl cname c args :
    declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
    #|args| >= ind_npars mind + c -> 
    Forall expanded args ->
    expanded (mkApps (tConstruct ind idx) args)
| expanded_tBox : expanded tBox.

End expanded.

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
 expanded Σ f4 -> P f4 -> Forall (expanded Σ) args -> Forall P args -> P (mkApps f4 args)) ->
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
 Forall (fun d : def term => expanded Σ (dbody d)) mfix ->  Forall (fun d : def term => P (dbody d)) mfix  -> P (tFix mfix idx)) ->
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
  - eapply H4; eauto. induction H13; econstructor; cbn in *; eauto.
  - eapply H6; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H8; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H9; eauto. induction H12; econstructor; cbn in *; eauto.
  - eapply H10; eauto. clear - H14 f. induction H14; econstructor; cbn in *; eauto.
Qed.

Local Hint Constructors expanded : core .
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

Lemma isEtaExp_app_expanded Σ ind idx n :
   isEtaExp_app Σ ind idx n = true <->
   exists mind idecl cname c,
   declared_constructor Σ (ind, idx) mind idecl (cname, c) /\ n ≥ ind_npars mind + c.
Proof.
  unfold isEtaExp_app, lookup_constructor_pars_args, lookup_inductive, lookup_minductive.
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
    eapply In_All in H. solve_all.
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
  - rewrite isEtaExp_Constructor. eapply andb_true_iff.
    split. 2: eapply forallb_Forall.
    2: solve_all. eapply expanded_isEtaExp_app_; eauto.
Qed.