(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.
     

From MetaCoq.Template Require Import config utils BasicAst Universes.
From MetaCoq.Erasure Require Import EAst ETyping EAstUtils.


From MetaCoq.Erasure Require Import EWcbvEval.

Lemma eval_trans' {wfl : WcbvFlags} {Σ e e' e''} :
  eval Σ e e' -> eval Σ e' e'' -> e' = e''.
Proof.
  intros ev ev'.
  eapply eval_to_value in ev.
  eapply value_final in ev.
  eapply (eval_deterministic ev ev').
Qed.

Lemma eval_trans {wfl : WcbvFlags} {Σ e e' e''} :
  eval Σ e e' -> eval Σ e' e'' -> eval Σ e e''.
Proof.
  intros ev ev'.
  enough (e' = e'') by now subst.
  eapply eval_trans'; eauto.
Qed.

Arguments eval : clear implicits.

Lemma eval_app_cong_tApp Σ t v args res :
  eval target_wcbv_flags Σ t v ->  
  eval target_wcbv_flags Σ (tApp v args) res ->
  eval target_wcbv_flags Σ (tApp t args) res.
Proof.
  intros. depind H0.
  - econstructor; eauto. eapply eval_trans; eauto.
  - econstructor; eauto. eapply eval_trans; eauto.
  - eapply eval_fix'; eauto. eapply eval_trans; eauto.
  - eapply eval_app_cong; eauto. eapply eval_trans; eauto.
  - cbn in i. easy.
Qed.

Definition isRel t :=
    match t with tRel _ => true | _ => false end.

Section expanded.

Variable Σ : global_declarations.

Local Unset Elimination Schemes.
 
Inductive expanded (Γ : list nat): term -> Prop :=
| expanded_tRel (n : nat) : nth n Γ 0 = 0 -> expanded Γ (tRel n)
| expanded_tRel_app (n : nat) args : nth n Γ 0 <= #|args| -> Forall (expanded Γ) args -> expanded Γ (mkApps (tRel n) args)
| expanded_tLambda (na : name) (body : term) : (* expanded Γ ty -> *) expanded (0 :: Γ) body -> expanded Γ (tLambda na body)
| expanded_tLetIn (na : name) (def : term) (body : term) : expanded Γ def (* -> expanded Γ def_ty *) -> expanded (0 :: Γ) body -> expanded Γ (tLetIn na def body)
| expanded_mkApps (f : term) (args : list term) : negb (isConstruct f || isFix f || isRel f) -> expanded Γ f -> Forall (expanded Γ) args -> expanded Γ (mkApps f args)
| expanded_tConst (c : kername) : expanded Γ (tConst c)
| expanded_tCase (ind : inductive) (pars : nat) (discr : term) (branches : list (list name × term)) :  
    expanded Γ discr -> 
    Forall (fun br => expanded (repeat 0 #|br.1| ++ Γ) br.2) branches -> 
    expanded Γ (tCase (ind, pars) discr branches)
| expanded_tProj (proj : projection) (t : term) : expanded Γ t -> expanded Γ (tProj proj t)
| expanded_tFix (mfix : mfixpoint term) (idx : nat) args d : 
  Forall (fun d => 
           let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in
          expanded (ctx ++ Γ) d.(dbody)) mfix ->
  Forall (expanded Γ) args ->
  args <> [] ->
  nth_error mfix idx = Some d ->
  #|args| > d.(rarg) ->
  expanded Γ (mkApps (tFix mfix idx) args)
| expanded_tCoFix (mfix : mfixpoint term) (idx : nat) : 
  Forall (fun d => expanded (repeat 0 #|mfix| ++ Γ) d.(dbody)) mfix ->
  expanded Γ (tCoFix mfix idx)
| expanded_tConstruct_app ind idx mind idecl cname c args :
    declared_constructor Σ (ind, idx) mind idecl (cname, c) ->
    #|args| >= ind_npars mind + c -> 
    Forall (expanded Γ) args ->
    expanded Γ (mkApps (tConstruct ind idx) args)
| expanded_tBox : expanded Γ tBox.

End expanded.

Lemma expanded_ind :
  ∀ (Σ : global_declarations) (P : list nat → term → Prop),
    (∀ (Γ : list nat) (n : nat), nth n Γ 0 = 0 → P Γ (tRel n))
    → (∀ (Γ : list nat) (n : nat) (args : list term),
	        nth n Γ 0 ≤ #|args|
        → Forall (expanded Σ Γ) args
        → Forall (P Γ) args 
        → P Γ (mkApps (tRel n) args))
    → (∀ (Γ : list nat) (na : name) (body : term),
          expanded Σ (0 :: Γ) body → P (0 :: Γ) body → P Γ (tLambda na body))
    → (∀ (Γ : list nat) (na : name) (def body : term),
          expanded Σ Γ def
        → P Γ def
        → expanded Σ (0 :: Γ) body
        → P (0 :: Γ) body → P Γ (tLetIn na def body))
    → (∀ (Γ : list nat) (f3 : term) (args : list term),
          negb (isConstruct f3 || isFix f3 || isRel f3)
        → expanded Σ Γ f3
        → P Γ f3 → Forall (expanded Σ Γ) args → Forall (P Γ) args → P Γ (mkApps f3 args))
    → (∀ (Γ : list nat) (c : kername), P Γ (tConst c))
    → (∀ (Γ : list nat) (ind : inductive) 
         (pars : nat) (discr : term) (branches : 
                                     list 
                                       (list name × term)),
          expanded Σ Γ discr
        → P Γ discr
        → Forall
            (λ br : list name × term,
                expanded Σ (repeat 0 #|br.1| ++ Γ) br.2) branches
        → Forall
            (λ br : list name × term,
                P (repeat 0 #|br.1| ++ Γ) br.2) branches
        → P Γ (tCase (ind, pars) discr branches))
    → (∀ (Γ : list nat) (proj : projection) (t : term),
          expanded Σ Γ t → P Γ t → P Γ (tProj proj t))
    → (∀ (Γ : list nat) (mfix : mfixpoint term) 
         (idx : nat) (args : list term) 
         (d : def term),
          Forall
            (λ d0 : def term,
                let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in
                expanded Σ (ctx ++ Γ) (dbody d0)) mfix
          → Forall
            (λ d0 : def term,
               let ctx := rev_map (fun  d => 1 + d.(rarg)) mfix in
                P (ctx ++ Γ) (dbody d0)) mfix
          → Forall (expanded Σ Γ) args
          → Forall (P Γ) args
          → args ≠ []
          → nth_error mfix idx = Some d
          → #|args| > rarg d
                    → P Γ (mkApps (tFix mfix idx) args))
    → (∀ (Γ : list nat) (mfix : mfixpoint term) (idx : nat),
          Forall
            (λ d : def term,
                expanded Σ (repeat 0 #|mfix| ++ Γ) (dbody d)) mfix 
        → Forall
            (λ d : def term,
                P (repeat 0 #|mfix| ++ Γ) (dbody d)) mfix 
        → P Γ (tCoFix mfix idx))
    → (∀ (Γ : list nat) (ind : inductive) 
         (idx : nat) (mind : mutual_inductive_body) 
         (idecl : one_inductive_body) 
         (cname : ident) (c : nat) 
         (args : list term),
          declared_constructor Σ (ind, idx) mind idecl (cname, c)
        → #|args| ≥ ind_npars mind + c
        → Forall (expanded Σ Γ) args
        → Forall (P Γ) args
        → P Γ (mkApps (tConstruct ind idx) args))
    → (∀ Γ : list nat, P Γ tBox)
    → ∀ (Γ : list nat) (t : term), expanded Σ Γ t → P Γ t.
Proof.
  intros Σ P HRel HRel_app HLamdba HLetIn HmkApps HConst HCase HProj HFix HCoFix HConstruct HBox.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  - eapply HRel_app; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HmkApps; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HCase; eauto. induction H; econstructor; eauto.
  - assert (Forall (P Γ) args). { clear - H0 f. induction H0; econstructor; eauto. }
    eapply HFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HCoFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct; eauto.
    clear - H1 f. induction H1; econstructor; eauto.
Qed.



Local Hint Constructors expanded : core.

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

Equations discr_expanded_head (t : term) : Prop :=
  discr_expanded_head (tConstruct ind n) := False ;
  discr_expanded_head (tFix mfix idx) := False ;
  discr_expanded_head (tRel n) := False ;
  discr_expanded_head _ := True.

Inductive expanded_head_view : term -> Type :=
| expanded_head_construct : forall ind n, expanded_head_view (tConstruct ind n)
| expanded_head_fix : forall mfix idx, expanded_head_view (tFix mfix idx)
| expanded_head_rel : forall n, expanded_head_view (tRel n)
| expanded_head_other : forall t, discr_expanded_head t -> expanded_head_view t.

Equations expanded_head_viewc t : expanded_head_view t :=
  expanded_head_viewc (tConstruct ind n) := expanded_head_construct ind n ;
  expanded_head_viewc (tFix mfix idx) := expanded_head_fix mfix idx ;
  expanded_head_viewc (tRel n) := expanded_head_rel n ;
  expanded_head_viewc t := expanded_head_other t I.

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

  Definition isEtaExp_fixapp (mfix : mfixpoint term) idx k :=
    match nth_error mfix idx with
    | Some d => Nat.ltb d.(rarg) k
    | None => false
    end.    
    
  Import TermSpineView.

  Equations? isEtaExp (Γ : list nat) (e : EAst.term) : bool
    by wf e (fun x y : EAst.term => size x < size y) :=
    isEtaExp Γ e with TermSpineView.view e := {
    | tRel i => Nat.eqb (nth i Γ 0) 0
    | tEvar ev args => forallb_InP args (fun x H => isEtaExp Γ x)
    | tLambda na M => isEtaExp (0 :: Γ) M
    | tApp u v napp nnil with expanded_head_viewc u := 
      { | expanded_head_construct ind i => isEtaExp_app ind i (List.length v) && forallb_InP v (fun x H => isEtaExp Γ x)
        | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx (List.length v) && 
                                        forallb_InP mfix (fun x H => isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) && forallb_InP v (fun x H => isEtaExp Γ x)
        | expanded_head_rel n => (nth n Γ 0 <=? List.length v) && forallb_InP v (fun x H => isEtaExp Γ x) 
        | expanded_head_other _ _ => isEtaExp Γ u && forallb_InP v (fun x H => isEtaExp Γ x) }
    | tLetIn na b b' => isEtaExp Γ b && isEtaExp (0 :: Γ) b'
    | tCase ind c brs => isEtaExp Γ c && forallb_InP brs (fun x H => isEtaExp (repeat 0 #|x.1| ++ Γ) x.2)
    | tProj p c => isEtaExp Γ c
    | tFix mfix idx => false
    | tCoFix mfix idx => forallb_InP mfix (fun x H => isEtaExp (repeat 0 #|mfix| ++ Γ) x.(dbody))
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
      now apply (In_size id size).
    - rewrite size_mkApps.
      apply (In_size id (fun d => size d.(dbody))) in H. unfold id in H. 
      change (fun x => size x) with size in H. cbn. lia.
    - rewrite size_mkApps.
      apply (In_size id size) in H. unfold id in H. 
      change (fun x => size x) with size in H. cbn. lia.
    - rewrite size_mkApps.
      apply (In_size id size) in H. unfold id in H. 
      change (fun x => size x) with size in H. cbn. lia.
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

  Lemma isEtaExp_mkApps_nonnil Γ f v :
    ~~ isApp f -> v <> [] ->
    isEtaExp Γ (mkApps f v) = match expanded_head_viewc f with 
      | expanded_head_construct ind i => isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v
      | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|v| && forallb (fun x => isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => (nth n Γ 0 <=? List.length v) && forallb (fun x => isEtaExp Γ x) v
      | expanded_head_other t discr => isEtaExp Γ f && forallb (isEtaExp Γ) v
    end.
  Proof.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn. destruct (expanded_head_viewc f); cbn; simp isEtaExp => //.
  Qed.

  Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
  Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

  Definition is_cons {A} (l : list A) := match l with [] => false | _ => true end.
  
  Lemma isEtaExp_mkApps Γ f v : ~~ isApp f -> 
    isEtaExp Γ (mkApps f v) = match expanded_head_viewc f with 
      | expanded_head_construct ind i => isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v
      | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|v| && forallb (fun x => isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => (nth n Γ 0 <=? List.length v) && forallb (fun x => isEtaExp Γ x) v
      | expanded_head_other t discr => isEtaExp Γ f && forallb (isEtaExp Γ) v
    end.
  Proof.
    intros napp.
    destruct v using rev_case; simp_eta.
    - destruct expanded_head_viewc; rewrite ? andb_true_r //. cbn. unfold isEtaExp_fixapp. now destruct (nth_error); cbn.
      cbn. destruct (Nat.eqb_spec (nth n Γ 0) 0), (Nat.leb_spec (nth n Γ 0) 0); try reflexivity; lia.
    - rewrite isEtaExp_mkApps_nonnil //. destruct v; cbn; try congruence.      
  Qed.

  Lemma isEtaExp_Constructor Γ ind i v :
    isEtaExp Γ (mkApps (EAst.tConstruct ind i) v) = isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v.
  Proof.
    now rewrite isEtaExp_mkApps.
  Qed.
 
  Lemma isEtaExp_mkApps_intro Γ t l : isEtaExp Γ t -> All (isEtaExp Γ) l -> isEtaExp Γ (mkApps t l).
  Proof.
    revert t Γ; induction l using rev_ind; auto.
    intros t Γ et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. simp_eta.
    - rewrite isEtaExp_mkApps //.
      destruct expanded_head_viewc.
      + cbn. len.
        rtoProp; repeat solve_all. cbn in et. simp isEtaExp in et.
        eapply isEtaExp_app_mon; tea; lia. 
        eapply All_app_inv; eauto.
      + cbn in *; congruence.
      + simp_eta in et. eapply Nat.eqb_eq in et. rewrite et.
        rtoProp. split. cbn. eauto.
        solve_all. eapply All_app_inv; solve_all.
      + rewrite et forallb_app /=. rtoProp; repeat solve_all. 
    - rewrite isEtaExp_mkApps in et => //.
      destruct expanded_head_viewc.
      + rewrite -mkApps_app. rewrite isEtaExp_Constructor.
        cbn. cbn. rtoProp; solve_all.
        eapply isEtaExp_app_mon; tea. cbn. len. lia. now depelim H1.
        depelim H1. solve_all. eapply All_app_inv => //.
        eapply All_app_inv => //. eauto.
      + rewrite -mkApps_app. rewrite isEtaExp_mkApps //. simp expanded_head_viewc.
        rewrite /isEtaExp_fixapp in et |- *.
        rtoProp; repeat split.
        * destruct nth_error; try congruence. eapply Nat.ltb_lt. eapply Nat.ltb_lt in H0.
          cbn in H0. len. lia.
        * solve_all.
        * solve_all. eapply All_app_inv; solve_all. eapply All_app_inv; solve_all.
      + rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
        cbn [expanded_head_viewc]. rtoProp. split.
        cbn. eapply Nat.leb_le in H0. eapply Nat.leb_le. revert H0. len. lia.
        solve_all. eapply All_app_inv. 2: eapply All_app_inv. all: solve_all.
      + rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
        destruct (expanded_head_viewc t0) => //.
        move/andP: et => [] -> /=. rtoProp; solve_all.
        rewrite forallb_app. rtoProp; repeat solve_all.
        eapply All_app_inv; eauto.
  Qed.

  Hint Rewrite repeat_length : len.

  Lemma expanded_lift Γ' Γ'' Γ t :
    isEtaExp (Γ' ++ Γ)%list t ->
    isEtaExp (Γ' ++ Γ'' ++ Γ)%list (lift #|Γ''| #|Γ'| t).
  Proof.
  Admitted.

  Lemma etaExp_csubst' a k b n Γ Δ : 
    #|Γ| = k ->
    closed a -> isEtaExp [] a -> isEtaExp (Γ ++ [n] ++ Δ) b -> isEtaExp (Γ ++ Δ) (ECSubst.csubst a k b).
  Proof.
    intros Hk Hcl. 
    remember (Γ ++ [n] ++ Δ)%list as Γ_.
    funelim (isEtaExp Γ_ b); try simp_eta; eauto; try fold csubst;
      try toAll; repeat solve_all; subst.
    - intros. simp isEtaExp ; cbn. destruct (Nat.compare_spec #|Γ0| i) => //; simp_eta.
      + setoid_rewrite <- lift_closed.
        rewrite <- (app_nil_r (Γ0 ++ Δ)).
        eapply expanded_lift with(Γ' := []); eassumption. 
        eassumption.
      + rewrite app_nth2. lia.
        rewrite app_nth2 in H0. lia.
        eapply Nat.eqb_eq in H0. eapply Nat.eqb_eq.
        rewrite <- H0 at 2. destruct i. lia.
        cbn [Nat.pred].
        rewrite app_nth2. cbn. lia. f_equal. cbn. lia.
      + rewrite !app_nth1 in H0 |- *; try lia.
        eapply Nat.eqb_eq in H0. eapply Nat.eqb_eq. lia.
    - eapply H with (Γ := 0 :: Γ0); cbn; eauto.
    - move/andP: H2 => [] etab etab'. simp_eta.
      apply/andP. split; eauto.
      eapply H0 with (Γ := 0 :: Γ0); cbn; eauto.
    - rtoProp. intuition eauto.
      solve_all. rewrite app_assoc. eapply a0; cbn; eauto. now len. cbn.
      now rewrite app_assoc.
    - rewrite app_assoc. eapply a0; len; eauto. now rewrite app_assoc.
    - fold csubst. move/andP: H1 => [] etaexp h.
      rewrite csubst_mkApps /=.
      rewrite isEtaExp_Constructor. solve_all.
      rewrite map_length. rtoProp; solve_all. solve_all.
    - rewrite csubst_mkApps /=.
      move/andP : H2 => [] /andP [] eu ef ev.
      rewrite isEtaExp_mkApps //.
      simp expanded_head_viewc.
      rtoProp; repeat split.
      + rewrite /isEtaExp_fixapp in eu |- *. rewrite nth_error_map. destruct nth_error; try congruence.
        cbn. now len.
      + solve_all.
        rewrite app_assoc.  eapply a0; len; eauto. cbn. f_equal.
        rewrite app_assoc. do 2 f_equal.
        rewrite !rev_map_spec. f_equal. rewrite map_map. now eapply map_ext.      
      + solve_all.
    - rewrite csubst_mkApps /=. rtoProp. destruct (Nat.compare_spec #|Γ0| n) => //; simp_eta.
      + eapply isEtaExp_mkApps_intro => //. 2: solve_all.
        setoid_rewrite <- lift_closed.
        rewrite <- (app_nil_r (Γ0 ++ Δ)).
        eapply expanded_lift with(Γ' := []); eassumption. 
        eassumption.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. split. 2: solve_all.
        eapply Nat.leb_le in H1. eapply Nat.leb_le. rewrite app_nth2 in H1 |- *; try lia.
        len. rewrite <- H1. rewrite !app_nth2; cbn; try lia.
        eapply Nat.eq_le_incl. f_equal. lia.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. split. 2: solve_all. rewrite app_nth1 in H1 |- *; try lia.
        eapply Nat.leb_le in H1. eapply Nat.leb_le. 
        len. rewrite <- H1. rewrite !app_nth1; cbn; try lia.
    - rewrite csubst_mkApps /=.
      move/andP: H2 => [] eu ev.
      eapply isEtaExp_mkApps_intro => //. 2: solve_all.
      eauto. 
  Qed.

  Lemma etaExp_csubst a b n : 
    closed a -> isEtaExp []a -> isEtaExp [n] b -> isEtaExp [] (ECSubst.csubst a 0 b).
  Proof.
    intros.
    eapply etaExp_csubst' with (Γ := []); eauto.
  Qed.

  Lemma etaExp_fixsubst k b Γ Δ mfix idx d : 
    #|Γ| = k ->
    nth_error mfix idx = Some d ->
    closed (EAst.tFix mfix idx) ->
    forallb (fun x => isEtaExp (rev_map (S ∘ rarg) mfix) x.(dbody)) mfix ->
    isEtaExp (Γ ++ [1 + d.(EAst.rarg)] ++ Δ) b -> isEtaExp (Γ ++ Δ) (ECSubst.csubst (EAst.tFix mfix idx) k b).
  Proof.
    intros Hk Hnth Hcl. 
    remember (Γ ++ [1 + d.(EAst.rarg)] ++ Δ)%list as Γ_.
    funelim (isEtaExp Γ_ b); try simp_eta; eauto; try fold csubst;
      try toAll; try now repeat solve_all; subst.
    - intros. simp isEtaExp ; cbn. destruct (Nat.compare_spec #|Γ0| i) => //; simp_eta.
      + rewrite app_nth2 in H0; try lia. subst. rewrite minus_diag in H0. now cbn in H0.
      + rewrite app_nth2. lia.
        rewrite app_nth2 in H0. lia.
        eapply Nat.eqb_eq in H0. eapply Nat.eqb_eq.
        rewrite <- H0 at 2. destruct i. lia.
        cbn [Nat.pred].
        rewrite app_nth2. cbn. lia. f_equal. cbn. lia.
      + rewrite !app_nth1 in H0 |- *; try lia.
        eapply Nat.eqb_eq in H0. eapply Nat.eqb_eq. lia.
    - intros. solve_all. eapply a; eauto. solve_all.
    - eapply H with (Γ := 0 :: Γ0); cbn -[isEtaExp]; eauto. 
    - solve_all. move/andP: H2 => [] etab etab'. simp_eta.
      apply/andP. split; eauto.
      eapply H0 with (Γ := 0 :: Γ0); cbn; eauto.
    - solve_all. rtoProp. intuition eauto.
      solve_all. rewrite app_assoc. eapply a; cbn-[isEtaExp]; eauto. now len. cbn.
      now rewrite app_assoc.
      solve_all.
    - solve_all. rewrite app_assoc. solve_all.  eapply a; len; eauto.
      { cbn in Hcl. solve_all. rewrite Nat.add_0_r in a0. eauto. }
      now rewrite app_assoc.
      solve_all.
    - solve_all. fold csubst. move/andP: H1 => [] etaexp h.
      rewrite csubst_mkApps /=.
      rewrite isEtaExp_Constructor. solve_all.
      rewrite map_length. rtoProp; solve_all.
      solve_all.
      eapply a; eauto.
      solve_all.
    - solve_all. rewrite csubst_mkApps /=.
      move/andP : H2 => [] /andP [] eu ef ev.
      rewrite isEtaExp_mkApps //.
      simp expanded_head_viewc.
      rtoProp; repeat split.
      + rewrite /isEtaExp_fixapp in eu |- *. rewrite nth_error_map.
        destruct (nth_error mfix idx); try congruence.
        cbn. now len.
      + solve_all.
        rewrite app_assoc.  eapply a; len; eauto.
        { cbn in Hcl. solve_all. rewrite Nat.add_0_r in a0. eauto. }
        cbn. f_equal.
        rewrite app_assoc. do 2 f_equal.
        rewrite !rev_map_spec. f_equal. rewrite map_map. now eapply map_ext.
        solve_all.      
      + solve_all. eapply a; eauto. solve_all.
    - rewrite csubst_mkApps /=. rtoProp. destruct (Nat.compare_spec #|Γ0| n) => //; simp_eta.
      + rewrite isEtaExp_mkApps => //. cbn [expanded_head_viewc].
        rtoProp. repeat split; eauto.
        * unfold isEtaExp_fixapp. rewrite Hnth. len. destruct H2 as [Hn H2].
          subst. rewrite app_nth2 in Hn; try lia.
          rewrite minus_diag in Hn. cbn in Hn. eapply Nat.ltb_lt.
          eapply Nat.leb_le in Hn. lia.        
        * cbn in Hcl. solve_all. 
          setoid_rewrite <- lift_closed.
          rewrite <- (app_nil_r (Γ0 ++ Δ)). 
          eapply expanded_lift. now rewrite app_nil_r.
          eapply closed_upwards. eassumption. now len.
        * destruct H2. solve_all. eapply a ;eauto. solve_all.          
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. intros. destruct H2. split. 2:{ solve_all. eapply a; eauto. solve_all. }
        eapply Nat.leb_le in H2. eapply Nat.leb_le. rewrite app_nth2 in H2 |- *; try lia.
        len. rewrite <- H2. rewrite !app_nth2; cbn; try lia.
        eapply Nat.eq_le_incl. destruct (n - #|Γ0|) eqn:E. lia. f_equal. lia.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        intros. destruct H2.
        rtoProp. split. 2:{ solve_all. eapply a; eauto. solve_all. }
        rewrite app_nth1 in H2 |- *; try lia.
        eapply Nat.leb_le in H2. eapply Nat.leb_le. 
        len. rewrite <- H2. rewrite !app_nth1; cbn; try lia.
    - intros. rtoProp. rewrite csubst_mkApps /=.
      eapply isEtaExp_mkApps_intro => //. 2:{ solve_all. eapply a; eauto. solve_all. }
      eapply H; eauto.
  Qed.
  
  Lemma isEtaExp_substl Γ Δ s t : 
    #|Γ| = #|s| ->
    Forall (closedn 0) s ->
    forallb (isEtaExp []) s -> isEtaExp (Γ ++ Δ) t ->
    isEtaExp Δ (substl s t).
  Proof.
    induction s in Γ, t |- *; simpl; auto;
    rtoProp; intuition eauto using etaExp_csubst.
    - destruct Γ; eauto; cbn in *; lia.
    - invs H0. destruct Γ; cbn in H; invs H.
      eapply IHs; eauto. eapply etaExp_csubst' with (Γ := []); eauto.
  Qed.

  Lemma isEtaExp_fixsubstl Δ mfix idx t : 
    closed (EAst.tFix mfix idx) ->
    forallb (fun x => isEtaExp (rev_map (S ∘ rarg) mfix) x.(dbody)) mfix ->
    isEtaExp ((rev_map (S ∘ rarg) mfix) ++ Δ) t ->
    isEtaExp Δ (substl (fix_subst mfix) t).
  Proof.
    intros Hcl Hall Heta.
    cbn in Hcl. solve_all.
    unfold fix_subst.
    revert Hall Heta.
  
    generalize (@eq_refl _ mfix).
    setoid_rewrite <- app_nil_r at 1.
    generalize ((@nil (EAst.def EAst.term))).
    generalize (mfix) at 1 6 8.
    
    intros mfix0. revert mfix Δ t.
    induction mfix0  using rev_ind; intros.
    - cbn -[isEtaExp] in *. eauto.
    - cbn -[isEtaExp] in *. rewrite app_length Nat.add_comm. cbn -[substl isEtaExp].
      eapply IHmfix0. 
      + subst. now rewrite <- app_assoc.
      + solve_all.
      + eapply etaExp_fixsubst with (Γ := []); eauto.
        2: cbn; solve_all. 2: solve_all.
        2:{ cbn -[isEtaExp] in *. revert Heta.
            rewrite !rev_map_spec map_app rev_app_distr. cbn -[isEtaExp] in *. intros.
            exact Heta.
        }
        subst. rewrite <- app_assoc. cbn. now eapply nth_error_snoc.
  Qed.

  Lemma isEtaExp_iota_red pars args br :
    Forall (closedn 0) args ->
    forallb (isEtaExp []) args ->
    isEtaExp (repeat 0 (#|args| - pars)) br.2 ->
    isEtaExp [] (ETyping.iota_red pars args br).
  Proof.
    intros  Hcl etaargs etabr.
    unfold ETyping.iota_red.
    erewrite (isEtaExp_substl _ []); eauto.
    - shelve.
    - solve_all. eapply All_skipn. solve_all.
    - rewrite forallb_rev forallb_skipn //.
    - rewrite app_nil_r. eauto.
    Unshelve. len. now rewrite List.skipn_length.  
  Qed.
   
(*

  Lemma isEtaExp_fix_subst mfix : 
    forallb (isEtaExp (repeat 0 #|mfix|) ∘ dbody) mfix ->
    forallb (isEtaExp []) (ETyping.fix_subst mfix).
  Proof.
    unfold ETyping.fix_subst.
    generalize (@eq_refl _ #|mfix|). 
    generalize #|mfix| at 1 3 4.
    intros. solve_all. revert n H H0.
    induction n; intros; simp_eta; constructor; auto.
    + simp_eta.
    simp isEtaExp. solve_all. 
  Qed. 

  *)
 
  Lemma isEtaExp_cofix_subst mfix : 
    forallb (isEtaExp (repeat 0 #|mfix|) ∘ dbody) mfix ->
    forallb (isEtaExp []) (ETyping.cofix_subst mfix).
  Proof.
    intros. solve_all.
    unfold ETyping.cofix_subst.
    unfold cofix_subst. generalize #|mfix|. intros n. solve_all. induction n.
      + econstructor.
      + econstructor. simp_eta. solve_all. now rewrite app_nil_r. solve_all.
  Qed. 
  
  Lemma isEtaExp_cunfold_fix mfix idx n f : 
    forallb (closedn 0 ∘ dbody) mfix ->
    forallb (isEtaExp (rev_map (S ∘ rarg) mfix) ∘ dbody) mfix ->
    Ee.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp [] f.
  Proof.
    intros hcl heta.
    unfold Ee.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    eapply isEtaExp_fixsubstl.
    - cbn. solve_all. unfold EAst.test_def. eapply closed_upwards; eauto. lia.
    - solve_all.
    - solve_all. eapply All_nth_error in heta as []; eauto.
      now rewrite app_nil_r.
      Unshelve. eauto.
  Qed.
  
  Lemma isEtaExp_cunfold_cofix mfix idx n f : 
    forallb (closedn 0 ∘ dbody) mfix ->
    forallb (isEtaExp (repeat 0 #|mfix|) ∘ dbody) mfix ->
    Ee.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp [] f.
  Proof.
    intros hcl heta.
    unfold Ee.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    eapply isEtaExp_substl.
    4:{ solve_all. eapply nth_error_all in heta; eauto. rewrite app_nil_r. eapply heta. }
    - len. now rewrite cofix_subst_length.
    - unfold cofix_subst. generalize #|mfix|. clear - hcl. induction n; econstructor; eauto.
      cbn. solve_all. eapply closed_upwards; eauto. lia.
    - eapply isEtaExp_cofix_subst in heta. solve_all.
  Qed.

  Lemma isEtaExp_tApp Γ f u : isEtaExp Γ (mkApps f u) -> 
    let (hd, v) := decompose_app (mkApps f u) in
    match expanded_head_viewc hd with
      | expanded_head_construct ind i => isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v
      | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|v| && forallb (fun x => isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => (nth n Γ 0 <=? List.length v) && forallb (fun x => isEtaExp Γ x) v
      | expanded_head_other t discr => isEtaExp Γ hd && forallb (isEtaExp Γ) v
      end. (* 
    | expanded_head_construct kn c => isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args
    | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|args| && forallb mfix (fun x => isEtaExp Σ x.(dbody)) && forallb (isEtaExp Σ) args
    | expanded_head_rel n => (nth n Γ 0 <=? List.length v) && forallb (fun x => isEtaExp Γ x) v
    | expanded_head_other u discr => isEtaExp Σ hd && forallb (isEtaExp Σ) args
    end. *)
  Proof.
    destruct decompose_app eqn:da.
    rewrite (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    intros eq.
    rewrite isEtaExp_mkApps in eq; eauto.
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

Lemma isEtaExp_expanded Σ Γ t :
  isEtaExp Σ Γ t -> expanded Σ Γ t.
Proof.
  funelim (isEtaExp Σ Γ t); intros; solve_all; eauto.
  - econstructor. now eapply Nat.eqb_eq.
  - todo "tVar".
  - rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. eapply In_All in H.
    todo "tEvar".
  - eapply andb_true_iff in H1 as []; eauto.
  - eapply isEtaExp_app_expanded in H as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app with (args := []); eauto.
  - eapply andb_true_iff in H1 as []. destruct ind. econstructor; eauto.
    rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2. 
    eapply In_All in H0. solve_all.
  - congruence.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. 
    eapply In_All in H. solve_all.
  - eapply andb_true_iff in H0 as []. eapply In_All in H.
    rewrite forallb_InP_spec in H1. eapply forallb_Forall in H1.
    eapply isEtaExp_app_expanded in H0 as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app; eauto. solve_all.
  - rtoProp. rewrite forallb_InP_spec in H2. rewrite forallb_InP_spec in H3. eapply In_All in H. eapply In_All in H0. 
    unfold isEtaExp_fixapp in H1. destruct nth_error eqn:E; try congruence.
    eapply expanded_tFix.
    all: try now solve_all.
    eapply Nat.ltb_lt in H1. lia.
  - rtoProp. econstructor. eapply Nat.leb_le; eauto.  rewrite forallb_InP_spec in H1.
    eapply Forall_forall. solve_all. eapply H; eauto.
    eapply All_Forall, Forall_forall in H1; eauto.
  - eapply andb_true_iff in H1 as []. rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2.
    econstructor.
    + destruct u; inv Heq; eauto.
    + eauto.
    + eapply In_All in H0. solve_all.
Qed.

Lemma expanded_isEtaExp Σ Γ t :
  expanded Σ Γ t -> isEtaExp Σ Γ t.
Proof.
  induction 1; simp_eta; eauto.
  all: try now (
    (try (eapply andb_true_iff; split; eauto));
    (try eapply forallb_Forall); 
    eauto).
  - eapply Nat.eqb_eq; eauto.
  - rewrite isEtaExp_mkApps //. cbn [expanded_head_viewc].
    rtoProp. split. 2: solve_all. now eapply Nat.leb_le.
  - eapply isEtaExp_mkApps_intro; eauto. solve_all. 
  - rewrite isEtaExp_mkApps //. cbn [expanded_head_viewc]. rtoProp. repeat split.
    + unfold isEtaExp_fixapp. rewrite H4. eapply Nat.ltb_lt. lia.
    + solve_all.
    + solve_all.
  - rewrite isEtaExp_Constructor. eapply andb_true_iff.
    split. 2: eapply forallb_Forall.
    2: solve_all. eapply expanded_isEtaExp_app_; eauto.
Qed.

Definition isEtaExp_constant_decl Σ cb := 
  option_default (isEtaExp Σ []) cb.(cst_body) true.

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


Lemma closedn_mkApps k f l : closedn k (mkApps f l) = closedn k f && forallb (closedn k) l.
Proof.
  induction l in f |- *; cbn; auto.
  - now rewrite andb_true_r.
  - now rewrite IHl /= andb_assoc.
Qed.

Lemma lookup_inductive_pars_constructor_pars_args Σ {ind n pars args} : 
  lookup_constructor_pars_args Σ ind n = Some (pars, args) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rewrite /lookup_constructor_pars_args /lookup_inductive_pars.
  rewrite /lookup_inductive. destruct lookup_minductive => //.
  cbn. do 2 destruct nth_error => //. congruence.
Qed.

Lemma eval_construct  {fl : Ee.WcbvFlags} Σ kn c args e : 
  Ee.eval Σ (mkApps (tConstruct kn c) args) e -> ∑ args', (e = mkApps (tConstruct kn c) args') × All2 (Ee.eval Σ) args args'.
Proof.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. exists []=> //.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr.
    * subst f'. 
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
    * now cbn in i.
Qed.

Lemma app_tip_nil {A} (l : list A) (x : A) : (l ++ [x])%list <> [].
Proof.
  destruct l; cbn; congruence.
Qed.

Lemma eval_mkApps_Construct {fl : Ee.WcbvFlags} Σ kn c args args' : 
  All2 (Ee.eval Σ) args args' ->
  Ee.eval Σ (mkApps (tConstruct kn c) args) (mkApps (tConstruct kn c) args').
Proof.
  revert args'. induction args using rev_ind; intros args'; destruct args' using rev_case; intros a.
  - depelim a. constructor => //.
  - depelim a. cbn. now apply app_tip_nil in H.
  - depelim a. now apply app_tip_nil in H.
  - eapply All2_app_inv in a as []. 2:{ eapply All2_length in a. len in a. cbn in a. lia. } 
    depelim a0. clear a0. rewrite !mkApps_app /=.
    constructor; auto.
    destruct args' using rev_ind; try now rewrite ?mkApps_app; cbn; destruct Ee.with_guarded_fix; eauto.
    cbn. rewrite Ee.isFixApp_mkApps; eauto.
    cbn. try now rewrite ?mkApps_app; cbn; destruct Ee.with_guarded_fix; eauto.
Qed.

Definition remove_last {A} (args : list A) := 
  List.firstn (#|args| - 1) args.

Lemma remove_last_app {A} (l : list A) x : 
  remove_last (l ++ [x]) = l.
Proof.
  unfold remove_last. cbn. len.
  replace (#|l| + 1 -1) with #|l| by lia.
  rewrite firstn_app Nat.sub_diag /= firstn_all app_nil_r //.
Qed.

Arguments isEtaExp : simpl never.

Lemma isEtaExp_tApp' {Σ} {Γ} {f u} : isEtaExp Σ Γ (tApp f u) -> 
  let (hd, args) := decompose_app (tApp f u) in
  match expanded_head_viewc hd with
  | expanded_head_construct kn c =>
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ Γ) args
  | expanded_head_fix mfix idx => 
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    isEtaExp_fixapp mfix idx #|args| && forallb (fun d => isEtaExp Σ (rev_map (fun  d => 1 + d.(rarg)) mfix ++ Γ) d.(dbody)) mfix && forallb (isEtaExp Σ Γ) args
  | expanded_head_rel n => 
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    (nth n Γ 0 <=? List.length args) && forallb (fun x => isEtaExp Σ Γ x) args
  | expanded_head_other _ discr => 
    [&& isEtaExp Σ Γ hd, forallb (isEtaExp Σ Γ) args, isEtaExp Σ Γ f & isEtaExp Σ Γ u]
  end.
Proof.
  move/(isEtaExp_tApp Σ Γ f [u]).
  cbn -[decompose_app]. destruct decompose_app eqn:da.
  destruct expanded_head_viewc eqn:cv => //.
  - intros ->.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
    rewrite mkApps_app in H. noconf H.
    rewrite remove_last_app last_last. intuition auto.
    destruct l; cbn in *; congruence.
  - intros Hfix.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H. noconf H.
    rewrite mkApps_app in H. noconf H.
    rewrite remove_last_app last_last. intuition auto.
    destruct l; cbn in *; congruence.
  - intros ->.
    pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
    rewrite mkApps_app in H. noconf H.
    rewrite remove_last_app last_last. intuition auto.
    destruct l; cbn in *; congruence.
  - pose proof (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l using rev_case. cbn. intuition auto. destruct t => //.
    rewrite mkApps_app in H. noconf H.
    move=> /andP[] etat. rewrite forallb_app => /andP[] etal /=.
    rewrite andb_true_r => etaa. rewrite etaa andb_true_r.
    rewrite etat etal. cbn. rewrite andb_true_r.
    eapply isEtaExp_mkApps_intro; auto; solve_all.
Qed.

Lemma decompose_app_tApp_split f a hd args :
  decompose_app (tApp f a) = (hd, args) -> f = mkApps hd (remove_last args) /\ a = last args a.
Proof.
  unfold decompose_app. cbn.
  move/decompose_app_rec_inv' => [n [napp [hskip heq]]].
  rewrite -(firstn_skipn n args).
  rewrite -hskip. rewrite last_last; split => //.
  rewrite heq. f_equal.
  now rewrite remove_last_app.
Qed.

Lemma remove_last_last {A} (l : list A) (a : A) : l <> [] ->
  l = (remove_last l ++ [last l a])%list.
Proof.
  induction l using rev_ind.
  congruence.
  intros. rewrite remove_last_app last_last //.
Qed.

Lemma forallb_repeat {A} {p : A -> bool} {a : A} {n} : 
  p a ->
  forallb p (repeat a n).
Proof.
  intros pa.
  induction n; cbn; auto.
  now rewrite pa IHn.
Qed.

Lemma isEtaExp_lookup_ext {Σ} {kn d}: 
  isEtaExp_env Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends Σ' Σ × isEtaExp_decl Σ' d.
Proof.
  induction Σ; cbn.
  - move=> _; rewrite /declared_constant /lookup_env /= //.
  - move=> /andP[] etaa etaΣ.
    destruct a as [kn' d']; cbn in *.
    rewrite /declared_constant /=; rewrite /eq_kername; destruct kername_eq_dec.
    * subst kn'. move=> [=]. intros ->.
      exists Σ. split => //. now exists [(kn, d)].
    * move=> Hl. destruct (IHΣ etaΣ Hl) as [Σ' [ext eta]].
      exists Σ'; split => //.
      destruct ext as [Σ'' ->].
      now exists ((kn', d')::Σ'').
Qed.

Lemma isEtaExp_app_extends Σ Σ' ind k n :
  extends Σ Σ' ->
  wf_glob Σ' -> 
  isEtaExp_app Σ ind k n ->
  isEtaExp_app Σ' ind k n.
Proof.
  rewrite /isEtaExp_app.
  rewrite /lookup_constructor_pars_args /lookup_inductive /lookup_minductive.
  move=> ext wf.
  destruct (lookup_env Σ _) eqn:hl => //.
  rewrite (extends_lookup wf ext hl) /= //.
Qed.

Lemma isEtaExp_extends Σ Σ' Γ t : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp Σ Γ t ->
  isEtaExp Σ' Γ t.
Proof.
  intros ext wf.
  funelim (isEtaExp Σ Γ t); simp_eta => //; rtoProp; intuition eauto; rtoProp; intuition auto.
  - eapply In_All in H; solve_all.
  - eapply isEtaExp_app_extends; tea.
  - eapply In_All in H0. solve_all.
  - eapply In_All in H; solve_all.
  - eapply In_All in H; solve_all.
    rewrite isEtaExp_Constructor //. rtoProp; intuition auto.
    eapply isEtaExp_app_extends; tea.
    solve_all.
  - eapply In_All in H, H0. rewrite isEtaExp_mkApps => //.
    cbn [expanded_head_viewc]. rtoProp. repeat split; eauto.
    all: solve_all.
  - eapply In_All in H. rewrite isEtaExp_mkApps => //.
    cbn [expanded_head_viewc]. rtoProp. repeat split; eauto.
    all: solve_all.
  - eapply In_All in H0. apply isEtaExp_mkApps_intro; eauto. solve_all.
Qed.

Lemma isEtaExp_extends_decl Σ Σ' t : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp_decl Σ t ->
  isEtaExp_decl Σ' t.
Proof.
  intros ext wf; destruct t; cbn => //.
  rewrite /isEtaExp_constant_decl; destruct (cst_body c) => /= //.
  now eapply isEtaExp_extends.
Qed.

Lemma isEtaExp_lookup {Σ kn d}: 
  isEtaExp_env Σ -> wf_glob Σ ->
  lookup_env Σ kn = Some d ->
  isEtaExp_decl Σ d.
Proof.
  move=> etaΣ wfΣ.
  move/(isEtaExp_lookup_ext etaΣ) => [Σ' []] ext hd.
  now eapply isEtaExp_extends_decl.
Qed.

Arguments lookup_inductive_pars_constructor_pars_args {Σ ind n pars args}.

Lemma eval_etaexp {fl : Ee.WcbvFlags} {Σ a a'} : 
  isEtaExp_env Σ ->
  wf_glob Σ ->
  closed_env Σ ->
  closedn 0 a ->
  Ee.eval Σ a a' -> isEtaExp Σ [] a -> isEtaExp Σ [] a'.
Proof.
  intros etaΣ wfΣ HΣcl Hcl.
  induction 1 using eval_mkApps_rect.
  all:try simp isEtaExp; rewrite -!isEtaExp_equation_1 => //.
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc eqn:vc.
    * move => [hl [hf [ha /andP[] ise etal]]].
      rewrite hf in H. eapply eval_construct in H as [? []]. exfalso. solve_discr.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      unfold isEtaExp_fixapp in etal. destruct nth_error eqn:Efix; try easy.
      (* maybe the new relation does not preserve eta-expandedness? it's certainly hard to prove.

         From H we can get that remove_last l was long enough to trigger evaluation, so the shorter application is still expanded
      
      *)
      rewrite hf in H. eapply IHeval3. admit.
      eapply etaExp_csubst; eauto. admit.
      eapply IHeval2. admit.
      solve_all. admit.
      simp_eta in IHeval1.
      eapply IHeval1.
      subst. cbn in Hcl. rtoProp. eauto.
      subst. econstructor.
    * todo "rel".
    * move/and4P => [] etat etal etaf etaa.
      move / andP : Hcl => [] Hcl1 Hcl2; fold closedn in *.
      eapply IHeval3; eauto.
      { eapply closed_csubst. eapply eval_closed; eauto. eapply eval_closed in H; eauto. }
      move: (IHeval1 Hcl1 etaf); simp_eta => etab.      
      eapply etaExp_csubst; eauto.
      { eapply eval_closed; eauto. }
  - admit.
  - move : Hcl => /andP [] Hcl1 Hcl2; fold closedn in *.  
    rtoProp; intuition eauto.
    eapply IHeval2. rewrite /iota_red.
    { eapply closed_substl.
       eapply eval_closed in H; eauto. rewrite closedn_mkApps in H. rtoProp. solve_all. eapply All_skipn. solve_all.
      solve_all. eapply All_nth_error in H6 as []; eauto. revert i. len. now rewrite H2.
    }
    eapply isEtaExp_substl with (Γ := repeat 0 #|br.1|); eauto.
    { len. rewrite List.skipn_length repeat_length in H2 |- *. lia. }
    { eapply eval_closed in H; eauto. rewrite closedn_mkApps in H. rtoProp. solve_all. eapply All_skipn. solve_all. }
    rewrite isEtaExp_Constructor // in H7. solve_all.
    eapply All_skipn. move/andP: H7 => []. repeat solve_all.
    eapply forallb_nth_error in H6; tea.
    now erewrite H1 in H6.
  - rtoProp; intuition auto.
    eapply IHeval2. eapply isEtaExp_substl.
    now apply forallb_repeat.
    rewrite H2 in H6. simpl in H6.
    now move/andP: H6.
  - intros ise.
    eapply IHeval3.
    apply isEtaExp_tApp' in ise.
    destruct decompose_app eqn:da.
    destruct (cc_viewc t) eqn:cv.
    * destruct ise as [? [? []]]. rewrite H4 in H.
      eapply eval_construct in H as [? []];solve_discr.
    * todo "fix". 
    * move/and4P: ise => [] iset isel isef isea.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [av]).
      specialize (IHeval1 isef).
      rewrite isEtaExp_mkApps // in IHeval1.
      simp cc_viewc in IHeval1.
      move: IHeval1 => /andP [] / andP [] evrarg evfix evargs.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_fix; tea.
      simp isEtaExp in evfix.
      eapply All_app_inv. now solve_all. constructor; auto.
  - intros ise.
    apply isEtaExp_tApp' in ise.
    destruct decompose_app eqn:da.
    destruct (cc_viewc t) eqn:cv.
    * destruct ise as [? [? []]]. rewrite H4 in H.
      eapply eval_construct in H as [? []]; solve_discr.
    * todo "fix".
    * move/and4P: ise => [] iset isel isef isea.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [av]).
      specialize (IHeval1 isef).
      rewrite isEtaExp_mkApps // in IHeval1.
      simp construct_viewc in IHeval1.
      move: IHeval1 => /andP [] / andP [] evrarg evfix evargs.
      todo "fix". (* 
      eapply isEtaExp_mkApps_intro => //.
      eapply All_app_inv. now solve_all. constructor; auto. *)
  - move=> /andP[] hdiscr hbrs. specialize (IHeval1 hdiscr).
    move: IHeval1. rewrite isEtaExp_mkApps // /= => /andP[] hcof hargs.
    eapply IHeval2. simp_eta. rtoProp; intuition auto.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hcof.
  -  move=> hdiscr. specialize (IHeval1 hdiscr).
    move: IHeval1. rewrite isEtaExp_mkApps // /= => /andP[] hcof hargs.
    eapply IHeval2. simp_eta.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hcof.
  - move=> _. eapply IHeval. eapply isEtaExp_lookup in H; tea.
    now move: H; rewrite /isEtaExp_decl /= /isEtaExp_constant_decl H0 /=.
  - intros hd.
    eapply IHeval2. specialize (IHeval1 hd).
    move: IHeval1.
    rewrite nth_nth_error in H1 *.
    destruct nth_error eqn:hnth.
    rewrite isEtaExp_Constructor.
    destruct args => //. now rewrite nth_error_nil in hnth.
    move=> /andP[] _ hargs. eapply nth_error_forallb in hnth; tea.
    depelim H0. now cbn in H1.
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct cc_viewc.
    * move=> [] hl [] hf [] ha /andP[] hl' etal.
      move: H H0. rewrite hf => H H0.
      destruct (eval_construct_size H) as [args' []]. subst f'.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [a']).
      rewrite isEtaExp_Constructor.
      apply/andP; split => //.
      + len. eapply All2_length in a0. rewrite -a0.
        rewrite (remove_last_last l a) // in hl'. len in hl'.
        now cbn in hl'.
      + solve_all.
        rewrite (remove_last_last l a) // in etal.
        eapply All_app in etal as [etal etaa].
        depelim etaa. clear etaa. rewrite -ha in i.
        eapply All_app_inv; try constructor; eauto.
        clear -H0 a0 etal. solve_all.
        destruct b as [ev Hev]. eapply (H0 _ _ ev) => //. lia.
    * todo "fix".
    * move/and4P => [] etat etal etaf etaa.
      eapply (isEtaExp_mkApps_intro _ f' [a']); eauto.
Qed.

Lemma isEtaExp_eval Σ {wfl : WcbvFlags} t v  :
eval Σ t v -> isEtaExp Σ [] t -> isEtaExp Σ [] v.
Admitted.

Local Hint Resolve isEtaExp_eval : core.
Local Hint Constructors eval : core.

Arguments eval : clear implicits.

Lemma eval_opt_to_target Σ t v  :
@eval opt_wcbv_flags Σ t v -> isEtaExp Σ [] t -> @eval target_wcbv_flags Σ t v.
Proof.
intros H. depind H; intros Hexp; eauto.
- todo "box".
- todo "lambda".
- simp_eta in Hexp. rtoProp. econstructor. eauto. eapply IHeval2. todo "isEtaExp csubst".
- todo "case".
- todo "case".
- destruct argsv.
  + cbn -[isEtaExp] in *. todo "impossible due to expansion".
  + eapply eval_trans. eapply eval_app_cong.
    * eapply IHeval1. todo "exp".
    * cbn. destruct argsv using rev_ind; cbn; try eauto. now rewrite mkApps_app. 
    * eapply IHeval2. todo "exp". 
    * replace (tApp (mkApps fn (t :: argsv)) av) with (mkApps (tApp fn t) (argsv ++ [av])) in IHeval3 by now rewrite mkApps_app.
      replace (tApp (mkApps (tFix mfix idx) (t :: argsv)) av) with (mkApps (tApp (tFix mfix idx) t) (argsv ++ [av])) by now rewrite mkApps_app.
      forward IHeval3. todo "exp".
      revert IHeval3. generalize (argsv ++ [av])%list. clear - e. intros l.
      revert res.
      induction l using rev_ind.
      -- cbn in *. intros. eapply eval_fix'; eauto.
      -- rewrite !mkApps_app; cbn. intros res H.
         eapply eval_trans.
         eapply eval_mkApps_inv with (args := [x]) in H as (? & ? & ?).
         eapply eval_app_cong_tApp. eapply IHl; eauto.
         cbn in *. eauto.
         eapply value_final, eval_to_value; eauto.
- todo "impossible due to expansion".
- cbn in unguarded. congruence.
- todo "case".
- todo "proj".
- todo "const".
- todo "proj".
- todo "proj".
- eapply eval_app_cong.
  + eapply IHeval1. todo "exp".
  + eapply IHeval2. todo "exp".
  + destruct f'; cbn in *; eauto.

Qed.
 