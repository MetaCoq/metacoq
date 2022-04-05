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
From MetaCoq.Erasure Require Import EAst EGlobalEnv EAstUtils EEnvMap EExtends EWellformed.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalInd.

Set Default Proof Using "Type*".

Definition switch_unguarded_fix fl := 
  {| with_prop_case := fl.(@with_prop_case);
     with_guarded_fix := false |}.

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

Local Arguments eval : clear implicits.

Lemma eval_app_cong_tApp fl Σ t v args res :
  eval (switch_unguarded_fix fl) Σ t v ->  
  eval (switch_unguarded_fix fl) Σ (tApp v args) res ->
  eval (switch_unguarded_fix fl) Σ (tApp t args) res.
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
| expanded_tRel_app (n : nat) args m : nth_error Γ n = Some m -> forall Hle : m <= #|args|, Forall (expanded Γ) args -> expanded Γ (mkApps (tRel n) args)
| expanded_tVar (id : ident) : expanded Γ (tVar id)
| expanded_tEvar (ev : nat) (args : list term) : Forall (expanded Γ) args -> expanded Γ (tEvar ev args)
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
  Forall (fun d => isLambda d.(dbody) /\
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
     (∀ (Γ : list nat) (n : nat) (args : list term) (m : nat),
         nth_error Γ n = Some m ->
          (m ≤ #|args|) ->
	        Forall (expanded Σ Γ) args
        → Forall (P Γ) args 
        → P Γ (mkApps (tRel n) args)) →
    (forall id : ident, forall Γ, P Γ (tVar id)) →
    (forall (ev : nat) (args : list term) Γ, Forall (expanded Σ Γ) args → Forall (P Γ) args → P Γ (tEvar ev args)) 
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
                isLambda d0.(dbody) /\
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
  intros Σ P HRel_app HVar HEvar HLamdba HLetIn HmkApps HConst HCase HProj HFix HCoFix HConstruct HBox.
  fix f 3.
  intros Γ t Hexp.  destruct Hexp; eauto.
  - eapply HRel_app; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HEvar; eauto. clear - f H. induction H; econstructor; eauto.
  - eapply HmkApps; eauto. clear - f H0. induction H0; econstructor; eauto.
  - eapply HCase; eauto. induction H; econstructor; eauto.
  - assert (Forall (P Γ) args). { clear - H0 f. induction H0; econstructor; eauto. }
    eapply HFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H. induction H; econstructor; cbn in *; intuition eauto; split.
  - eapply HCoFix; eauto.
    revert H. clear - f.
    generalize mfix at 1 3. intros mfix0 H.  induction H; econstructor; cbn in *; eauto; split.
  - eapply HConstruct; eauto.
    clear - H1 f. induction H1; econstructor; eauto.
Qed.

Definition expanded_constant_decl Σ (cb : constant_body) : Prop :=
  on_Some_or_None (expanded Σ []) cb.(cst_body).
    
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

Local Hint Constructors expanded : core.

From MetaCoq.SafeChecker Require Import PCUICWfEnv.
     
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EArities Extract Prelim
    ELiftSubst ESpineView ECSubst.

Global Hint Rewrite repeat_length : len.

Lemma expanded_closed Σ Γ t : 
  expanded Σ Γ t -> ELiftSubst.closedn #|Γ| t.
Proof.
  induction 1; cbn; eauto.
  all: try now (rewrite ?closedn_mkApps; rtoProp; repeat solve_all).
  - rewrite closedn_mkApps. rtoProp. split. cbn.
    + eapply nth_error_Some_length in H. now eapply Nat.ltb_lt.
    + solve_all.
  - rtoProp. repeat split. eauto. solve_all. revert b. now len.
  - rewrite closedn_mkApps. rtoProp. repeat split; cbn; solve_all.
    revert  b. now len.
  - solve_all. revert b. now len.
Qed.

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
  
Ltac toAll := 
    repeat match goal with 
      | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
    end.

Import ECSubst.

Section isEtaExp.
  Context (Σ : global_declarations).
  
  Definition isEtaExp_app ind c k :=
    match lookup_constructor_pars_args Σ ind c with
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
    | tRel i => option_default (Nat.eqb 0) (nth_error Γ i) false
    | tEvar ev args => forallb_InP args (fun x H => isEtaExp Γ x)
    | tLambda na M => isEtaExp (0 :: Γ) M
    | tApp u v napp nnil with expanded_head_viewc u := 
      { | expanded_head_construct ind i => isEtaExp_app ind i (List.length v) && forallb_InP v (fun x H => isEtaExp Γ x)
        | expanded_head_fix mfix idx => 
          isEtaExp_fixapp mfix idx (List.length v) && 
          forallb_InP mfix (fun x H => isLambda x.(dbody) && isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) && forallb_InP v (fun x H => isEtaExp Γ x)
        | expanded_head_rel n => option_default (fun m => m <=? List.length v) (nth_error Γ n) false && forallb_InP v (fun x H => isEtaExp Γ x) 
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
  Proof using Σ.
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
      | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|v| && 
        forallb (fun x => isLambda x.(dbody) && isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => option_default (fun m => m <=? List.length v) (nth_error Γ n) false && forallb (fun x => isEtaExp Γ x) v
      | expanded_head_other t discr => isEtaExp Γ f && forallb (isEtaExp Γ) v
    end.
  Proof.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn -[isEtaExp]. destruct (expanded_head_viewc f); cbn -[isEtaExp]; simp isEtaExp => //.
  Qed.

  Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
  Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

  Definition is_cons {A} (l : list A) := match l with [] => false | _ => true end.
  
  Lemma isEtaExp_mkApps Γ f v : ~~ isApp f -> 
    isEtaExp Γ (mkApps f v) = match expanded_head_viewc f with 
      | expanded_head_construct ind i => isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v
      | expanded_head_fix mfix idx => 
        isEtaExp_fixapp mfix idx #|v| && 
        forallb (fun x => isLambda x.(dbody) && isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => option_default (fun m => m <=? List.length v) (nth_error Γ n) false && forallb (fun x => isEtaExp Γ x) v
      | expanded_head_other t discr => isEtaExp Γ f && forallb (isEtaExp Γ) v
    end.
  Proof using Σ.
    intros napp.
    destruct v using rev_case; simp_eta.
    - destruct expanded_head_viewc; rewrite ? andb_true_r //. cbn. unfold isEtaExp_fixapp. now destruct (nth_error); cbn.
      cbn.
      destruct (nth_error Γ n) as [m | ]; cbn; try reflexivity.
      destruct (Nat.eqb_spec 0 m), (Nat.leb_spec m 0); try reflexivity; lia.
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
      + simp_eta in et.
       destruct (nth_error Γ n) as [m | ] eqn:Heq; cbn in et; try eauto.
        eapply Nat.eqb_eq in et. rewrite <- et.
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
        destruct (nth_error Γ n) as [m | ] eqn:Heq; cbn in H0; eauto.
        cbn. eapply Nat.leb_le in H0. eapply Nat.leb_le. revert H0. len. lia.
        solve_all. eapply All_app_inv. 2: eapply All_app_inv. all: solve_all.
      + rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
        destruct (expanded_head_viewc t0) => //.
        move/andP: et => [] -> /=. rtoProp; solve_all.
        rewrite forallb_app. rtoProp; repeat solve_all.
        eapply All_app_inv; eauto.
  Qed.

  Lemma nth_error_app_Some {X} (A B : list X) n x : 
    nth_error A n = Some x -> nth_error (A ++ B) n = Some x.
  Proof.
    induction n in A |- *; destruct A; cbn; try congruence.
    eauto.
  Qed.

  Lemma expanded_weakening Γ' Γ t :
    isEtaExp Γ t ->
    isEtaExp (Γ ++ Γ') t.
  Proof.
    funelim (isEtaExp Γ t); simp_eta; eauto; intros Hexp; toAll; solve_all; rtoProp; repeat solve_all; eauto.
    - destruct nth_error eqn:E; try easy. erewrite nth_error_app_Some; eauto.
    - rewrite app_assoc. eapply a, b. reflexivity.
    - rewrite app_assoc. eapply a, b. reflexivity.
    - rewrite isEtaExp_mkApps => //. cbn [expanded_head_viewc]. rtoProp; repeat solve_all.
    - rewrite isEtaExp_mkApps => //. cbn [expanded_head_viewc]. rtoProp; repeat solve_all.
      rewrite app_assoc. rtoProp; intuition auto.
    - rewrite isEtaExp_mkApps => //. cbn [expanded_head_viewc]. rtoProp; repeat solve_all.
      destruct nth_error eqn:E; try easy. erewrite nth_error_app_Some; eauto.
    - rewrite isEtaExp_mkApps => //. rewrite Heq. rtoProp; repeat solve_all.
  Qed.

(*   Lemma expanded_lift Γ' Γ'' Γ t :
    isEtaExp (Γ' ++ Γ)%list t ->
    isEtaExp (Γ' ++ Γ'' ++ Γ)%list (lift #|Γ''| #|Γ'| t).
  Proof.
  Admitted.
 *)
  Lemma isEtaExp_closed Γ t : 
    isEtaExp Γ t -> closedn #|Γ| t.
  Proof.
    funelim (isEtaExp Γ t); simp_eta; cbn [closedn];
    rewrite ?closedn_mkApps; rtoProp; (try toAll); repeat solve_all.
    - destruct nth_error eqn:Hn; cbn in H; try easy.
      eapply nth_error_Some_length in Hn. now eapply Nat.ltb_lt.
    - eapply a in b. 2: f_equal. revert b. now len.
    - eapply a in b. 2: f_equal. revert b. now len.
    - cbn. solve_all. rtoProp; intuition auto. eapply a in H0. 2: reflexivity. revert H0. now len.
    - destruct nth_error eqn:Hn; cbn in H1; try easy.
      eapply nth_error_Some_length in Hn. now eapply Nat.ltb_lt.
  Qed.

  Lemma etaExp_csubst' a k b n Γ Δ : 
    #|Γ| = k ->
    isEtaExp [] a -> isEtaExp (Γ ++ [n] ++ Δ) b -> isEtaExp (Γ ++ Δ) (ECSubst.csubst a k b).
  Proof.
    intros Hk H.
    assert (Hcl : closed a) by now eapply isEtaExp_closed in H. revert H.
    remember (Γ ++ [n] ++ Δ)%list as Γ_.
    funelim (isEtaExp Γ_ b); try simp_eta; eauto; try fold csubst;
      try toAll; repeat solve_all; subst.
    - intros. simp isEtaExp ; cbn. destruct (Nat.compare_spec #|Γ0| i) => //; simp_eta.
      + eapply expanded_weakening with (Γ := []). eauto.
      + rewrite nth_error_app2. lia.
        rewrite !nth_error_app2 in H0. lia. cbn. lia.
        erewrite option_default_ext; eauto.
        f_equal. destruct i; cbn; lia.
      + now rewrite !nth_error_app1 in H0 |- *; try lia.
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
      + solve_all. rtoProp; intuition auto.
        now eapply isLambda_csubst.
        rewrite app_assoc.  eapply a0; len; eauto. cbn. f_equal.
        rewrite app_assoc. do 2 f_equal.
        rewrite !rev_map_spec. f_equal. rewrite map_map. now eapply map_ext.      
      + solve_all.
    - rewrite csubst_mkApps /=. rtoProp. destruct (Nat.compare_spec #|Γ0| n) => //; simp_eta.
      + eapply isEtaExp_mkApps_intro => //. 2: solve_all.
        now eapply expanded_weakening with (Γ := []).
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. split. 2: solve_all.
        rewrite !nth_error_app2 in H1 |- *; cbn; try lia.
        len. erewrite option_default_ext; eauto. f_equal.
        destruct n; cbn; lia.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. split. 2: solve_all. len. now rewrite !nth_error_app1 in H1 |- *; try lia.
    - rewrite csubst_mkApps /=.
      move/andP: H2 => [] eu ev.
      eapply isEtaExp_mkApps_intro => //. 2: solve_all.
      eauto. 
  Qed.

  Lemma etaExp_csubst a b n : 
    isEtaExp []a -> isEtaExp [n] b -> isEtaExp [] (ECSubst.csubst a 0 b).
  Proof.
    intros.
    eapply etaExp_csubst' with (Γ := []); eauto.
  Qed.

  Lemma etaExp_fixsubst k b Γ Δ mfix idx d : 
    #|Γ| = k ->
    nth_error mfix idx = Some d ->
    closed (EAst.tFix mfix idx) ->
    forallb (fun x => isLambda x.(dbody) &&  isEtaExp (rev_map (S ∘ rarg) mfix) x.(dbody)) mfix ->
    isEtaExp (Γ ++ [1 + d.(EAst.rarg)] ++ Δ) b -> isEtaExp (Γ ++ Δ) (ECSubst.csubst (EAst.tFix mfix idx) k b).
  Proof using Type*.
    intros Hk Hnth Hcl. 
    remember (Γ ++ [1 + d.(EAst.rarg)] ++ Δ)%list as Γ_.
    funelim (isEtaExp Γ_ b); try simp_eta; eauto; try fold csubst;
      try toAll; try solve_all; subst.
    - intros. simp isEtaExp ; cbn. destruct (Nat.compare_spec #|Γ0| i) => //; simp_eta.
      + rewrite nth_error_app2 in H0; try lia; cbn in H0; try easy. subst. rewrite minus_diag in H0. cbn in H0. easy.
      + rewrite !nth_error_app2 in H0 |- *; cbn; try lia.
        erewrite option_default_ext; eauto. f_equal.
        destruct i; cbn; lia.
      + now rewrite !nth_error_app1 in H0 |- *; try lia.
    - intros. eapply forallb_All in H1; eapply All_mix in H; tea.
      eapply All_forallb, All_map, All_impl; tea; cbv beta.
      intros x Hx. eapply Hx; eauto. apply Hx.
    - eapply H with (Γ := 0 :: Γ0); cbn -[isEtaExp]; eauto. 
    - solve_all. move/andP: H2 => [] etab etab'. simp_eta.
      apply/andP. split; eauto.
      eapply H; eauto. solve_all.
      eapply H0 with (Γ := 0 :: Γ0); eauto. solve_all.
    - rtoProp. intuition eauto.
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
      rewrite forallb_map. 
      eapply All_forallb. clear Heq0 Heq.
      eapply All_impl; tea; cbv beta.
      intros x Hx.
      eapply Hx; eauto.
      solve_all. apply Hx.
    - solve_all. rewrite csubst_mkApps /=.
      move/andP : H2 => [] /andP [] eu ef ev.
      rewrite isEtaExp_mkApps //.
      simp expanded_head_viewc.
      rtoProp; repeat split.
      + rewrite /isEtaExp_fixapp in eu |- *. rewrite nth_error_map.
        destruct (nth_error mfix idx); try congruence.
        cbn. now len.
      + solve_all. rtoProp; intuition auto. now eapply isLambda_csubst.
        rewrite app_assoc.  eapply a; len; eauto.
        { cbn in Hcl. solve_all. rewrite Nat.add_0_r in a0. eauto. }
        cbn. f_equal.
        rewrite app_assoc. do 2 f_equal.
        rewrite !rev_map_spec. f_equal. rewrite map_map. now eapply map_ext.
        solve_all.      
      + eapply forallb_All in ev; eapply All_mix in H0; tea.
        eapply All_forallb, All_map, All_impl; tea; cbv beta.
        intros x Hx. eapply Hx; eauto. solve_all. apply Hx.
    - rewrite csubst_mkApps /=. rtoProp. destruct (Nat.compare_spec #|Γ0| n) => //; simp_eta.
      + rewrite isEtaExp_mkApps => //. cbn [expanded_head_viewc].
        rtoProp. repeat split; eauto.
        * unfold isEtaExp_fixapp. rewrite Hnth. len.
          subst. rewrite nth_error_app2 in H1; try lia.
          rewrite minus_diag in H1. cbn in H1. eapply Nat.ltb_lt.
          eapply Nat.leb_le in H1. lia.        
        * cbn in Hcl. solve_all. rtoProp; intuition auto.
          now eapply expanded_weakening.
        * eapply forallb_All in H2. eapply All_mix in H; tea.
          eapply All_forallb, All_map, All_impl; tea; cbv beta.
          intros x Hx. eapply Hx; eauto. apply Hx.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        rtoProp. intros.
        split. 2:{
          eapply forallb_All in H2; eapply All_mix in H; tea; clear H2.      
          eapply All_forallb, All_map, All_impl; tea; cbv beta.
          intros x Hx. eapply Hx; eauto. apply Hx. }
        rewrite !nth_error_app2 in H1 |- *; cbn; try lia. len.
        erewrite option_default_ext. eauto. f_equal.
        destruct n; cbn; lia.
      + rewrite isEtaExp_mkApps; eauto. cbn [expanded_head_viewc].
        intros. rtoProp. split. 2:{
          eapply forallb_All in H2; eapply All_mix in H; tea; clear H2.      
          eapply All_forallb, All_map, All_impl; tea; cbv beta.
          intros x Hx. eapply Hx; eauto. apply Hx. }
        len.
        now rewrite !nth_error_app1 in H1 |- *; try lia.
    - intros. rtoProp. rewrite csubst_mkApps /=.
      eapply isEtaExp_mkApps_intro => //.
       2:{ eapply forallb_All in H3; eapply All_mix in H0; tea; clear H3.      
        eapply All_map, All_impl; tea; cbv beta.
        intros x Hx. eapply Hx; eauto. apply Hx. }
      eapply H; eauto.
  Qed.
  
  Lemma isEtaExp_substl Γ Δ s t : 
    #|Γ| = #|s| ->
    forallb (isEtaExp []) s -> isEtaExp (Γ ++ Δ) t ->
    isEtaExp Δ (substl s t).
  Proof.
    induction s in Γ, t |- *; simpl; auto;
    rtoProp; intuition eauto using etaExp_csubst.
    - destruct Γ; eauto; cbn in *; lia.
    - destruct Γ; cbn in H; invs H.
      eapply IHs; eauto. eapply etaExp_csubst' with (Γ := []); eauto.
  Qed.

  Lemma isEtaExp_fixsubstl Δ mfix t : 
    forallb (fun x => isLambda x.(dbody) &&
      isEtaExp (rev_map (S ∘ rarg) mfix) x.(dbody)) mfix ->
    isEtaExp ((rev_map (S ∘ rarg) mfix) ++ Δ) t ->
    isEtaExp Δ (substl (fix_subst mfix) t).
  Proof using Type*.
    intros Hall Heta.
    assert (Hcl : closed (EAst.tFix mfix 0) ). { cbn. solve_all. rtoProp; intuition auto. eapply isEtaExp_closed in H0. revert H0. now len. }
    revert Hcl Hall Heta.  
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
    isEtaExp [] (EGlobalEnv.iota_red pars args br).
  Proof.
    intros  Hcl etaargs etabr.
    unfold EGlobalEnv.iota_red.
    erewrite (isEtaExp_substl _ []); eauto.
    - shelve.
    - solve_all. eapply All_skipn. solve_all.
    - rewrite app_nil_r. eauto.
    Unshelve. len. now rewrite List.skipn_length.  
  Qed.
   
(*

  Lemma isEtaExp_fix_subst mfix : 
    forallb (isEtaExp (repeat 0 #|mfix|) ∘ dbody) mfix ->
    forallb (isEtaExp []) (EGlobalEnv.fix_subst mfix).
  Proof.
    unfold EGlobalEnv.fix_subst.
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
    forallb (isEtaExp []) (EGlobalEnv.cofix_subst mfix).
  Proof.
    intros. solve_all.
    unfold EGlobalEnv.cofix_subst.
    unfold cofix_subst. generalize #|mfix|. intros n. solve_all. induction n.
      + econstructor.
      + econstructor. simp_eta. solve_all. now rewrite app_nil_r. solve_all.
  Qed. 
  
  Lemma isEtaExp_cunfold_fix mfix idx n f : 
    forallb (fun d => isLambda d.(dbody) && isEtaExp (rev_map (S ∘ rarg) mfix) d.(dbody)) mfix ->
    EGlobalEnv.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp [] f.
  Proof.
    intros heta.
    unfold EGlobalEnv.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    eapply isEtaExp_fixsubstl.
    - solve_all; rtoProp; intuition auto.
    - rewrite app_nil_r. solve_all. eapply All_nth_error in heta; eauto.
      now move/andP: heta.
  Qed.
  
  Lemma isEtaExp_cunfold_cofix mfix idx n f : 
    forallb (isEtaExp (repeat 0 #|mfix|) ∘ dbody) mfix ->
    EGlobalEnv.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp [] f.
  Proof.
    intros heta.
    unfold EGlobalEnv.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    eapply isEtaExp_substl.
    3:{ solve_all. eapply nth_error_all in heta; eauto. rewrite app_nil_r. eapply heta. }
    - len. now rewrite cofix_subst_length.
    - solve_all. unfold cofix_subst. generalize #|mfix|. clear - heta. induction n; econstructor; eauto.
      simp_eta. solve_all. now rewrite app_nil_r.
  Qed.

  Lemma isEtaExp_tApp Γ f u : isEtaExp Γ (mkApps f u) -> 
    let (hd, v) := decompose_app (mkApps f u) in
    match expanded_head_viewc hd with
      | expanded_head_construct ind i => isEtaExp_app ind i #|v| && forallb (isEtaExp Γ) v
      | expanded_head_fix mfix idx => isEtaExp_fixapp mfix idx #|v| && 
        forallb (fun x => isLambda x.(dbody) && isEtaExp (rev_map (S ∘ rarg) mfix ++ Γ) x.(dbody)) mfix && forallb (isEtaExp Γ) v
      | expanded_head_rel n => (option_default (fun m => m <=? List.length v) (nth_error Γ n) false) && forallb (fun x => isEtaExp Γ x) v
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

Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.

Lemma isEtaExp_app_expanded Σ ind idx n :
   isEtaExp_app Σ ind idx n = true <->
   exists mind idecl cname c,
   declared_constructor Σ (ind, idx) mind idecl (cname, c) /\ n ≥ ind_npars mind + c.
Proof.
  unfold isEtaExp_app, lookup_constructor_pars_args, lookup_inductive, lookup_minductive.
  split.
  - intros H. cbn in H.
    destruct lookup_env as [[| mind] | ] eqn:E; cbn in H; try congruence.
    destruct nth_error as [ idecl | ] eqn:E2; cbn in H; try congruence.
    destruct (nth_error (E.ind_ctors idecl) idx) as [ [cname ?] | ] eqn:E3; cbn in H; try congruence.
    repeat esplit.
    red. all: eauto. eapply leb_iff in H. lia.
  - intros (? & ? & ? & ? & [[]] & Hle).
    cbn.
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
  - eapply expanded_tRel_app with (args := []). destruct (nth_error); invs H. f_equal. eapply Nat.eqb_eq in H1; eauto. cbn. lia. econstructor.
  - rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. eapply In_All in H. econstructor. solve_all.
  - eapply andb_true_iff in H1 as []; eauto.
  - eapply isEtaExp_app_expanded in H as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app with (args := []); eauto.
  - eapply andb_true_iff in H1 as []. destruct ind. econstructor; eauto.
    rewrite forallb_InP_spec in H2. eapply forallb_Forall in H2. 
    eapply In_All in H0. solve_all.
  - econstructor. rewrite forallb_InP_spec in H0. eapply forallb_Forall in H0. 
    eapply In_All in H. solve_all.
  - eapply andb_true_iff in H0 as []. eapply In_All in H.
    rewrite forallb_InP_spec in H1. eapply forallb_Forall in H1.
    eapply isEtaExp_app_expanded in H0 as (? & ? & ? & ? & ? & ?).
    eapply expanded_tConstruct_app; eauto. solve_all.
  - rtoProp. rewrite forallb_InP_spec in H2. rewrite forallb_InP_spec in H3. eapply In_All in H. eapply In_All in H0. 
    unfold isEtaExp_fixapp in H1. destruct nth_error eqn:E; try congruence.
    eapply expanded_tFix.
    all: try now solve_all. solve_all; rtoProp; intuition auto.
    eapply Nat.ltb_lt in H1. lia.
  - rtoProp. destruct (nth_error) eqn:Hn; invs H0.
    econstructor. eauto. eapply Nat.leb_le; eauto.  rewrite forallb_InP_spec in H1.
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
  - rewrite isEtaExp_mkApps //. cbn [expanded_head_viewc].
    rtoProp. split. 2: solve_all. rewrite H.  now eapply Nat.leb_le.
  - eapply isEtaExp_mkApps_intro; eauto. solve_all. 
  - rewrite isEtaExp_mkApps //. cbn [expanded_head_viewc]. rtoProp. repeat split.
    + unfold isEtaExp_fixapp. rewrite H4. eapply Nat.ltb_lt. lia.
    + solve_all; rtoProp; intuition auto.
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
  unfold lookup_constructor, lookup_inductive. destruct lookup_minductive => //.
  cbn. do 2 destruct nth_error => //. congruence.
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
    isEtaExp_fixapp mfix idx #|args| && forallb (fun d => isLambda d.(dbody) && isEtaExp Σ (rev_map (fun  d => 1 + d.(rarg)) mfix ++ Γ) d.(dbody)) mfix && forallb (isEtaExp Σ Γ) args
  | expanded_head_rel n => 
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    option_default (fun m => m <=? List.length args) (nth_error Γ n) false && forallb (fun x => isEtaExp Σ Γ x) args
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

Lemma isEtaExp_lookup_ext {Σ} {kn d}: 
  isEtaExp_env Σ ->
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends Σ' Σ × isEtaExp_decl Σ' d.
Proof.
  induction Σ; cbn.
  - move=> _; rewrite /declared_constant /lookup_env /= //.
  - move=> /andP[] etaa etaΣ.
    destruct a as [kn' d']; cbn in *.
    elim: eqb_specT.
    * intros ?; subst kn'. move=> [=]. intros ->.
      exists Σ. split => //. now exists [(kn, d)].
    * intros hkn; move=> Hl. destruct (IHΣ etaΣ Hl) as [Σ' [ext eta]].
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

Lemma isEtaExp_extends {efl : EEnvFlags} Σ Σ' Γ t : 
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
    all: solve_all; rtoProp; intuition eauto.
  - eapply In_All in H. rewrite isEtaExp_mkApps => //.
    cbn [expanded_head_viewc]. rtoProp. repeat split; eauto.
    all: solve_all.
  - eapply In_All in H0. apply isEtaExp_mkApps_intro; eauto. solve_all.
Qed.

Lemma isEtaExp_extends_decl {efl : EEnvFlags} Σ Σ' t : 
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

Arguments lookup_inductive_pars_constructor_pars_args {Σ ind n pars args}.

Lemma Forall_last {A} (P : A -> Prop) a l : l <> [] -> Forall P l -> P (last l a).
Proof.
  intros. induction H0.
  - congruence.
  - destruct l.
    + cbn. eauto.
    + cbn. eapply IHForall. congruence.
Qed.

Lemma All_remove_last {A} (P : A -> Type) l : All P l -> All P (remove_last l).
Proof.
  intros. now eapply All_firstn.
Qed.

Lemma eval_etaexp {fl : Ee.WcbvFlags} {efl : EEnvFlags} {Σ a a'} : 
  isEtaExp_env Σ ->
  wf_glob Σ ->
  Ee.eval Σ a a' -> isEtaExp Σ [] a -> isEtaExp Σ [] a'.
Proof.
  intros etaΣ wfΣ.
  induction 1 as [ | ? ? ? ? ? ? ? ? IHs | | | | ? ? ? ? ? ? ? ? ? ? ? IHs | ? ? ? ? ? ? ? ? ? ? ? IHs | ? ? ? ? ? ? ? ? ? ? IHs | | | | | | |   ] using eval_mkApps_rect.
  all:try simp isEtaExp; rewrite -!isEtaExp_equation_1 => //.
  6:{  
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc eqn:vc.
    * move => [hl [hf [ha /andP[] ise etal]]].
      pose proof (H' := H).
      rewrite hf in H'. eapply eval_construct in H' as [? []]. exfalso. solve_discr.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      pose proof (mkApps_app (EAst.tFix mfix idx) argsv [av]).
      cbn in H3. rewrite <- H3. clear H3.
      subst.
      specialize eval_mkApps_tFix_inv_size with (Heval := H); intros [(args' & ? & Heq) | (? & ? & ? & ? & ?)]; eauto.
      -- eapply (f_equal decompose_app) in Heq. rewrite !decompose_app_mkApps in Heq => //. invs Heq.
         rewrite isEtaExp_mkApps => //.
         cbn [expanded_head_viewc]. rtoProp. repeat split.
         ++ unfold isEtaExp_fixapp in *. destruct nth_error eqn:Hn; try easy. len.
            eapply Nat.ltb_lt in etal.
            eapply Nat.ltb_lt. eapply All2_length in a0.
            rewrite remove_last_length' in a0 |-*. eauto. lia.
         ++ solve_all.
         ++ sq. solve_all. eapply All_app_inv. 2:{ repeat econstructor. eapply IHeval2. rewrite ha. eapply Forall_last; eauto. }
            eapply All_remove_last in isel.
            solve_all. destruct b.
            unshelve eapply IHs. 2: eauto. lia. eauto.
       -- rewrite !isEtaExp_mkApps in IHeval1 |- * => //.
          cbn [expanded_head_viewc] in *. forward IHeval1; rtoProp.
          ++ repeat split; solve_all. 2:{ unfold remove_last. now eapply All_firstn. }
             unfold isEtaExp_fixapp, cunfold_fix in *. destruct nth_error; invs H1. clear IHeval1.
             destruct nth_error; invs H4. eapply Nat.ltb_lt in etal. eapply Nat.ltb_lt. len.
             destruct l; try congruence.
          ++ repeat split; solve_all. 2:{ eapply All_app_inv; eauto. repeat econstructor; eauto. eapply IHeval2. rewrite ha. eapply Forall_last; eauto. }
             unfold isEtaExp_fixapp, cunfold_fix in *. destruct nth_error; invs H1.
             destruct nth_error; invs H4. eapply Nat.ltb_lt in H6, etal. eapply Nat.ltb_lt. len.
             destruct l; try congruence. cbn. rewrite remove_last_length' in H5; try congruence. cbn in *. lia.
      * intros (? & ? & ? & ?). rtoProp. solve_all.
        rewrite nth_error_nil in H6. easy.
      * move/and4P => [] etat etal etaf etaa.
        pose proof (mkApps_app (tFix mfix idx) argsv [av]). cbn in H3. rewrite <- H3. clear H3.
        specialize (IHeval1 etaf). 
        rewrite !isEtaExp_mkApps in IHeval1 |- * => //.
        cbn [expanded_head_viewc] in *. rtoProp. repeat split; solve_all.
        -- unfold isEtaExp_fixapp, cunfold_fix in *. destruct nth_error; invs H1.
           len. eapply Nat.ltb_lt. eapply Nat.ltb_lt in H3. lia.
        -- eapply All_app_inv; solve_all.
  }
  5:{
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc eqn:vc.
    * move => [hl [hf [ha /andP[] ise etal]]]. clear IHs.
      rewrite hf in H. eapply eval_construct in H as [? []]. exfalso. solve_discr.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      subst.
      eapply IHeval3.
      
      pose proof (mkApps_app fn argsv [av]).
      cbn in H3. rewrite <- H3. clear H3.

      assert (isEtaExp Σ [] a). { rewrite ha. eapply Forall_last; eauto. solve_all. }

      specialize eval_mkApps_tFix_inv_size with (Heval := H); intros [(args' & ? & Heq) | (? & ? & ? & ? & ?)]; eauto.
      -- solve_all. eapply (f_equal decompose_app) in Heq. rewrite !decompose_app_mkApps in Heq => //. invs Heq. sq.
         eapply isEtaExp_mkApps_intro. 
         eapply isEtaExp_cunfold_fix. 2: eauto. solve_all.
         now rewrite app_nil_r in H5.
         eapply All_app_inv. 2: repeat econstructor; eauto.
         eapply All_remove_last in isel.
         solve_all. destruct b.
         unshelve eapply IHs. 2: eauto. lia. eauto.
       -- forward IHeval1.
          rewrite isEtaExp_mkApps => //.
          cbn [expanded_head_viewc]. rtoProp. repeat split; solve_all.
          2: eapply All_firstn; eauto.
          unfold isEtaExp_fixapp, cunfold_fix in *.
          destruct nth_error; try easy. invs H1.
          destruct nth_error; try easy. invs H5. eapply Nat.ltb_lt. lia.
          rewrite isEtaExp_mkApps in IHeval1 => //.
          cbn [expanded_head_viewc] in IHeval1. rtoProp.
          eapply isEtaExp_mkApps_intro. 
          eapply isEtaExp_cunfold_fix. 2: eauto. solve_all.
          now rewrite app_nil_r in H10.
          eapply All_app_inv. 2: repeat econstructor; eauto.
          solve_all.
        * intros (? & ? & ? & ?). rtoProp. solve_all.
          rewrite nth_error_nil in H6. easy.
        * move/and4P => [] etat etal etaf etaa. eapply IHeval3.
          pose proof (mkApps_app fn argsv [av]). cbn in H3. rewrite <- H3. clear H3.
          specialize (IHeval1 etaf). 
          rewrite !isEtaExp_mkApps in IHeval1 => //.
          cbn [expanded_head_viewc] in *. rtoProp.
          eapply isEtaExp_mkApps_intro. 
          eapply isEtaExp_cunfold_fix. 2: eauto. solve_all.
          now rewrite app_nil_r in H6.
          eapply All_app_inv. 2: repeat econstructor; eauto.
          solve_all.
  }
  10:{ move/isEtaExp_tApp'.
  destruct decompose_app eqn:da.
  destruct expanded_head_viewc.
  * move=> [] hl [] hf [] ha /andP[] hl' etal.
    move: H H0. rewrite hf => H H0.
    destruct (eval_construct_size H) as [args' []]. subst f'.
    rewrite -[EAst.tApp _ _](mkApps_app _ _ [a']).
    rewrite isEtaExp_Constructor.
    apply/andP; split => //.
    + len. eapply All2_length in a0. rewrite -a0.
      rewrite (remove_last_last l a) // in hl'.
      rewrite app_length in hl'.
      now cbn in hl'.
    + solve_all.
      rewrite (remove_last_last l a) // in etal.
      eapply All_app in etal as [etal etaa].
      depelim etaa. clear etaa. rewrite -ha in i.
      eapply All_app_inv; try constructor; eauto.
      clear -H0 a0 etal. solve_all.
      destruct b as [ev Hev]. eapply (H0 _ _ ev) => //. lia.
  * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
    subst.
  
    assert (isEtaExp Σ [] a). { rewrite ha. eapply Forall_last; solve_all. }
    destruct with_guarded_fix eqn:guarded.
    {
    
    specialize eval_mkApps_tFix_inv_size with (Heval := H); intros [(args' & ? & Heq) | (? & ? & ? & ? & ?)]; eauto.
    -- subst. rewrite isFixApp_mkApps in H1 => //. destruct EAst.isLambda; easy.
    -- eapply (isEtaExp_mkApps_intro _ _ f' [a']); eauto.
       eapply IHeval1. rewrite isEtaExp_mkApps => //.
      cbn [expanded_head_viewc]. rtoProp.
      repeat split; solve_all.
      2: eapply All_firstn; eauto.
      unfold isEtaExp_fixapp,  cunfold_fix in *.
      destruct nth_error; try easy.
      invs H5. eapply Nat.ltb_lt. lia.

    }
    {
      specialize eval_mkApps_tFix_inv_size_unguarded with (Heval := H); intros Hinv; destruct Hinv as [[Heq ->] | (a_ & a_' & args' & argsv & Heq & Hall & n & fn & Hunf & Haa' & Hev & Hev' & Hsz)]; eauto.
      -- cbn in *. easy.
      -- eapply (isEtaExp_mkApps_intro _ _ f' [a']); eauto.
         unshelve eapply H0. 2: eauto. lia.
         eapply (isEtaExp_mkApps_intro).
         eapply (isEtaExp_mkApps_intro _ _ fn [a_']); eauto. 2: econstructor; [ | econstructor].
         ++ eapply isEtaExp_cunfold_fix. 2: eauto. solve_all. now rewrite app_nil_r in H5.
         ++ solve_all. eapply All_firstn in isel. unfold remove_last in Heq. eapply All_Forall in isel.
            setoid_rewrite Heq in isel. invs isel. eauto.
         ++ eapply forallb_Forall in isel. eapply Forall_firstn in isel. unfold remove_last in Heq.
            setoid_rewrite Heq in isel. eapply Forall_All in isel. invs isel. solve_all. subst; eauto.
            destruct b0. unshelve eapply H0. 2: eauto. lia. eauto.
       }
  * intros (? & ? & ? & ?). rtoProp. solve_all.
      rewrite nth_error_nil in H6. easy.
  * move/and4P => [] etat etal etaf etaa. 
  eapply (isEtaExp_mkApps_intro _ _ f' [a']); eauto.
  }
  1:{ move/isEtaExp_tApp'.
      destruct decompose_app eqn:da.
      destruct expanded_head_viewc.
      * clear IHs. move=> [] hl [] hf [] ha /andP[] hl' etal.
        move: H H0. rewrite hf => H H0.
        eapply eval_construct in H as [? []];solve_discr.
      * solve_all. rtoProp. solve_all. subst.

      destruct with_guarded_fix eqn:guarded.

      {
        specialize eval_mkApps_tFix_inv_size with (Heval := H); intros [(args' & ? & Heq) | (? & ? & ? & ? & ?)]; eauto. 
        -- solve_discr.
        -- eapply IHeval3. eapply etaExp_csubst. eapply IHeval2.
           rewrite H3. eapply Forall_last; solve_all.
           forward IHeval1.
           rewrite isEtaExp_mkApps => //.
           cbn [expanded_head_viewc]. rtoProp; solve_all; solve_all.
           2: eapply All_firstn; solve_all.
           unfold isEtaExp_fixapp, cunfold_fix in *.
           destruct nth_error; try easy. invs H8. eapply Nat.ltb_lt. lia.
           simp_eta in IHeval1. eauto.
      }
      {
        specialize eval_mkApps_tFix_inv_size_unguarded with (Heval := H); intros Hinv; destruct Hinv as [[Heq Heq'] | (a_ & a_' & args' & argsv & Heq & Hall & n & fn & Hunf & Haa' & Hsz & Hev & Hsz')]; eauto; try congruence.
        eapply IHeval3. eapply etaExp_csubst.
        
        eapply IHeval2. rewrite H3. eapply Forall_last. eauto. solve_all. 
        assert (isEtaExp Σ [] (mkApps (tApp fn a_') argsv) -> isEtaExp Σ []  (EAst.tLambda na b)) as IH. {
         unshelve eapply IHs; eauto.
        }
        simp_eta in IH. eapply IH.
        eapply (isEtaExp_mkApps_intro).
        eapply (isEtaExp_mkApps_intro _ _ fn [a_']); eauto. 2: econstructor; [ | econstructor].
        ++ eapply isEtaExp_cunfold_fix. 2: eauto. solve_all. now rewrite app_nil_r in H4.
        ++ solve_all. eapply All_firstn in H6 as isel. unfold remove_last in Heq. eapply All_Forall in isel.
           setoid_rewrite Heq in isel. invs isel. eauto.
        ++ eapply All_Forall in H6 as isel. eapply Forall_firstn in isel. unfold remove_last in Heq.
           setoid_rewrite Heq in isel. eapply Forall_All in isel. invs isel. solve_all. subst; eauto.
           destruct b1. unshelve eapply IHs. 2: eauto. lia. eauto.        
      }
     
       * solve_all. rtoProp. solve_all. rewrite nth_error_nil in H5; easy.
  * move/and4P => [] etat etal etaf etaa. simp_eta in IHeval1. eapply IHeval3, etaExp_csubst; eauto.  
  }

  - rtoProp. solve_all. eapply IHeval2, etaExp_csubst; eauto. 

  - rtoProp; intuition eauto.
    eapply IHeval2. rewrite /iota_red.
    eapply isEtaExp_substl with (Γ := repeat 0 #|br.1|); eauto.
    { len. lia. }
    rewrite isEtaExp_Constructor // in H4. solve_all.
    eapply All_skipn. move/andP: H4 => []. repeat solve_all.
    eapply forallb_nth_error in H6; tea.
    now erewrite H1 in H6.
  - rtoProp; intuition auto.
    eapply IHeval2. eapply isEtaExp_substl. shelve.
    now apply forallb_repeat.
    rewrite H2 in H6. simpl in H6.
    now move/andP: H6.
    Unshelve. now len.
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc.
    * clear IHs. move=> [] hl [] hf [] ha /andP[] hl' etal.
      move: H H0. rewrite hf => H H0.
      clear H0; eapply eval_construct in H as [? []]; solve_discr.
    * solve_all. rtoProp. solve_all. subst.
      specialize eval_mkApps_tFix_inv_size_unguarded with (Heval := H); intros Hinv; 
      destruct Hinv as [[Heq Heq'] | (a_ & a_' & args' & argsv & Heq & Hall & n & fn_ & Hunf & Hav & Hsza & Hev & Hsz)]; eauto; try congruence.

      -- invs Heq'. eapply IHeval1. 
         eapply (isEtaExp_mkApps_intro _ _ fn [av]); eauto. 2: econstructor; [ | econstructor].
         ++ eapply isEtaExp_cunfold_fix. 2: eauto. solve_all. now rewrite app_nil_r in H7.
         ++ eapply (H2 _ _ H1). lia. rewrite H6. eapply Forall_last. 2: solve_all. eauto.
      -- assert (isEtaExp Σ [] (mkApps (tApp fn_ a_') argsv) -> isEtaExp Σ [] (EAst.tFix mfix idx)).
        { intros; eapply H0; eauto. }
         exfalso.
         forward H7.
         eapply isEtaExp_mkApps_intro. 
         eapply (isEtaExp_mkApps_intro _ _ fn_ [a_']); eauto. 2: econstructor; [ | econstructor].
         ** eapply isEtaExp_cunfold_fix. 2: eauto. solve_all. now rewrite app_nil_r in H10.
         ** solve_all. eapply All_firstn in H9 as isel. unfold remove_last in Heq. eapply All_Forall in isel.
            setoid_rewrite Heq in isel. invs isel. eauto.
         ** eapply All_firstn in H9 as isel. unfold remove_last in Heq. eapply All_Forall in isel.
            setoid_rewrite Heq in isel. eapply Forall_All in isel. invs isel. solve_all; subst; eauto.
            destruct b0.
            unshelve eapply H0. 2: eauto. lia. eauto.
         ** simp_eta in H3. easy.
    * solve_all. rtoProp. solve_all. rewrite nth_error_nil in H8. easy.
    * move/and4P => [] etat etal etaf etaa.
      eapply IHeval1.
      eapply (isEtaExp_mkApps_intro _ _ fn [av]); eauto.
      eapply isEtaExp_cunfold_fix; tea.
      simp_eta in IHs. specialize (IHs etaf). easy.
  - move=> /andP[] hdiscr hbrs. specialize (IHeval1 hdiscr).
    move: IHeval1. rewrite isEtaExp_mkApps // /= => /andP[] hcof hargs.
    eapply IHeval2. simp_eta. rtoProp; intuition auto.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hcof. solve_all. now rewrite app_nil_r in H2.
  - move=> hdiscr. specialize (IHeval1 hdiscr).
    move: IHeval1. rewrite isEtaExp_mkApps // /= => /andP[] hcof hargs.
    eapply IHeval2. simp_eta.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hcof. solve_all. now rewrite app_nil_r in H2.
  - move=> _. eapply IHeval. eapply isEtaExp_lookup in H; tea.
    now move: H; rewrite /isEtaExp_decl /= /isEtaExp_constant_decl H0 /=.
  - intros hd.
    eapply IHeval2. specialize (IHeval1 hd).
    move: IHeval1.
    rewrite nth_nth_error in H1 *.
    destruct nth_error eqn:hnth.
    rewrite isEtaExp_Constructor.
    destruct args => //. now rewrite nth_error_nil in hnth.
    move=> /andP[] _ hargs.
    eapply nth_error_forallb in hnth; tea.
    depelim H0. now cbn in H1. Unshelve.
Qed.

(* Lemma isEtaExp_eval Σ {wfl : WcbvFlags} t v  :
eval Σ t v -> isEtaExp Σ [] t -> isEtaExp Σ [] v.
Admitted.

Local Arguments eval : clear implicits.
*)

Lemma mkApps_eq f args a t : ~~ isApp f -> mkApps f args = tApp a t ->
  args <> [] /\ a = (mkApps f (remove_last args)) /\ t = last args t.
Proof.
  intros napp eq.
  destruct args using rev_case.
  * cbn in eq. destruct f => //.
  * split => //.
    + intros neq. destruct args => //.
    + rewrite mkApps_app in eq. noconf eq.
      rewrite remove_last_app. split => //.
      now rewrite last_last. 
Qed.

Lemma isEtaExp_fixapp_mon {mfix idx n n'} : n <= n' -> isEtaExp_fixapp mfix idx n -> isEtaExp_fixapp mfix idx n'.
Proof.
  rewrite /isEtaExp_fixapp.
  destruct nth_error eqn:hnth => //.
  intros hn. move/Nat.ltb_lt => hl. apply Nat.ltb_lt.  lia.
Qed.

Definition isStuckFix' t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) => #|args| <=? narg
    | None => true
    end
  | _ => false
  end.

Lemma eval_stuck_fix_eq {fl Σ mfix idx args v} :
  with_guarded_fix ->
  forall eva : @eval fl Σ (mkApps (tFix mfix idx) args) v,
  ∑ args', All2 (fun a a' => @eval fl Σ a a') args args' ×
    ((isStuckFix' (tFix mfix idx) args' × v = mkApps (tFix mfix idx) args') + isEtaExp_fixapp mfix idx #|args|).
Proof.
  intros withguard.
  intros H; depind H; try solve_discr.
  + eapply mkApps_eq in H1 as [? []] => //; subst.
    specialize (IHeval1 mfix idx _ _ withguard eq_refl) as [args' []].
    exists (args' ++ [t']).
    rewrite (remove_last_last args t H1).
    split. eapply All2_app => //. rewrite -H3. eauto.
    destruct s.
    * destruct p; solve_discr.
    * right. len. eapply isEtaExp_fixapp_mon; tea. lia.
  + eapply mkApps_eq in H2 as [? []] => //; subst.
    specialize (IHeval1 mfix idx _ _ withguard eq_refl) as [args' []].
    exists (args' ++ [a']).
    rewrite (remove_last_last args a H2).
    split. eapply All2_app => //. rewrite -H4. eauto.
    destruct s.
    * destruct p; solve_discr.
    * right. len. eapply isEtaExp_fixapp_mon; tea. lia.
  + eapply mkApps_eq in H2 as [? []] => //; subst.
    specialize (IHeval1 mfix0 idx0 (remove_last args) _ withguard eq_refl) as [args' []].
    exists (args' ++ [av]).
    rewrite (remove_last_last args a H2).
    split. eapply All2_app => //. rewrite -H4. eauto.
    destruct s.
    * destruct p; solve_discr. noconf H3.
      right. len.
      move: e; unfold isEtaExp_fixapp.
      unfold EGlobalEnv.cunfold_fix. destruct nth_error eqn:hnth => //.
      intros [=]. rewrite H3. rewrite -(All2_length a0). eapply Nat.ltb_lt; lia.
    * right. len. eapply isEtaExp_fixapp_mon; tea. lia.
  + eapply mkApps_eq in H1 as [? []] => //; subst.
    specialize (IHeval1 mfix0 idx0 (remove_last args) _ withguard eq_refl) as [args' []].
    exists (args' ++ [av]).
    rewrite (remove_last_last args a H1).
    split. eapply All2_app => //. rewrite -H3. eauto.
    destruct s.
    * destruct p; solve_discr. noconf H2.
      left. split. 
      unfold isStuckFix'; rewrite e. len. eapply Nat.leb_le. lia.
      now rewrite -[tApp _ _](mkApps_app _ _ [av]).
    * right. len. eapply isEtaExp_fixapp_mon; tea. lia.
  + eapply mkApps_eq in H1 as [? []] => //; subst.
    specialize (IHeval1 mfix idx (remove_last args) _ withguard eq_refl) as [args' []].
    exists (args' ++ [a']).
    rewrite (remove_last_last args a H1).
    split. eapply All2_app => //. rewrite -H3. eauto.
    destruct s.
    * destruct p. subst f'. cbn in i.
      rewrite !negb_or in i.
      move/andP: i => [] /andP[] _ /=.
      rewrite Ee.isFixApp_mkApps /= //. cbn. rewrite withguard //.
    * right. len. eapply isEtaExp_fixapp_mon; tea. lia.
  + eapply atom_mkApps in i. destruct i => //. cbn in H0. subst args.
    exists []. split; eauto.
    left.
    unfold isStuckFix', cunfold_fix. destruct nth_error => //.
Qed.

Lemma isEtaExp_FixApp {Σ mfix idx l} :
  isEtaExp_fixapp mfix idx #|l| ->
  forallb (λ d : def EAst.term, isLambda d.(dbody) && isEtaExp Σ (rev_map (λ d0 : def term, 1 + rarg d0) mfix ++ []) (dbody d)) mfix ->
  forallb (isEtaExp Σ []) l ->
  isEtaExp Σ [] (mkApps (tFix mfix idx) l).
Proof.
  intros hmfix hm hl.
  funelim (isEtaExp Σ _ _) => //; solve_discr. noconf H.
  unfold isEtaExp_fixapp in hmfix. destruct nth_error => //.
  noconf H1. simp_eta. now rewrite hmfix hl /= hm /=.
  now cbn in d.
Qed.

Lemma forallb_firstn {A} {p : A -> bool} {n l} : forallb p l -> forallb p (firstn n l).
Proof.
  intros hl. induction l in n, hl |- *; cbn => //.
  - now rewrite firstn_nil.
  - destruct n; cbn => //.
    now move: hl => /= /andP[] -> /=.
Qed.
Lemma forallb_remove_last {A} {p : A -> bool} {l} : forallb p l -> forallb p (remove_last l).
Proof.
  intros hl; unfold remove_last. now apply forallb_firstn.
Qed.

Lemma forallb_last {A} {p : A -> bool} {l t} : l <> [] -> forallb p l -> p (last l t).
Proof.
  induction l => //. intros _. cbn. destruct l.
  - now move/andP.
  - move/andP => [] _ hl. apply IHl => //.
Qed.

Lemma isEtaExp_tFix {Σ mfix idx} : ~ isEtaExp Σ [] (tFix mfix idx).
Proof.
  intros he.
  now simp_eta in he.
Qed.

Lemma neval_to_stuck_fix {efl : EEnvFlags} {Σ mfix idx t} :
  isEtaExp_env Σ ->
  wf_glob Σ ->
  isEtaExp Σ [] t -> @eval opt_wcbv_flags Σ t (tFix mfix idx) -> False.
Proof.
  intros etaΣ wfΣ he hev.
  pose proof (eval_etaexp etaΣ wfΣ hev he).
  now apply isEtaExp_tFix in H.
Qed.

Lemma neval_to_stuck_fix_app {efl : EEnvFlags} {fl Σ mfix idx t args} :
  with_guarded_fix ->
  isEtaExp_env Σ ->
  wf_glob Σ ->
  isEtaExp Σ [] t -> @eval fl Σ t (mkApps (tFix mfix idx) args) -> False.
Proof.
  intros wguard etaΣ wfΣ he hev.
  pose proof (eval_etaexp etaΣ wfΣ hev he).
  move: H.
  move/isEtaExp_tApp.
  rewrite decompose_app_mkApps // /= // app_nil_r //.
  move/andP => [] /andP[] etaapp etamfix etaargs.
  eapply eval_to_value in hev.
  move: etaapp. rewrite /isEtaExp_fixapp.
  destruct nth_error eqn:hnth => // => /Nat.ltb_lt hrarg.
  eapply stuck_fix_value_args in hev.
  2:{ unfold cunfold_fix. rewrite hnth. reflexivity. }
  lia.
Qed.

Lemma isEtaExp_tApp_eval {fl} {Σ} {f u v} : 
  with_guarded_fix ->
  @eval fl Σ f v ->
  isEtaExp Σ [] (tApp f u) -> 
  (forall kn c args, v <> mkApps (tConstruct kn c) args) ->
  (forall mfix idx args, v <> mkApps (tFix mfix idx) args) ->
  let (hd, args) := decompose_app (tApp f u) in
  match expanded_head_viewc hd with
  | expanded_head_construct kn c => False
  | expanded_head_fix mfix idx =>
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    [&& isEtaExp_fixapp mfix idx #|remove_last args|,
    forallb (fun d => isLambda d.(dbody) && isEtaExp Σ (rev_map (fun  d => 1 + d.(rarg)) mfix ++ []) d.(dbody)) mfix,
    forallb (isEtaExp Σ []) (remove_last args) & isEtaExp Σ [] u]
  | expanded_head_rel n => False
  | expanded_head_other _ discr => 
    [&& isEtaExp Σ [] hd, forallb (isEtaExp Σ []) args, isEtaExp Σ [] f & isEtaExp Σ [] u]
  end.
Proof.
  intros wguard ev eta; revert eta ev.
  move/isEtaExp_tApp'.
  cbn -[decompose_app]. destruct decompose_app eqn:da.
  destruct expanded_head_viewc eqn:cv => //.
  * move=> [] hl [] ha [] ht /andP[] etaap etal.
    rewrite ha. intros h.
    eapply eval_construct in h as [? []]. subst v.
    intros Hc _. specialize (Hc ind n x). now apply Hc.
  * move=> [] hl [] ha [] ht /andP[] /andP[] etafix etab etal.
    rewrite ha.
    intros H; eapply eval_stuck_fix_eq in H as [args' [Hargs' [[]|]]]. subst v.
    intros _ Hfix. elimtype False. eapply Hfix; trea.
    intros Hc Hfix. intuition auto. rewrite i /= etab /=.
    rewrite forallb_remove_last // /=.
    rewrite ht. eapply forallb_last => //. rewrite wguard //.
  * move=> [] hl [] ha [] ht /andP[] hnth.
    now rewrite nth_error_nil /= in hnth.
Qed.

Lemma isEtaExp_closedn Σ Γ t : isEtaExp Σ Γ t -> closedn #|Γ| t.
Proof.
  move/isEtaExp_expanded. apply expanded_closed.
Qed.

Lemma all_isEtaExp_closedn Σ Γ t : forallb (isEtaExp Σ Γ) t -> forallb (closedn #|Γ|) t.
Proof.
  solve_all. solve_all. now eapply isEtaExp_closedn.
Qed.

Lemma isEtaExp_iota_red' Σ pars args br :
  forallb (isEtaExp Σ []) args ->
  isEtaExp Σ (repeat 0 (#|args| - pars)) br.2 ->
  isEtaExp Σ [] (EGlobalEnv.iota_red pars args br).
Proof.
  intros etaargs etabr.
  eapply isEtaExp_iota_red; eauto.
  apply all_isEtaExp_closedn in etaargs. solve_all.
Qed.

Lemma skipn_length {A} n (l : list A) : length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
  intros. rewrite IHl; auto with arith.
Qed.

Lemma eval_mkApps_inv' {wfl : WcbvFlags} Σ f args v :
  eval Σ (mkApps f args) v ->
  ∑ f' args', eval Σ f f' × All2 (eval Σ) args args' × eval Σ (mkApps f' args') v.
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. split => //. eapply eval_to_value in ev.
    split => //. now eapply value_final.
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [t']). split => //.
      rewrite mkApps_app.
      econstructor; tea. eapply All2_app; auto.
      econstructor; tea. eapply value_final. now eapply eval_to_value in ev2.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [a']). split => //. split; auto.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_beta; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix_value; tea. eapply value_final, eval_to_value; tea.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app. 
      eapply eval_fix'; eauto. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evars res]]]].
      exists f'', (args' ++ [a']); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_app_cong; tea. eapply value_final, eval_to_value; tea.
    + cbn in i. discriminate.
Qed.

Lemma eval_mkApps_inv_size {wfl : WcbvFlags} {Σ f args v} :
  forall ev : eval Σ (mkApps f args) v,
  ∑ f' args' (evf : eval Σ f f'),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva <= eval_depth ev) args args' &
      ∑ evres : eval Σ (mkApps f' args') v, eval_depth evres <= eval_depth ev].
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. exists ev => //. split => //.
    exact (size_final _ _ _ ev).
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [t']). exists evf'.
      rewrite mkApps_app. 
      split => //. cbn. lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      unshelve econstructor; tea.
      econstructor; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn. lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [a']). exists evf'. split => //. 
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists.
      eapply eval_beta; tea. 
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //. 
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix_value; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix'; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evfs evars [evres res]]]]].
      exists f'', (args' ++ [a']); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_app_cong; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia. 
    + cbn in i. discriminate.
Qed.

Lemma eval_deterministic_all {wfl : WcbvFlags} {Σ} {t v v'} :
  All2 (eval Σ) t v ->
  All2 (eval Σ) t v' ->
  v = v'.
Proof.
  induction 1 in v' |- *; intros H; depelim H; auto. f_equal; eauto.
  now eapply eval_deterministic.
Qed.

Lemma eval_mkApps_Construct_size {wfl : WcbvFlags} {Σ ind c args v} :
  forall ev : eval Σ (mkApps (tConstruct ind c) args) v,
  ∑ args' (evf : eval Σ (tConstruct ind c) (tConstruct ind c)),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva <= eval_depth ev) args args' &
      v = mkApps (tConstruct ind c) args'].
Proof.
  intros ev.
  destruct (eval_mkApps_inv_size ev) as [f'' [args' [? []]]].
  exists args'. 
  exists (eval_atom _ (tConstruct ind c) eq_refl).
  cbn. split => //. destruct ev; cbn => //; auto with arith.
  clear l. destruct (eval_construct _ _ _ _ _ ev) as [? []]. subst v.
  eapply (eval_construct _ _ _ []) in x as [? []]. subst f''. depelim a1.
  f_equal.
  eapply eval_deterministic_all; tea.
  eapply All2_impl; tea; cbn; eauto. now intros x y [].
Qed.

Lemma eval_app_cong_tApp' fl Σ t arg arg' res :
  @value (switch_unguarded_fix fl) t ->  
  @eval (switch_unguarded_fix fl) Σ arg arg' ->
  @eval (switch_unguarded_fix fl) Σ (tApp t arg') res ->
  @eval (switch_unguarded_fix fl) Σ (tApp t arg) res.
Proof.
  intros. depind H0.
  - eapply eval_app_cong_tApp; tea. econstructor. constructor. constructor. exact H.
  - pose proof (eval_trans' H H0_0). subst a'. econstructor; tea.
  - pose proof (eval_trans' H H0_0). subst av. eapply eval_fix; tea.
  - pose proof (eval_trans' H H0_0). subst av. eapply eval_fix_value; tea.
  - eapply value_final in X. pose proof (eval_trans' X H0_). subst f.
    pose proof (eval_trans' H H0_0). subst av.
    eapply eval_fix'; tea.
  - eapply eval_app_cong; tea.
    eapply eval_trans; tea.
  - now cbn in i.
Qed.

Lemma eval_value_cong {fl} {Σ} {f args args' res} : 
  @value (switch_unguarded_fix fl) f ->
  All2 (@eval (switch_unguarded_fix fl) Σ) args args' ->
  @eval (switch_unguarded_fix fl) Σ (mkApps f args') res ->
  @eval (switch_unguarded_fix fl) Σ (mkApps f args) res.
Proof.
  intros vf.
  revert args' res; induction args using rev_ind.
  - intros args' res H; depelim H. now cbn.
  - intros args' res H.
    eapply All2_app_inv_l in H as [r1 [r2 [? []]]]. depelim a0. depelim a0. subst args'. 
    intros H.
    rewrite mkApps_app in H |- *. rewrite mkApps_app.
    eapply eval_mkApps_inv' in H as [f' [args' [evf' [evargs' evres]]]].
    depelim evargs'. depelim evargs'.
    pose proof (eval_trans' e0 e). subst y0.
    eapply eval_app_cong_tApp. eapply IHargs. tea. exact evf'.
    eapply eval_app_cong_tApp'. now eapply eval_to_value in evf'. exact e0. exact evres.
Qed.

Lemma eval_app_cong_mkApps {fl} {Σ} {f f' res : EAst.term} {args args'} :
  @eval (switch_unguarded_fix fl) Σ f f' → 
  All2 (@eval (switch_unguarded_fix fl) Σ) args args' ->
  @eval (switch_unguarded_fix fl) Σ (mkApps f' args') res → 
  @eval (switch_unguarded_fix fl) Σ (mkApps f args) res.
Proof.
  revert args' res; induction args using rev_ind.
  - cbn. intros. eapply eval_trans. tea. now depelim X.
  - intros args' res evf evargs evf'.
    rewrite !mkApps_app. cbn.
    eapply All2_app_inv_l in evargs as [r1 [r2 [? []]]]. depelim a0. depelim a0. subst args'. 
    rewrite mkApps_app in evf'.
    eapply eval_mkApps_inv' in evf' as [f'' [args' [evf'' [evargs' evres]]]].
    depelim evargs'. depelim evargs'.
    pose proof (eval_trans' e0 e). subst y0.
    eapply eval_app_cong_tApp. eapply IHargs. tea. exact a. exact evf''.
    eapply eval_app_cong_tApp'. now eapply eval_to_value in evf''. exact e0. exact evres.
Qed.

Lemma All_eval_etaexp {fl : WcbvFlags} {efl : EEnvFlags} Σ l l' :
  isEtaExp_env Σ ->
  wf_glob Σ ->
  All2 (eval Σ) l l' -> forallb (isEtaExp Σ []) l -> forallb (isEtaExp Σ []) l'.
Proof.
  intros; solve_all. now eapply eval_etaexp.
Qed.

Lemma isFix_mkApps f args : ~~ isFix f -> ~~ isFix (mkApps f args).
Proof.
  induction args using rev_ind => //.
  intros hf.
  rewrite mkApps_app /= //.
Qed.


Lemma nisFixApp_nisFix f : ~~ isFixApp f -> ~~ isFix f.
Proof.
  unfold isFixApp.
  destruct decompose_app eqn:da => /=.
  rewrite (decompose_app_inv da).
  intros h. now apply isFix_mkApps.
Qed.

Lemma eval_opt_to_target {fl: WcbvFlags} {efl : EEnvFlags} Σ t v :
  with_guarded_fix ->
  isEtaExp_env Σ ->
  wf_glob Σ ->
  @eval fl Σ t v -> 
  isEtaExp Σ [] t -> 
  @eval (switch_unguarded_fix fl) Σ t v.
Proof.
  intros wguard etaΣ wfΣ.
  intros H.
  induction H using eval_mkApps_rect.
  - move/(isEtaExp_tApp_eval wguard H) => IH.
    forward IH by (intros; intro; solve_discr).
    forward IH by (intros; intro; solve_discr).
    destruct (decompose_app (tApp a t)) eqn:da.
    destruct (expanded_head_viewc t0) => //.
    * move: IH => [] hl [] ha [] ht /andP[] etafix /and3P[] etab etal etat.
      clear H0.
      rewrite ha in H.
      eapply eval_stuck_fix_eq in H as [args' [Hargs' [[]|]]]. solve_discr.
      forward IHeval1 => //.
      rewrite ha. eapply isEtaExp_FixApp => //. 
      forward IHeval2 => //.
      now econstructor. auto.
    * move: IH => /and4P [] ht0 hl ha ht.
      forward IHeval1 => //.
      forward IHeval2 => //.
      econstructor; eauto.
  - clear H0.
    move/(isEtaExp_tApp_eval wguard H) => IH.
    forward IH by (intros; intro; solve_discr).
    forward IH by (intros; intro; solve_discr).
    destruct (decompose_app (tApp f0 a)) eqn:da.
    destruct (expanded_head_viewc t) => //.
    * move: IH => [] hl [] ha [] ht /andP[] etafix /and3P[] etab etal etat.
      rewrite ha in H.
      eapply eval_stuck_fix_eq in H as [args' [Hargs' [[]|]]]. solve_discr.
      forward_keep IHeval1 => //.
      rewrite ha. eapply isEtaExp_FixApp => //. 
      forward IHeval2 => //.
      forward IHeval3. eapply etaExp_csubst; tea. eapply eval_etaexp; tea.
      eapply eval_etaexp in IHeval1; tea. simp_eta in IHeval1. exact IHeval1.
      now econstructor. auto.
    * move: IH => /and4P [] ht0 hl ha ht.
      forward_keep IHeval1 => //.
      forward IHeval2 => //.
      forward IHeval3. eapply etaExp_csubst; tea. eapply eval_etaexp; tea.
      eapply eval_etaexp in IHeval1; tea. simp_eta in IHeval1. exact IHeval1.
      econstructor; eauto.
   
  - intros Hexp; simp_eta in Hexp. rtoProp. econstructor. eauto.
    forward_keep IHeval1 => //.
    forward IHeval2 => //.
    eapply etaExp_csubst; tea.
    eapply eval_etaexp in IHeval1; tea. 
  - simp_eta. move=> /andP[] etad etabrs.
    forward IHeval1 => //.
    move: (eval_etaexp etaΣ wfΣ IHeval1 etad).
    rewrite isEtaExp_Constructor => /andP[] etac etaargs.
    forward_keep IHeval2 => //.
    eapply isEtaExp_iota_red'; eauto.
    eapply forallb_nth_error in etabrs; tea. erewrite H1 in etabrs.
    cbn in etabrs. now rewrite -H2 app_nil_r skipn_length in etabrs.
    econstructor; tea.
    
  - simp_eta. move=> /andP[] etad etabrs.
    forward IHeval1 => //.
    eapply eval_iota_sing => //. tea.
    eapply IHeval2.
    eapply (isEtaExp_substl _ (repeat 0 #|n|)); trea.
    now len. rewrite forallb_repeat //.
    rewrite H2 /= in etabrs. now move/andP: etabrs.

  - cbn -[isEtaExp] in *.
    intros he. generalize he.
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc.  
    * move=> [] hl [] hf [] ha heta.
      clear H0.
      rewrite hf in H. eapply eval_construct in H as [? []]; solve_discr.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      set (H' := H); assert (eval_depth H' = eval_depth H) by reflexivity.
      clearbody H'. move: H' H4. rewrite {1 2}hf. intros H'.
      pose proof H' as Hfix.
      rewrite -[tApp _ _](mkApps_app _ _ [av]) in IHeval3.
      forward_keep IHeval2.
      { rewrite ha. now eapply forallb_last. }
      unshelve epose proof (eval_mkApps_tFix_inv_size _ _ _ _ _ _ H') => //; auto.
      intros hev.
      destruct X as [[args' [hargs heq]]|].
      { solve_discr. noconf H5.
        forward IHeval3.
        { rewrite app_nil_r in etab. eapply isEtaExp_cunfold_fix in etab. 2:tea.
          eapply (isEtaExp_mkApps_intro _ [] _ _) => //. tea.
          eapply All_app_inv.
          2:eapply All_tip.1, eval_etaexp; tea.
          eapply forallb_remove_last in isel.
          eapply All_eval_etaexp in isel; tea. solve_all.
          eapply All2_impl; tea. cbn. now intros ? ? []. }
        destruct (eval_mkApps_inv_size IHeval3) as [f'' [args'' [evf' [evs evargs' [evres ressize]]]]].
        rewrite -[tApp _ _](mkApps_app _ _ [a]). 
        rewrite ha. rewrite -remove_last_last //.
        assert (All2
          (λ a a' : EAst.term, @eval (switch_unguarded_fix fl) Σ a a')
          l (args' ++ [av])).
        { rewrite [l](remove_last_last l a hl). eapply All2_app => //.
          eapply forallb_remove_last, forallb_All in isel.
          eapply All2_All_mix_left in hargs; tea.
          eapply All2_impl; tea.
          { cbn. intros x y [etax []]. eapply (H0 _ _ x0) => //. lia. }
          constructor. 2:constructor. now rewrite -ha. }
        clear evs evargs'. clear ressize. move: X IHeval3.
        generalize (args' ++ [av]) => evargs.
        intros hargs'; depelim hargs' => //.
        cbn. intros ev. eapply eval_mkApps_inv in ev as [f' [evf'' evargs]].
        eapply eval_app_cong_mkApps.
        eapply eval_fix' => //. constructor => //. now rewrite H2. exact e.
        exact evf''. exact hargs'. exact evargs. }
      { destruct s as [n [b [hrm [hunf hn]]]].
        clear H0 hev; rewrite hf in H.
        eapply neval_to_stuck_fix_app in H => //.
        apply isEtaExp_FixApp => //.
        move: hunf. rewrite /cunfold_fix /isEtaExp_fixapp.
        destruct nth_error => //. intros [=]. eapply Nat.ltb_lt. now subst n.
        now eapply forallb_remove_last. }
    * move=> [] hl [] ha [] ht /andP[] hnth.
      now rewrite nth_error_nil /= in hnth.
    * move=> /and4P[] => ht hl hf ha. clear H0.
      now eapply neval_to_stuck_fix_app in H; tea.
      
  - clear H0.
    cbn -[isEtaExp] in *.
    intros he. generalize he.
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc.
    * move=> [] hl [] hf [] ha heta.
      rewrite hf in H. eapply eval_construct in H as [? []]; solve_discr.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      rewrite hf in H.
      elimtype False.
      pose proof H as Hfix.
      eapply eval_stuck_fix_eq in H as [args' [hargs [[hstuck ?]|]]].
      { solve_discr. noconf H.
        move: etal. rewrite /isEtaExp_fixapp.
        unfold isStuckFix' in hstuck. rewrite H2 in hstuck.
        move: H2. rewrite /cunfold_fix.
        destruct nth_error eqn:hnth => //.
        intros [=]. subst narg. rewrite -(All2_length hargs) in hstuck, H3.
        move/Nat.ltb_lt. apply Nat.leb_le in hstuck.
        rewrite remove_last_length' // in hstuck, H3. lia. }
      eapply neval_to_stuck_fix_app in Hfix; tea.
      eapply isEtaExp_FixApp => //.
      now eapply forallb_remove_last. auto.
    * move=> [] hl [] ha [] ht /andP[] hnth.
      now rewrite nth_error_nil /= in hnth.
    * move=> /and4P[] => ht hl hf ha.
      now eapply neval_to_stuck_fix_app in H; tea.
  - cbn in unguarded. congruence.
  - simp_eta => /andP[] etad etabrs.
    forward IHeval1 by tas.
    forward IHeval2.
    { simp_eta. rewrite etabrs andb_true_r.
      eapply eval_etaexp in H0; tea.
      move: H0; rewrite isEtaExp_mkApps // /= => /andP[] etafix etaargs.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_cofix; tea. simp_eta in etafix.
      now rewrite app_nil_r in etafix. solve_all. }
    econstructor; eauto.
  - simp_eta => etad.
    forward IHeval1 by tas.
    forward IHeval2. { simp_eta.
      eapply eval_etaexp in H0; tea.
      move: H0; rewrite isEtaExp_mkApps // /= => /andP[] etafix etaargs.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_cofix; tea. simp_eta in etafix.
      now rewrite app_nil_r in etafix. solve_all. }
    econstructor; eauto.
  - move=> _.
    forward IHeval.
    { eapply isEtaExp_lookup in H; tea.
      now rewrite /isEtaExp_decl /isEtaExp_constant_decl H0 /= in H. }
    econstructor; eauto.
  - simp_eta => etad.
    forward IHeval1 by tas.
    forward IHeval2.
    { eapply eval_etaexp in H; tea.
      move: H; rewrite isEtaExp_mkApps // /= => /andP[] etaapp etaargs.
      rewrite nth_nth_error. destruct nth_error eqn:hnth => //.
      eapply forallb_nth_error in etaargs; tea.
      now erewrite hnth in etaargs. }
    eapply eval_proj; tea.
  - simp_eta => etad.
    forward IHeval by tas.
    eapply eval_proj_prop ; tea. 
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    rewrite (decompose_app_inv da).
    destruct expanded_head_viewc.
    * move=> [] hl [] hf [] ha /andP[] heta etal.
      set (H' := H) ; assert (eval_depth H' = eval_depth H) by reflexivity.
      clearbody H'. move: H' H3. rewrite {1 2}hf. intros H'.
      destruct (eval_mkApps_Construct_size H') as [args' [evc [evcs hargs ->]]].
      intros hevd.
      rewrite (remove_last_last l a hl).
      rewrite -[tApp _ _](mkApps_app _ _ [a']).
      eapply eval_mkApps_Construct. eapply All2_app.
      eapply forallb_remove_last, forallb_All in etal.
      eapply All2_All_mix_left in hargs; tea.
      eapply All2_impl; tea. cbn; intros ? ? [].
      destruct s as [evxy hevxy]. unshelve eapply H0; tea. lia.
      constructor; [|constructor]. rewrite -ha.
      eapply IHeval2. rewrite ha. now eapply forallb_last.
    * move => [hl [hf [ha /andP[] /andP[] etal etab]]] isel.
      forward IHeval2. { rewrite ha. now eapply forallb_last. }
      clear H0.
      rewrite hf in H.
      pose proof H as Hfix.
      eapply eval_stuck_fix_eq in H as [args' [hargs [[hstuck ?]|]]]; auto.
      { subst f'. cbn in H1.
        rewrite !negb_or /= in H1.
        move/andP: H1 => [] /andP[] _.
        rewrite isFixApp_mkApps // wguard //. }
      { cbn in H1.
        rewrite (remove_last_last l a hl) /=.
        rewrite mkApps_app. eapply eval_app_cong.
        rewrite hf in IHeval1. eapply IHeval1.
        rewrite isEtaExp_mkApps // /= i etab /=.
        now eapply forallb_remove_last. cbn.
        move: H1. rewrite !negb_or => /andP[] /andP[] -> isfix -> /=.
        rewrite andb_true_r. rewrite wguard in isfix. now eapply nisFixApp_nisFix.
        now rewrite -ha. }
    * move=> [] hl [] ha [] ht /andP[] hnth.
      now rewrite nth_error_nil /= in hnth.
    * move=> /and4P[] => ht hl hf ha.
      forward IHeval1 by tas.
      forward IHeval2 by tas.
      rewrite -(decompose_app_inv da). eapply eval_app_cong; tea.
      move: H1. rewrite !negb_or => /andP[] /andP[] -> isfix -> /=.
      rewrite andb_true_r. rewrite wguard in isfix. now eapply nisFixApp_nisFix.
  - intros hexp. now eapply eval_atom.
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

Import PCUICAst.

Lemma erases_App (Σ : global_env_ext) Γ f L t :
  erases Σ Γ (tApp f L) t ->
  (t = EAst.tBox × squash (isErasable Σ Γ (tApp f L)))
  \/ exists f' L', t = EAst.tApp f' L' /\
            erases Σ Γ f f' /\
            erases Σ Γ L L'.
Proof.
  intros. generalize_eqs H.
  revert f L.
  inversion H; intros; try congruence; subst.
  - invs H4. right. repeat eexists; eauto.
  - left. split; eauto. now sq.
Qed.

Lemma erases_mkApps_inv (Σ : global_env_ext) Γ f L t :
  Σ;;; Γ |- mkApps f L ⇝ℇ t ->
  (exists L1 L2 L2', L = L1 ++ L2 /\
                erases Σ Γ (mkApps f L1) EAst.tBox /\
                Forall2 (erases Σ Γ) L2 L2' /\
                t = EAst.mkApps EAst.tBox L2'
  )
  \/ exists f' L', t = EAst.mkApps f' L' /\
            erases Σ Γ f f' /\
            Forall2 (erases Σ Γ) L L'.
Proof.
  intros. revert f H ; induction L; cbn in *; intros.
  - right. exists t, []. cbn. repeat split; eauto.
  - eapply IHL in H; eauto.
    destruct H as [ (? & ? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. left. exists (a :: x), x0, x1. repeat split; eauto.
    + subst.
      eapply erases_App in H0 as [ (-> & []) | (? & ? & ? & ? & ?)].
      * left. exists [a], L, x0. cbn. repeat split; eauto. now constructor.
      * subst. right. exists x1, (x2 :: x0). repeat split; eauto.
Qed.

Lemma declared_constructor_arity {cf : checker_flags} {Σ c mdecl idecl cdecl} {wf : wf Σ} :
  PCUICAst.declared_constructor Σ c mdecl idecl cdecl ->
  context_assumptions (cstr_args cdecl) = cstr_arity cdecl.
Proof.
  intros hd.
  destruct (PCUICWeakeningEnvTyp.on_declared_constructor hd) as [[onmind onind] [cu []]].
  now eapply cstr_args_length in o.
Qed.

From MetaCoq.PCUIC Require Import PCUICEtaExpand. 
From MetaCoq.Erasure Require Import EDeps.

Lemma expanded_erases (cf := config.extraction_checker_flags) {Σ : global_env_ext} Σ' Γ Γ' t v :
  wf Σ ->
  Σ ;;; Γ |- t ⇝ℇ v ->
  PCUICEtaExpand.expanded Σ.1 Γ' t ->
  erases_deps Σ Σ' v ->
  EEtaExpandedFix.expanded Σ' Γ' v.
Proof.
  intros wfΣ he exp etaΣ.
  revert Γ v etaΣ he.
  induction exp using PCUICEtaExpand.expanded_ind; cbn.
  all:try solve [intros Γ0 v etaΣ hv; depelim hv; try depelim etaΣ; constructor; solve_all].
  - move=> Γ0 etaΣ v /erases_mkApps_inv; intros [(?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * constructor => //.
      eapply EDeps.erases_deps_mkApps_inv in v as [].
      eapply Forall_All in H2. eapply Forall2_All2 in H5.
      eapply All_app in H2 as []. 
      solve_all.
    * eapply EDeps.erases_deps_mkApps_inv in v as [].
      depelim H4; simp_eta => //.
      + eapply expanded_tRel_app; tea. now rewrite -(Forall2_length H5).
        eapply Forall_All in H2. eapply Forall2_All2 in H5. solve_all.
      + constructor => //. solve_all.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //.
      eapply Forall_All in H1. eapply Forall2_All2 in H4.
      eapply All_app in H1 as []. solve_all.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      specialize (IHexp _ _ H2 H3).
      constructor => //.
      clear -H H3. destruct H3; cbn in *; congruence.
      solve_all.
  - intros Γ0 v etaΣ hv; depelim hv; try constructor. 
    depelim etaΣ.
    eauto.
    depelim etaΣ.
    solve_all. rewrite -b2. len. eapply H7 => //.
    exact a0.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //. 
      eapply Forall_All in H2. eapply Forall2_All2 in H8.
      eapply All_app in H2 as []. solve_all.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      depelim H7; simp_eta => //.
      + eapply All2_nth_error_Some in H4; tea. destruct H4 as [? [? []]]; tea.
        assert (rev_map (fun d1 : def term => S (rarg d1)) mfix = rev_map (fun d1 => S (EAst.rarg d1)) mfix').
        { rewrite !rev_map_spec. f_equal. clear -X. induction X; cbn; auto. destruct r as [eqb eqrar isl isl' e].
          rewrite eqrar IHX //. }
        depelim H6.
        eapply EEtaExpandedFix.expanded_tFix; tea.
        ++ cbn. rewrite -H6. solve_all. apply b0.
          eapply b1 => //. eapply b0.
        ++ solve_all.
        ++ intros hx0. subst x0. depelim H8 => //.
        ++ now rewrite -(Forall2_length H8) -e1.
      + constructor => //; solve_all.
  - intros Γ0 v etaΣ hv. depelim hv. depelim etaΣ.
    constructor => //. rewrite -(All2_length X). solve_all. constructor.
  - intros Γ0 v etaΣ.
    move=> /erases_mkApps_inv; intros [(?&?&?&?&?&?&?)|(?&?&?&?&?)]; subst.
    * eapply erases_deps_mkApps_inv in etaΣ as [].
      constructor => //.
      eapply Forall_All in H2. eapply Forall2_All2 in H5.
      eapply All_app in H2 as []. solve_all.
    * depelim H4; simp_eta => //.
      + eapply erases_deps_mkApps_inv in etaΣ as [].
        depelim H4.
        destruct cdecl'.
        eapply EEtaExpandedFix.expanded_tConstruct_app; tea.
        ++ cbn. rewrite -(Forall2_length H5).
          destruct (PCUICGlobalEnv.declared_constructor_inj H H4) as [? []]. subst idecl0 mind cdecl0.    
          rewrite (declared_constructor_arity H) in H0.
          destruct H7. rewrite -H10.
          destruct H8 as [? _].
          eapply Forall2_nth_error_left in H8. 2:apply H.
          destruct H8 as [[i' n'] [hnth heq]].
          cbn in hnth.
          rewrite (proj2 H6) in hnth. noconf hnth.
          destruct heq. congruence.
        ++ solve_all.
        + constructor => //.
          eapply erases_deps_mkApps_inv in etaΣ as [].
          solve_all.
Qed.
