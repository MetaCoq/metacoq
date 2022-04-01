(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils Kernames BasicAst EnvMap.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EWcbvEval EGlobalEnv
   ECSubst EInduction EWcbvEvalInd EEtaExpanded.

Set Asymmetric Patterns.
From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.

#[export]
Hint Constructors eval : core.

Definition atomic_term (t : term) :=
  match t with
  | tBox | tConstruct _ _ | tConst _ | tRel _ | tVar _ => true
  | _ => false
  end.

Section OnSubterm.

  Inductive on_subterms (Q : nat -> term -> Type) (n : nat) : term -> Type :=
  | on_atom t : atomic_term t -> on_subterms Q n t
  | on_evar k l : All (Q n) l -> on_subterms Q n (tEvar k l)
  | on_lambda na t : Q (S n) t -> on_subterms Q n (tLambda na t)
  | on_letin na t u : Q n t -> Q (S n) u -> on_subterms Q n (tLetIn na t u)
  | on_app f u : Q n f -> Q n u -> on_subterms Q n (tApp f u)
  | on_case ci discr brs : Q n discr -> 
    All (fun br => Q (#|br.1| + n) br.2) brs -> on_subterms Q n (tCase ci discr brs)
  | on_proj p c : Q n c -> on_subterms Q n (tProj p c)
  | on_fix mfix idx : All (fun d => Q (#|mfix| + n) d.(dbody)) mfix -> on_subterms Q n (tFix mfix idx)
  | on_cofix mfix idx : All (fun d => Q (#|mfix| + n) d.(dbody)) mfix -> on_subterms Q n (tCoFix mfix idx).
  Derive Signature for on_subterms.
End OnSubterm.

Class Qdummy (Q : nat -> term -> Type) := qdummy : forall n, Q n tDummy.
#[export] Hint Mode Qdummy ! : typeclass_instances.

Class Qpres (Q : nat -> term -> Type) := qpres : forall n t, Q n t -> on_subterms Q n t.
#[export] Hint Mode Qpres ! : typeclass_instances.
Class Qapp (Q : nat -> term -> Type) := qapp : forall n f args, Q n (mkApps f args) <~> Q n f × All (Q n) args.
#[export] Hint Mode Qapp ! : typeclass_instances.
Class Qcase (Q : nat -> term -> Type) := qcase : forall n ci discr brs, Q n (tCase ci discr brs) <~> Q n discr × All (fun br => Q (#|br.1| + n) br.2) brs.
#[export] Hint Mode Qcase ! : typeclass_instances.
Class Qproj (Q : nat -> term -> Type) := qproj : forall n p discr, Q n (tProj p discr) <~> Q n discr.
#[export] Hint Mode Qproj ! : typeclass_instances.
Class Qfix (Q : nat -> term -> Type) := qfix : forall n mfix idx, Q n (tFix mfix idx) <~>  All (fun d => Q (#|mfix| + n) d.(dbody)) mfix.
#[export] Hint Mode Qfix ! : typeclass_instances.
Class Qcofix (Q : nat -> term -> Type) := qcofix : forall n mfix idx, Q n (tCoFix mfix idx) <~>  All (fun d => Q (#|mfix| + n) d.(dbody)) mfix.
#[export] Hint Mode Qcofix ! : typeclass_instances.
Class Qsubst (Q : nat -> term -> Type) := qsubst : forall t l, Q (#|l|) t -> All (Q 0) l -> Q 0 (substl l t).
#[export] Hint Mode Qsubst ! : typeclass_instances.
Class Qfixs (Q : nat -> term -> Type) := qfixs : forall mfix idx, Q 0 (tFix mfix idx) -> 
    forall args fn, cunfold_fix mfix idx = Some (args, fn) ->
    Q 0 fn.
#[export] Hint Mode Qfixs ! : typeclass_instances.
Class Qcofixs (Q : nat -> term -> Type) := qcofixs : forall mfix idx, Q 0 (tCoFix mfix idx) -> 
  forall args fn, cunfold_cofix mfix idx = Some (args, fn) ->
  Q 0 fn.
#[export] Hint Mode Qcofixs ! : typeclass_instances.
      
Lemma Qfix_subst mfix Q : Qfix Q -> All (λ d : def term, Q (#|mfix| + 0) (dbody d)) mfix -> All (Q 0) (fix_subst mfix).
Proof.
  intros qfix; unfold fix_subst.
  generalize #|mfix| at 2. intros n hfix.
  induction n; constructor; auto.
  now eapply qfix.
Qed.

Lemma Qcofix_subst mfix Q : Qcofix Q -> All (λ d : def term, Q (#|mfix| + 0) (dbody d)) mfix -> All (Q 0) (cofix_subst mfix).
Proof.
  intros qfix; unfold cofix_subst.
  generalize #|mfix| at 2. intros n hfix.
  induction n; constructor; auto.
  now eapply qfix.
Qed.

#[export] Instance Qsubst_Qfixs Q : Qpres Q -> Qfix Q -> Qsubst Q -> Qfixs Q.
Proof.
  move=> qpres qfix; rewrite /Qsubst /Qfixs.
  intros Hs mfix idx hfix args fn.
  rewrite /cunfold_fix.
  eapply qpres in hfix. depelim hfix => //.
  destruct nth_error eqn:hnth => //.
  eapply nth_error_all in hnth; tea. cbn in hnth.
  rewrite Nat.add_0_r in hnth.
  intros [= <-]. subst fn.
  eapply Hs. rewrite fix_subst_length //.
  now apply Qfix_subst.
Qed.

#[export] Instance Qsubst_Qcofixs Q : Qpres Q -> Qcofix Q -> Qsubst Q -> Qcofixs Q.
Proof.
  move=> qpres qfix; rewrite /Qsubst /Qcofixs.
  intros Hs mfix idx hfix args fn.
  rewrite /cunfold_cofix.
  eapply qpres in hfix. depelim hfix => //.
  destruct nth_error eqn:hnth => //.
  eapply nth_error_all in hnth; tea. cbn in hnth.
  rewrite Nat.add_0_r in hnth.
  intros [= <-]. subst fn.
  eapply Hs. rewrite cofix_subst_length //.
  now apply Qcofix_subst.
Qed.

Class Qconst Σ (Q : nat -> term -> Type) := qconst :
  ∀ kn decl, declared_constant Σ kn decl → 
    match cst_body decl with
    | None => unit
    | Some b => Q 0 b
    end.
#[export] Hint Mode Qconst - ! : typeclass_instances.

Definition isConstructApp c := isConstruct (decompose_app c).1.

Class Qpreserves (Q : nat -> term -> Type) Σ :=
  { qpres_qpres :> Qpres Q;
    qpres_qcons :> Qconst Σ Q;
    qpres_qapp :> Qapp Q;
    qpres_qcase :> Qcase Q;
    qpres_qproj :> Qproj Q;
    qpres_qsubst :> Qsubst Q;
    qpres_qfix :> Qfix Q;
    qpres_qcofix :> Qcofix Q;
    qpres_qdummy :> Qdummy Q }.

Lemma eval_preserve_mkApps_ind :
∀ (wfl : WcbvFlags) (Σ : global_declarations) 
  (P' : term → term → Type)
  (Q : nat -> term -> Type)
  {Qpres : Qpreserves Q Σ}
  (P := (fun x y => [× P' x y, Q 0 x, Q 0 y, isEtaExp Σ x & isEtaExp Σ y])%type)
  (HPQ : ∀ t u, eval Σ t u -> Q 0 t -> P' t u -> Q 0 u),
  isEtaExp_env Σ ->
  wf_glob Σ ->
  (∀ (a t t' : term),
	 eval Σ a tBox ->
     P a tBox →
     eval Σ t t' → P t t' → P' (tApp a t) tBox) → 
  (∀ (f0 : term) (na : name) (b a a' res : term),
      eval Σ f0 (tLambda na b) → 
      P f0 (tLambda na b)
         → eval Σ a a'
           → P a a'
             → eval Σ (ECSubst.csubst a' 0 b) res
          → P (ECSubst.csubst a' 0 b) res → P' (tApp f0 a) res)
    → (∀ (na : name) (b0 b0' b1 res : term),
         eval Σ b0 b0'
         → P b0 b0'
         -> isEtaExp Σ b1
           → eval Σ (ECSubst.csubst b0' 0 b1) res
             → P (ECSubst.csubst b0' 0 b1) res → 
             P' (tLetIn na b0 b1) res)
      → (∀ (ind : inductive) (pars : nat) (discr : term) 
           (c : nat) (args : list term) (brs : 
                                              list 
                                                (list name × term)) 
           (br : list name × term) (res : term),
           forallb (λ x : list name × term, isEtaExp Σ x.2) brs ->
           eval Σ discr (mkApps (tConstruct ind c) args)
           → P discr (mkApps (tConstruct ind c) args)
             → inductive_isprop_and_pars Σ ind = Some (false, pars)
               → nth_error brs c = Some br
                 → #|skipn pars args| = #|br.1|
                   → eval Σ (iota_red pars args br) res
                     → P (iota_red pars args br) res
                       → P' (tCase (ind, pars) discr brs) res)
        → (∀ (ind : inductive) (pars : nat) (discr : term) 
             (brs : list (list name × term)) 
             (n : list name) (f3 res : term),
             with_prop_case
             → eval Σ discr tBox
               → P discr tBox
                 → inductive_isprop_and_pars Σ ind = Some (true, pars)
                   → brs = [(n, f3)]
                   -> forallb (isEtaExp Σ ∘ snd) brs
                     → eval Σ (ECSubst.substl (repeat tBox #|n|) f3)
                         res
                       → P (ECSubst.substl (repeat tBox #|n|) f3) res
                         → P' (tCase (ind, pars) discr brs) res)
          → (∀ (f4 : term) (mfix : mfixpoint term) 
               (idx : nat) (argsv : list term) 
               (a av fn res : term),
               with_guarded_fix ->
               eval Σ f4 (mkApps (tFix mfix idx) argsv)
               → P f4 (mkApps (tFix mfix idx) argsv)
                 → eval Σ a av
                   → P a av
                     → cunfold_fix mfix idx = Some (#|argsv|, fn)
                     -> isEtaExp Σ fn
                      → eval Σ (tApp (mkApps fn argsv) av) res
                         → P (tApp (mkApps fn argsv) av) res
                           → P' (tApp f4 a) res)
            → (∀ (f5 : term) (mfix : mfixpoint term) 
                 (idx : nat) (argsv : list term) 
                 (a av : term) (narg : nat) (fn : term),
                 with_guarded_fix ->
                 eval Σ f5 (mkApps (tFix mfix idx) argsv)
                 → P f5 (mkApps (tFix mfix idx) argsv)
                   → eval Σ a av
                     → P a av
                       → cunfold_fix mfix idx = Some (narg, fn)
                         → #|argsv| < narg
                         -> isEtaExp Σ (tApp (mkApps (tFix mfix idx) argsv) av)
                           → P' (tApp f5 a)
                               (tApp
                                  (mkApps (tFix mfix idx) argsv) av))
            → (∀ (f5 : term) (mfix : mfixpoint term) 
            (idx : nat) (a av : term) (narg : nat) (fn : term) res,
            with_guarded_fix = false ->
            eval Σ f5 (tFix mfix idx)
            → P f5 (tFix mfix idx)
              → cunfold_fix mfix idx = Some (narg, fn)
              -> isEtaExp Σ fn
              -> eval Σ a av -> P a av
              → eval Σ (tApp fn av) res   
              → P (tApp fn av) res
              -> isEtaExp Σ (tApp f5 a)
              → P' (tApp f5 a) res) → 
              
              (∀ (ip : inductive × nat) (mfix : mfixpoint term) 
                   (idx : nat) (args : list term) 
                   (narg : nat) discr (fn : term) (brs : 
                                                 list 
                                                 (list name × term)) 
                   (res : term),
                   cunfold_cofix mfix idx = Some (narg, fn)
                   -> isEtaExp Σ fn
                   -> forallb (isEtaExp Σ) args
                   -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                   -> P discr (mkApps (tCoFix mfix idx) args)
                   -> forallb (isEtaExp Σ ∘ snd) brs
                   → eval Σ (tCase ip (mkApps fn args) brs) res
                     → P (tCase ip (mkApps fn args) brs) res
                       → P'
                           (tCase ip discr brs)
                           res)
                → (∀ (p : projection) (mfix : mfixpoint term) 
                     (idx : nat) (args : list term) 
                     (narg : nat) discr (fn res : term),
                     cunfold_cofix mfix idx = Some (narg, fn)
                     -> isEtaExp Σ fn
                     -> forallb (isEtaExp Σ) args
                     -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                     -> P discr (mkApps (tCoFix mfix idx) args)
                     → eval Σ (tProj p (mkApps fn args)) res
                       → P (tProj p (mkApps fn args)) res
                         → P'
                             (tProj p discr) res)
                  → (∀ (c : kername) (decl : constant_body) 
                       (body : term),
                       declared_constant Σ c decl
                       → ∀ res : term,
                           cst_body decl = Some body
                           → eval Σ body res
                             → P body res → P' (tConst c) res)
                    → (∀ (i : inductive) (pars arg : nat) 
                         (discr : term) (args : list term) 
                         (res : term),
                         eval Σ discr
                           (mkApps (tConstruct i 0) args)
                         → P discr (mkApps (tConstruct i 0) args)
                           → inductive_isprop_and_pars Σ i = Some (false, pars)
                             → eval Σ (nth (pars + arg) args tDummy) res
                               → P (nth (pars + arg) args tDummy) res
                                 → P' (tProj (i, pars, arg) discr) res)
                      → (∀ (i : inductive) (pars arg : nat) 
                           (discr : term),
                           with_prop_case
                           → eval Σ discr tBox
                             → P discr tBox
                               → inductive_isprop_and_pars Σ i = Some (true, pars)
                                 → P' (tProj (i, pars, arg) discr)
                                     tBox) →
  (∀ (f11 f' : term) a a',
     forall (ev : eval Σ f11 f'), P f11 f' ->  
     (forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> Q 0 t -> isEtaExp Σ t -> P t u) →
     ~~ isConstructApp f11 ->
     ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f') → 
     eval Σ a a' → P a a' → 
     isEtaExp Σ (tApp f' a') ->
     P' (tApp f11 a) (tApp f' a')) → 
  (∀ ind i args args',
    All2 (eval Σ) args args' -> 
    isEtaExp_app Σ ind i #|args| ->
    Q 0 (mkApps (tConstruct ind i) args) -> Q 0 (mkApps (tConstruct ind i) args') ->
    All2 P args args' ->
    P' (mkApps (tConstruct ind i) args) (mkApps (tConstruct ind i) args')) → 
  (∀ t : term, atom t → Q 0 t -> isEtaExp Σ t -> P' t t) ->
  ∀ (t t0 : term), Q 0 t -> isEtaExp Σ t -> eval Σ t t0 → P' t t0.
Proof.
  intros * Qpres P P'Q etaΣ wfΣ.
  assert (qfixs: Qfixs Q) by tc.
  assert (qcofixs: Qcofixs Q) by tc.
  intros.
  enough (P' t t0 × isEtaExp Σ t0). apply X16.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2.π2))).
  set(foo := existT _ t (existT _ t0 (existT _ X15 H0)) :  { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  move: H.
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H0 with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  rename X15 into qt.
  clear t t0 qt H0.
  intros (t & t0 & qt & ev). 
  intros IH.
  set (IH' t t0 q H := IH (t; t0; q; H)). clearbody IH'; clear IH; rename IH' into IH.
  Opaque isEtaExp.
  cbn in IH. unfold MR in IH; cbn in IH. cbn.
  Ltac ih := 
    match goal with 
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply IH; tea; cbn; try lia
    end.
  Ltac iheta e := 
    match goal with 
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply (IH _ _ e); tea; cbn; try lia
    end.
  Ltac hp' P'Q := intros [hp' heta]; repeat split => //; try eapply P'Q; tea.
  assert (and_assum : forall x y, (P' x y × isEtaExp Σ y) -> 
    ((P' x y × isEtaExp Σ y) -> Q 0 x × Q 0 y × isEtaExp Σ x) ->
    P x y).    
  { intuition auto. red. intuition auto. }
  Ltac ih' P'Q :=
    match goal with
    | [ H : _, IH : forall x y, ?Q 0 x -> _ |- _ ] =>
      eapply H; tea; (apply and_assum; [ih|hp' P'Q])
    end.
  destruct ev.
  1-14:eapply qpres in qt; depelim qt => //.  
  all:try solve [ih' P'Q].
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      clear IH; rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat.
      split. eapply X; tea; (apply and_assum; [ih|hp' P'Q]).
      iheta q.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      clear IH; rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat. 
      assert (ql : Q 0 (tLambda na b)).
      { eapply P'Q; tea. ih. }
       assert (qs: Q 0 (csubst a' 0 b)).
      { eapply qpres in ql. depelim ql => //.
        eapply (qsubst b [a']) in q1. now cbn in q1.
        repeat constructor.
        eapply P'Q; tea; ih. }
      assert (isEtaExp Σ (csubst a' 0 b)).
      { eapply etaExp_csubst; tea. cbn in IH. specialize (IH _ _ q0 ev2). apply IH; [lia|auto].
        specialize (IH _ _ q ev1). forward IH by cbn; lia.
        forward IH by auto. destruct IH as [_ eta]. now simp_eta in eta. }
      split. eapply X0; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
      iheta qs.
  - simp_eta. move=> /andP[etab0 etab1].
    assert (qs : Q 0 (csubst b0' 0 b1)).
    { eapply (qsubst b1 [b0']) in q0. now cbn in q0.
      repeat constructor.
      eapply P'Q; tea; ih. }
    assert (isEtaExp Σ (csubst b0' 0 b1)).
    { eapply etaExp_csubst; tea. iheta q. }
    split; [eapply X1; tea|]. 1-2:(apply and_assum; [ih|hp' P'Q]).
    iheta qs.
  - simp_eta. move=> /andP[etad etabrs].
    assert (isEtaExp Σ (iota_red pars args br)).
    { eapply isEtaExp_iota_red.
      assert (isEtaExp Σ (mkApps (tConstruct ind c) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in H.
      now move/andP: H => [].
      now clear IH; eapply nth_error_forallb in e0; tea. }
    assert (Q 0 (iota_red pars args br)).
    { unfold iota_red.
      eapply nth_error_all in a; tea. cbn in a.
      rewrite -e1 in a.
      rewrite -(List.rev_length (skipn pars args)) in a.
      rewrite Nat.add_0_r in a.
      eapply (qsubst _ (List.rev (skipn pars args))) in a.
      2:{ eapply All_rev, All_skipn. 
        assert (Q 0 (mkApps (tConstruct ind c) args)).
        eapply P'Q; tea; ih.
        eapply qapp in X15; tea. eapply X15. }
      exact a. }
    split. eapply X2; tea. 1-2:(apply and_assum; [ih|hp' P'Q]).
    iheta X15.
  - simp_eta; move=> /andP[etad etabrs].
    assert (isEtaExp Σ (substl (repeat tBox #|n|) f)).
    { eapply isEtaExp_substl => //. rewrite forallb_repeat //.
      rewrite e0 /= in etabrs. now move/andP: etabrs. }
    assert (Q 0 (substl (repeat tBox #|n|) f)).
    { subst brs. eapply All_tip in a. cbn in a.
      rewrite -(repeat_length tBox #|n|) Nat.add_0_r in a.
      eapply (qsubst _ (repeat tBox #|n|)) in a => //.
      eapply All_repeat. eapply P'Q; tea; ih. }
   split. eapply X3; tea; (apply and_assum; [ih|hp' P'Q]).
   iheta X15.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      clear IH; rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat. 
      assert (qa : Q 0 (tApp (mkApps fn argsv) av)).
      { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
        eapply qapp in ev1' as [hfix qargs] => //.
        rewrite -[tApp _ _](mkApps_app _ _ [av]).
        eapply (qapp _ _ _).2.
        split => //.
        eapply (qfixs mfix idx) in hfix; tea.
        eapply All_app_inv => //. eapply All_tip.1.
        eapply P'Q; tea; ih. clear ev1'; ih. }
      assert (etaapp : isEtaExp Σ fn × isEtaExp Σ (tApp (mkApps fn argsv) av)).
      { rewrite -[tApp _ _](mkApps_app _ _ [av]).
        assert (hfix : isEtaExp Σ (mkApps (tFix mfix idx) argsv)) by iheta q.
        rewrite isEtaExp_mkApps_napp /= // in hfix.
        move/andP: hfix => [hfix hargs].
        apply EWcbvEvalInd.and_assum.
        eapply isEtaExp_cunfold_fix. now simp_eta in hfix. exact e.
        intros hfn.
        eapply isEtaExp_mkApps_intro => //.        
        eapply All_app_inv. now eapply forallb_All in hargs. eapply (fst All_tip).
        iheta q0. }
      destruct etaapp as [etafn etafnapp].
      split. eapply X4; tea; (apply and_assum; [ih|hp' P'Q]).
      iheta qa.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      clear IH; rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat.
      assert (isEtaExp Σ (tApp (mkApps (tFix mfix idx) argsv) av)).
      { rewrite -[tApp _ _](mkApps_app _ _ [av]).
        rewrite isEtaExp_mkApps_napp // /=.
        assert (isEtaExp Σ (mkApps (tFix mfix idx) argsv)) by iheta q.
        assert (isEtaExp Σ av) by iheta q0.
        rewrite isEtaExp_mkApps_napp // /= in H.
        move/andP: H => [] -> /=.
        rewrite forallb_app /= H0 => -> /= //. }
      split => //. eapply X5; tea; (apply and_assum; [ih|hp' P'Q]).
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      clear IH; rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat. 
      assert (qav : Q 0 av).
      { eapply P'Q; tea; ih. }
      assert (qa : Q 0 (tApp fn av)).
      { pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:clear ev1'; ih.
        eapply qfixs in ev1'. cbn in IH. eapply ev1' in e.
        eapply (qapp _ _ [av]); split => //. now eapply All_tip.1. }
      assert (etafn : isEtaExp Σ fn).
      { assert (hfix : isEtaExp Σ (tFix mfix idx)) by iheta q.
        eapply isEtaExp_cunfold_fix. now simp_eta in hfix. exact e. }
      assert (etaav : isEtaExp Σ av).
      { iheta q0. }
      assert (etaapp : isEtaExp Σ (tApp fn av)).
      { change (isEtaExp Σ (mkApps fn [av])).
        eapply isEtaExp_mkApps_intro => //.
        now eapply All_tip.1. }
      split. eapply X6; tea. 1-3:(apply and_assum; [ih|hp' P'Q]).
      rewrite (decompose_app_inv da). eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs.
      iheta qa.
  - simp_eta. move=> /andP[etad etabrs].
    assert (qa : Q 0 (tCase ip (mkApps fn args) brs)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix qargs] => //.
      eapply (qcase _ _ _ _).2. split => //.
      eapply qapp; split => //.
      eapply (qcofixs mfix idx) in hfix; tea. 
      clear ev1'; ih. }
    assert (etafn : isEtaExp Σ fn && forallb (isEtaExp Σ) args).
    { assert (hfix : isEtaExp Σ (mkApps (tCoFix mfix idx) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in hfix.
      move/andP: hfix => [hfix hargs].
      apply/andP; split => //.
      eapply isEtaExp_cunfold_cofix. now simp_eta in hfix. exact e. }
    move/andP: etafn => [] etaf etaargs.
    assert (etac : isEtaExp Σ (tCase ip (mkApps fn args) brs)).
    { simp_eta. rewrite etabrs andb_true_r.
      eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs. }
    split. eapply X7; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta qa.
  - simp_eta. move=> etad.
    cbn in IH.
    assert (qa : Q 0 (tProj p (mkApps fn args))).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [hfix ?].
      eapply qproj. eapply qapp. split => //.
      eapply (qcofixs mfix idx) in hfix; tea.
      clear ev1'; ih. }
    assert (etafn : isEtaExp Σ fn && forallb (isEtaExp Σ) args).
    { assert (hfix : isEtaExp Σ (mkApps (tCoFix mfix idx) args)) by iheta q.
      rewrite isEtaExp_mkApps_napp /= // in hfix.
      move/andP: hfix => [hfix hargs].
      apply/andP; split => //.
      eapply isEtaExp_cunfold_cofix. now simp_eta in hfix. exact e. }
    move/andP: etafn => [] etaf etaargs.
    assert (etaa : isEtaExp Σ (tProj p (mkApps fn args))).
    { simp_eta.
      eapply isEtaExp_mkApps_intro => //.
      now eapply forallb_All in etaargs. }
    split. eapply X8; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta qa.
  - move => _.
    assert (Q 0 body).
    { cbn in IH; eapply (qconst (Q:=Q)) in isdecl. now rewrite e in isdecl. }
    assert (isEtaExp Σ body).
    { eapply isEtaExp_lookup in etaΣ as etad; tea.
      unfold isEtaExp_decl, isEtaExp_constant_decl in etad.
      now rewrite e /= in etad. }
    split. eapply X9; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta X15.
  - simp_eta => etadiscr.
    assert (Q 0 (nth (pars + arg) args tDummy)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply qapp in ev1' as [_ qargs].
      { clear -Qpres qargs. generalize (pars+arg).
        induction args; cbn.
        destruct n; apply qdummy.
        depelim qargs. intros [] => //. now eapply IHargs. }
      clear ev1'; ih. }
    assert (isEtaExp Σ (nth (pars + arg) args tDummy)).
    { assert (isEtaExp Σ (mkApps (tConstruct i 0) args)) by iheta q.
      move: H; simp_eta.
      rewrite isEtaExp_mkApps_napp // /=.
      move=> /andP[] etaapp etaargs.
      rewrite nth_nth_error. destruct nth_error eqn:hnth.
      eapply nth_error_forallb in etaargs; tea.
      unfold tDummy. now simp_eta. }
    split. eapply X10; tea; (apply and_assum; [ih|hp' P'Q]).
    iheta X15.
  - simp_eta => etadiscr.
    split. unshelve eapply X11; tea; try (intros; apply and_assum; [ih|hp' P'Q]).
    now idtac.
  - move/isEtaExp_tApp.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      assert (eval_depth ev1 = eval_depth ev1) by reflexivity.
      set (ev1' := ev1). change ev1 with ev1' in H at 1. clearbody ev1'. move: H.
      subst f.
      pose proof (eval_construct_size ev1') as [ex []]. subst f'.
      cbn in IH. intros eq.
      assert (All2 (λ x y : term, ∑ ev' : eval Σ x y, eval_depth ev' < S (Nat.max (eval_depth ev1) (eval_depth ev2)))
        (remove_last args ++ [a]) (ex ++ [a'])).
      { eapply All2_app. eapply All2_impl; tea; cbn. intros ?? []. exists x0. lia.
        constructor; [|constructor]. exists ev2. lia. }
      assert (All (Q 0) (remove_last args ++ [a])).
      { eapply All_app_inv. eapply qapp in q as []; auto.
        now eapply All_tip.1. }
      assert (All (isEtaExp Σ) (remove_last args ++ [a])).
      { rewrite ht -(remove_last_last args a argsn). now eapply forallb_All. }
      eapply All2_All_mix_left in X15; tea.
      assert (All2 (fun x y => P' x y × isEtaExp Σ y) (remove_last args ++ [a]) (ex ++ [a'])).
      { clear X17. eapply All2_All_mix_left in X15; tea.
        eapply All2_impl; tea. cbn. intros ? ? [? [? [ev ?]]].
        eapply (IH _ _ q1 ev). lia. auto. }
      rewrite (remove_last_last args a argsn) in etaargs.
      rewrite -[tApp _ _](mkApps_app _ _ [a]).
      rewrite -[tApp _ _](mkApps_app _ _ [a']).
      assert (All (fun x => Q 0 x × isEtaExp Σ x) (ex ++ [a'])).
      { eapply All2_mix in X15; tea. cbn in X15.
        eapply All2_All_mix_left in X15. 2:exact X16.
        eapply All2_All_right; tea; cbn.
        intros ? ? [? [? [? []]]]. split. eapply P'Q; tea. apply p. apply p. }
      split. 
      eapply (X13 ind n).
      + eapply All2_app. eapply All2_impl; tea. cbn. now intros ? ? [].
        constructor; [|constructor]. apply ev2.
      + rewrite ht. rewrite -remove_last_last //.
      + eapply qapp in q as []; auto.
        eapply qapp. split => //.
      + eapply qapp in q as []. eapply qapp; auto. split => //.
        eapply All_impl; tea; cbn; intuition auto.
      + eapply All2_All_mix_left in X18; [|exact X16].
        eapply All2_All_mix_right in X18; [|exact X19].
        eapply All2_All_mix_left in X18; [|exact X17].
        eapply All2_impl; tea; cbn.
        intros x y [? [[] ?]].
        red. intuition auto.
      + rewrite isEtaExp_Constructor.
        apply/andP. split. rewrite -(All2_length X18).
        rewrite ht -remove_last_last //.
        eapply All_forallb. eapply All_impl; tea. cbn; intuition auto.
    * move=> /and4P [] etat0 etaargs etaa etat. 
      split. eapply (X12 _ _ _ _ ev1); tea. 
      1,4:(apply and_assum; [ih|hp' P'Q]).
      intros. apply and_assum; [ih|hp' P'Q].
      pose proof (decompose_app_inv da). clear cv.
      apply PCUICNormal.negb_is_true => iscapp.
      cbn in da. eapply (f_equal fst) in da. 
      rewrite Prelim.fst_decompose_app_rec in da. cbn in *.
      unfold isConstructApp in iscapp. rewrite da in iscapp. 
      destruct t => //.
      eapply (isEtaExp_mkApps_intro _ _ [a']) => //.
      iheta q.
      eapply All_tip.1. iheta q0.
      eapply (isEtaExp_mkApps_intro _ _ [a']) => //. iheta q.
      eapply All_tip.1. iheta q0.
  - intros ise. split => //. eapply X14; tea.
Qed.

Lemma All_True {A} l : All (fun x : A => True) l.
Proof.
  induction l; intuition auto.
Qed.

#[export] Instance Qpreserves_True Σ : Qpreserves (fun _ _ => True) Σ.
Proof.
  split; intros; red; intros; try split; intuition auto.
  { destruct t; try solve [constructor; auto; auto using All_True]. }
  { destruct cst_body => //. }
  all:apply All_True.
Qed.

Ltac destruct_nary_times :=
  match goal with 
  | [ H : _ × _ |- _ ] => destruct H
  | [ H : [× _, _ & _] |- _ ] => destruct H 
  | [ H : [× _, _, _ & _] |- _ ] => destruct H 
  | [ H : [× _, _, _, _ & _] |- _ ] => destruct H 
  end.

Lemma eval_etaexp {fl : WcbvFlags} {Σ a a'} : 
  isEtaExp_env Σ ->
  wf_glob Σ ->
  eval Σ a a' -> isEtaExp Σ a -> isEtaExp Σ a'.
Proof.
  intros etaΣ wfΣ ev eta.
  generalize I. intros q. revert a a' q eta ev.
  apply (eval_preserve_mkApps_ind fl Σ (fun _ x => isEtaExp Σ x) (fun _ _ => True)) => //.
  all:intros; repeat destruct_nary_times.
  all:intuition auto.
  - rewrite isEtaExp_Constructor => //.
    rewrite -(All2_length X0) H.
    cbn; eapply All_forallb. eapply All2_All_right; tea.
    cbn. intros x y []; auto.
Qed.
