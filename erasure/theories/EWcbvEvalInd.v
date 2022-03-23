(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils Kernames BasicAst EnvMap.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EWcbvEval ETyping ECSubst EInduction.

Set Asymmetric Patterns.
From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.

#[global]
Hint Constructors eval : core.


Definition and_assum {A B : Type} (f : A) (f' : A -> B) : A × B :=
  (f, f' f).


Definition atomic_term (t : term) :=
  match t with
  | tBox | tConstruct _ _ | tConst _ | tRel _ | tVar _ => true
  | _ => false
  end.
  
Lemma All_tip {A} {P : A -> Type} {a : A} : P a <~> All P [a].
Proof. split; intros. repeat constructor; auto. now depelim X. Qed.

Lemma eval_construct_size  {fl : WcbvFlags} [Σ kn c args e] : 
  forall (ev : eval Σ (mkApps (tConstruct kn c) args) e),
  ∑ args', (e = mkApps (tConstruct kn c) args') ×
  All2 (fun x y => ∑ ev' : eval Σ x y, eval_depth ev' < eval_depth ev) args args'.
Proof.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. exists []=> //.
  - intros ev. revert ev.
    rewrite mkApps_app /=.
    intros ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr.
    * subst f'. 
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
      eapply All2_impl; tea. cbn. intros ? ? [ev' ?]. exists ev'. lia.
      constructor. exists ev2. lia. constructor.
    * now cbn in i.
Qed.

Section eval_mkApps_rect.
  
  Variables (wfl : WcbvFlags) (Σ : global_declarations) (P : term → term → Type).

  Let IH x y (ev : eval Σ x y) := 
    forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> P t u.

  Lemma eval_mkApps_rect :
    (∀ a t t' : term,
	    forall ev : eval Σ a tBox, P a tBox → 
                            IH _ _ ev ->
                            eval Σ t t' → P t t' → P (tApp a t) tBox)
    → (∀ (f0 : term) (na : BasicAst.name) (b a a' res : term),
        forall ev : eval Σ f0 (tLambda na b),
          P f0 (tLambda na b)
          → IH _ _ ev
          → eval Σ a a' →
          P a a'
          → eval Σ (ECSubst.csubst a' 0 b) res
          → P (ECSubst.csubst a' 0 b) res → P (tApp f0 a) res)
    → (∀ (na : BasicAst.name) (b0 b0' b1 res : term),
          eval Σ b0 b0'
          → P b0 b0'
          → eval Σ (ECSubst.csubst b0' 0 b1) res
          → P (ECSubst.csubst b0' 0 b1) res →
          P (tLetIn na b0 b1) res)
    → (∀ (ind : Kernames.inductive) (pars : nat) (discr : term) 
         (c : nat) (args : list term) (brs : list  (list BasicAst.name × term)) 
         (br : list BasicAst.name × term) (res : term),
          eval Σ discr (mkApps (tConstruct ind c) args)
          → P discr (mkApps (tConstruct ind c) args)
          → inductive_isprop_and_pars Σ ind = Some (false, pars)
          → nth_error brs c = Some br
          → #|skipn pars args| = #|br.1|
          → eval Σ (iota_red pars args br) res
          → P (iota_red pars args br) res
          → P (tCase (ind, pars) discr brs) res)
    → (∀ (ind : Kernames.inductive) (pars : nat) (discr : term) 
         (brs : list (list BasicAst.name × term)) 
         (n : list BasicAst.name) (f3 res : term),
          with_prop_case
          → eval Σ discr tBox
          → P discr tBox
          → inductive_isprop_and_pars Σ ind = Some (true, pars)
          → brs = [(n, f3)]
          → eval Σ (ECSubst.substl (repeat tBox #|n|) f3) res
          → P (ECSubst.substl (repeat tBox #|n|) f3) res
          → P (tCase (ind, pars) discr brs) res)
    → (∀ (f4 : term) (mfix : mfixpoint term) 
         (idx : nat) (argsv : list term) 
         (a av fn res : term),
        forall guarded : with_guarded_fix,
        forall ev : eval Σ f4 (mkApps (tFix mfix idx) argsv),
          P f4 (mkApps (tFix mfix idx) argsv)
          → IH _ _ ev
          → eval Σ a av
          → P a av
          → cunfold_fix mfix idx = Some (#|argsv|, fn)
          → eval Σ (tApp (mkApps fn argsv) av) res
          → P (tApp (mkApps fn argsv) av) res
          → P (tApp f4 a) res)
    → (∀ (f5 : term) (mfix : mfixpoint term) 
         (idx : nat) (argsv : list term) 
         (a av : term) (narg : nat) (fn : term),
        forall guarded : with_guarded_fix,
        forall ev : eval Σ f5 (mkApps (tFix mfix idx) argsv),
          P f5 (mkApps (tFix mfix idx) argsv) 
          → IH _ _ ev
          → eval Σ a av
          → P a av
          → cunfold_fix mfix idx = Some (narg, fn)
          → #|argsv| < narg
          → P (tApp f5 a) (tApp (mkApps (tFix mfix idx) argsv) av))
    → (∀ (f6 : term) (mfix : mfixpoint term) 
         (idx : nat) (a fn res : term) (narg : nat) 
         (unguarded : with_guarded_fix = false) 
         (ev : eval Σ f6 (tFix mfix idx)),
          P f6 (tFix mfix idx)
          → IH _ _ ev
          → cunfold_fix mfix idx = Some (narg, fn)
          → eval Σ (tApp fn a) res
          → P (tApp fn a) res
          → P (tApp f6 a) res)
    → (∀ (ip : Kernames.inductive × nat) (mfix : mfixpoint term) 
         (idx : nat) (args : list term) 
         (narg : nat) discr (fn : term) (brs : list (list BasicAst.name × term)) 
         (res : term),
          cunfold_cofix mfix idx = Some (narg, fn)
          -> eval Σ discr (mkApps (tCoFix mfix idx) args)
          -> P discr (mkApps (tCoFix mfix idx) args)
          → eval Σ (tCase ip (mkApps fn args) brs) res
          → P (tCase ip (mkApps fn args) brs) res
          → P (tCase ip discr brs) res)
    → (∀ (p : Kernames.projection) (mfix : mfixpoint term) 
         (idx : nat) (args : list term) 
         (narg : nat) discr (fn res : term),
          cunfold_cofix mfix idx = Some (narg, fn)
          -> eval Σ discr (mkApps (tCoFix mfix idx) args)
          -> P discr (mkApps (tCoFix mfix idx) args)
          → eval Σ (tProj p (mkApps fn args)) res
          → P (tProj p (mkApps fn args)) res
          → P (tProj p discr) res)
    → (∀ (c : Kernames.kername) (decl : constant_body) (body : term),
          declared_constant Σ c decl
          → ∀ res : term,
          cst_body decl = Some body
          → eval Σ body res
          → P body res → P (tConst c) res)
    → (∀ (i : inductive) (pars arg : nat) 
         (discr : term) (args : list term) 
         (res : term),
          eval Σ discr (mkApps (tConstruct i 0) args)
          → P discr (mkApps (tConstruct i 0) args)
          → inductive_isprop_and_pars Σ i = Some (false, pars)
          → eval Σ (nth (pars + arg) args tDummy) res
          → P (nth (pars + arg) args tDummy) res
          → P (tProj (i, pars, arg) discr) res)
    → (∀ (i : inductive) (pars arg : nat) (discr : term),
          with_prop_case
          → eval Σ discr tBox
          → P discr tBox
          → inductive_isprop_and_pars Σ i = Some (true, pars)
          → P (tProj (i, pars, arg) discr) tBox)
    → (∀ (f11 f' : term) a a' ,
        forall (ev : eval Σ f11 f'),
          P f11 f' ->
          IH _ _ ev
          → ~~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f')
          → eval Σ a a'
          → P a a'
          → P (tApp f11 a) (tApp f' a'))
    → (∀ t : term, atom t → P t t)
    → ∀ t t0 : term, eval Σ t t0 → P t t0.
Proof.
  intros.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & eval Σ t t0 }}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2))).
  set(foo := existT _ t (existT _ t0 H) :  { t : _ & { t0 : _ & eval Σ t t0 }}).
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  clear t t0 H.
  intros (t & t0 & ev). 
  intros IH'.
  set (IH'' t t0 H := IH' (t; t0; H)). clearbody IH''; clear IH'; rename IH'' into IH'.
  cbn in IH'. unfold MR in IH'; cbn in IH'. cbn.
  destruct ev; cbn in IH'.
  all:try match goal with
  | [ H : _ |- _ ] =>
    eapply H; tea; unshelve eapply IH'; tea; cbn; try lia
  end.
  all:try solve[match goal with
  | [ H : _ |- _ ] =>
    unshelve eapply H; try match goal with |- eval _ _ _ => tea end; tea; unfold IH; intros; unshelve eapply IH'; tea; cbn; try lia
  end].
Qed.

End eval_mkApps_rect.

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

  Definition Qpres (Q : nat -> term -> Type) := 
    forall n t, Q n t <~> OnSubterm.on_subterms Q n t.
  
  Lemma on_subterms_mkApps Q n f args : Qpres Q -> Q n (mkApps f args) <~> Q n f × All (Q n) args.
  Proof.
    intros qpres.
    etransitivity.
    eapply qpres.
    induction args using rev_ind; cbn; intuition auto.
    - split; intuition auto; now eapply qpres. 
    - rewrite mkApps_app.
      split; intros ons.
      depelim ons => //. split. eapply IHargs. now eapply qpres.
      eapply All_app_inv => //. 2:repeat constructor || auto.
      eapply IHargs. now eapply qpres.
      destruct ons. eapply All_app in a as [onargs onx].
      eapply All_tip in onx.
      eapply on_app => //. eapply qpres, IHargs. split => //. 
  Qed.
    
End OnSubterm.

Definition Qsubst (Q : nat -> term -> Type) :=
  forall n t l, Q (#|l| + n) t -> All (Q n) l -> Q n (substl l t).

Definition Qfix (Q : nat -> term -> Type) :=
  forall n mfix idx, Q n (tFix mfix idx) -> 
    forall args fn, cunfold_fix mfix idx = Some (args, fn) ->
    Q n fn.

Definition Qcofix (Q : nat -> term -> Type) :=
  forall n mfix idx, Q n (tCoFix mfix idx) -> 
    forall args fn, cunfold_cofix mfix idx = Some (args, fn) ->
    Q n fn.
      
Definition Qconst Σ (Q : nat -> term -> Type) :=
  ∀ kn decl, declared_constant Σ kn decl → 
    match cst_body decl with
    | None => unit
    | Some b => Q 0 b
    end.

Lemma eval_preserve_mkApps_ind :
∀ (wfl : WcbvFlags) (Σ : global_declarations) 
  (P' : term → term → Type)
  (Q : nat -> term -> Type)
  (P := (fun x y => P' x y × Q 0 x × Q 0 y)%type)
  (HPQ : ∀ t u, eval Σ t u -> Q 0 t -> P' t u -> Q 0 u),
  Qconst Σ Q ->
  Qpres Q ->
  Qsubst Q ->
  Qfix Q ->
  Qcofix Q ->
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
           → eval Σ (ECSubst.csubst b0' 0 b1) res
             → P (ECSubst.csubst b0' 0 b1) res → 
             P' (tLetIn na b0 b1) res)
      → (∀ (ind : inductive) (pars : nat) (discr : term) 
           (c : nat) (args : list term) (brs : 
                                              list 
                                                (list name × term)) 
           (br : list name × term) (res : term),
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
                           → P' (tApp f5 a)
                               (tApp
                                  (mkApps (tFix mfix idx) argsv) av))
            → (∀ (f5 : term) (mfix : mfixpoint term) 
            (idx : nat) (a av : term) (narg : nat) (fn : term) res,
            with_guarded_fix = false ->
            eval Σ f5 (tFix mfix idx)
            → P f5 (tFix mfix idx)
              → cunfold_fix mfix idx = Some (narg, fn)
              → eval Σ (tApp fn a) res   
              → P (tApp fn a) res
              → P' (tApp f5 a) res) → 
              
              (∀ (ip : inductive × nat) (mfix : mfixpoint term) 
                   (idx : nat) (args : list term) 
                   (narg : nat) discr (fn : term) (brs : 
                                                 list 
                                                 (list name × term)) 
                   (res : term),
                   cunfold_cofix mfix idx = Some (narg, fn)
                   -> eval Σ discr (mkApps (tCoFix mfix idx) args)
                   -> P discr (mkApps (tCoFix mfix idx) args)
                   → eval Σ (tCase ip (mkApps fn args) brs) res
                     → P (tCase ip (mkApps fn args) brs) res
                       → P'
                           (tCase ip discr brs)
                           res)
                → (∀ (p : projection) (mfix : mfixpoint term) 
                     (idx : nat) (args : list term) 
                     (narg : nat) discr (fn res : term),
                     cunfold_cofix mfix idx = Some (narg, fn)
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
                                     tBox)
                        → (∀ (f11 f' : term) a a' ,
                             forall (ev : eval Σ f11 f'),
                              P f11 f' ->  
                              (forall t u (ev' : eval Σ t u), eval_depth ev' <= eval_depth ev -> Q 0 t -> P t u)
                            → ~~
                                 (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f')
                                 → eval Σ a a'
                                → P a a'
                          →  P' (tApp f11 a) (tApp f' a'))
                                  
                          → (∀ t : term, atom t → P' t t) ->
  ∀ (t t0 : term), Q 0 t -> eval Σ t t0 → P' t t0.
Proof.
  intros * P'Q qconst Qpres Qs qfix qcofix. intros.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2.π2))).
  set(foo := existT _ t (existT _ t0 (existT _ X14 H)) :  { t : _ & { t0 : _ & { qt : Q 0 t & eval Σ t t0 }}}).
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  rename X14 into qt.
  clear t t0 qt H.
  intros (t & t0 & qt & ev). 
  intros IH.
  set (IH' t t0 q H := IH (t; t0; q; H)). clearbody IH'; clear IH; rename IH' into IH.
  cbn in IH. unfold MR in IH; cbn in IH. cbn.
  Ltac ih := 
    match goal with 
    [ IH : forall x y, ?Q 0 x -> _ |- _ ] => unshelve eapply IH; tea; cbn; try lia
    end.
  destruct ev.
  all:eapply Qpres in qt; depelim qt => //.
  all:try solve [match goal with
  | [ H : _ |- _ ] =>
    eapply H; tea; (apply and_assum; [unshelve eapply IH; tea; cbn; try lia|intros hp'; split => //; eapply P'Q; tea])
  end].
  - eapply X0; tea. 1-2:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    assert (qs: Q 0 (csubst a' 0 b)).
    { assert (Q 0 (tLambda na b)).
      { eapply P'Q; tea. ih. }
      eapply Qpres in X14. depelim X14 => //.
      eapply (Qs 0 b [a']) in q1. now cbn in q1.
      repeat constructor.
      eapply P'Q; tea; ih. }
    eapply and_assum. ih.
    intros hp'. split => //. eapply P'Q; tea; ih.
  - eapply X1; tea. 1:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    assert (qs : Q 0 (csubst b0' 0 b1)).
    { eapply (Qs 0 b1 [b0']) in q0. now cbn in q0.
      repeat constructor.
      eapply P'Q; tea; ih. }
    apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - eapply X2; tea. 1:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    unfold iota_red.
    eapply nth_error_all in a; tea. cbn in a.
    rewrite -e1 in a.
    rewrite -(List.rev_length (skipn pars args)) in a.
    eapply (Qs _ _ (List.rev (skipn pars args))) in a.
    2:{ eapply All_rev, All_skipn. 
      assert (Q 0 (mkApps (tConstruct ind c) args)).
      eapply P'Q; tea; ih.
      eapply on_subterms_mkApps in X14; tea. eapply X14. } 
    eapply and_assum. ih. unfold iota_red. lia.
    intros hp'. split => //. eapply P'Q; tea.
  - eapply X3; tea. 1:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    subst brs. eapply All_tip in a. cbn in a.
    rewrite -(repeat_length tBox #|n|) in a.
    eapply (Qs _ _ (repeat tBox #|n|)) in a.
    2:{ eapply All_repeat. 
        eapply P'Q; tea; ih. }
    eapply and_assum. ih.
    intros hp'. split => //. eapply P'Q; tea.
  - eapply X4; tea.
    1,2:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    assert (qa : Q 0 (tApp (mkApps fn argsv) av)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply on_subterms_mkApps in ev1' as [hfix qargs] => //.
      eapply Qpres. eapply on_app. eapply on_subterms_mkApps => //.
      split => //. eapply (qfix 0 mfix idx) in hfix; tea.
      eapply P'Q; tea; ih. clear ev1'; ih. }
    apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - eapply X6; tea. 
    1:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    assert (qa : Q 0 (tApp fn a)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //. 2:clear ev1'; ih.
      eapply qfix in ev1'. cbn in IH. eapply ev1' in e.
      eapply Qpres. eapply on_app => //. }
    apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - eapply X7; tea.
    1:(apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
    assert (qa : Q 0 (tCase ip (mkApps fn args) brs)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply on_subterms_mkApps in ev1' as [hfix qargs] => //.
      eapply Qpres. eapply on_case. eapply on_subterms_mkApps => //.
      split => //. eapply (qcofix 0 mfix idx) in hfix; tea. exact a.
      clear ev1'; ih. }
    apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - cbn in IH.
    assert (qa : Q 0 (tProj p (mkApps fn args))).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply on_subterms_mkApps in ev1' as [hfix qargs] => //.
      eapply Qpres. eapply on_proj. eapply on_subterms_mkApps => //.
      split => //. eapply (qcofix 0 mfix idx) in hfix; tea.
      clear ev1'; ih. }
    eapply X8; tea.
    all:apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - eapply X9; tea.
    assert (Q 0 body).
    { cbn in IH; eapply qconst in isdecl. now rewrite e in isdecl. }
    all:apply and_assum; [ih|].
    intros hp'; split => //. eapply P'Q; tea.
  - assert (Q 0 (nth (pars + arg) args tDummy)).
    { pose proof (ev1' := ev1). eapply P'Q in ev1' => //.
      eapply on_subterms_mkApps in ev1' as [hfix qargs] => //.
      { clear -Qpres qargs. generalize (pars+arg).
        induction args; cbn.
        destruct n; eapply Qpres; constructor => //.
        depelim qargs. intros [] => //. now eapply IHargs. }
      clear ev1'; ih. }
    eapply X10; tea.
    all:apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea].
  - unshelve eapply X12; tea.
    all:try (intros; apply and_assum; [ih|intros hp'; split => //; eapply P'Q; tea]).
Qed.

