(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils Kernames BasicAst EnvMap.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EWcbvEval EGlobalEnv ECSubst EInduction.

Set Asymmetric Patterns.
From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.

#[global]
Hint Constructors eval : core.

Definition and_assum {A B : Type} (f : A) (f' : A -> B) : A × B :=
  (f, f' f).
  
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

