From Coq Require Import Arith List.
From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import
     PCUICAst PCUICAstUtils PCUICTyping
     PCUICInversion PCUICWeakeningEnv.
Set Warnings "-notation-overridden".
From MetaCoq.Erasure Require Import
     EAst EAstUtils ECSubst EInduction
     ELiftSubst ESubstitution ETyping Extract
     EWcbvEval Prelim.
Set Warnings "+notation-overridden".
From MetaCoq.Template Require Import config utils monad_utils.

Derive NoConfusion for term.
Derive Signature for erases_deps.
Derive Signature for Forall.

Lemma erases_deps_mkApps Σ Σ' hd args :
  erases_deps Σ Σ' hd ->
  Forall (erases_deps Σ Σ') args ->
  erases_deps Σ Σ' (mkApps hd args).
Proof.
  intros er erall.
  induction args using rev_ind; [easy|].
  rewrite !mkApps_app.
  cbn in *.
  apply Forall_app in erall as (? & ?).
  depelim H0.
  now constructor.
Qed.

Lemma erases_deps_mkApps_inv Σ Σ' hd args :
  erases_deps Σ Σ' (mkApps hd args) ->
  erases_deps Σ Σ' hd /\ Forall (erases_deps Σ Σ') args.
Proof.
  intros er.
  induction args using rev_ind; [easy|].
  rewrite mkApps_app in *.
  cbn in *.
  depelim er.
  intuition auto.
  now apply app_Forall.
Qed.

Lemma erases_deps_lift Σ Σ' n k t :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (lift n k t).
Proof.
  intros er.
  induction t in k, t, er |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _); constructor.
  - depelim er.
    constructor.
    induction H; cbn in *; [easy|].
    now depelim X.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    econstructor; eauto.
    induction X; [easy|].
    depelim H2.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
Qed.

Lemma erases_deps_subst Σ Σ' s k t :
  All (erases_deps Σ Σ') s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (subst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _); [|now constructor].
    destruct nth_error eqn:nth; [|now constructor].
    eapply All_nth_error in nth; [|now eauto].
    now apply erases_deps_lift.
  - depelim er.
    constructor.
    induction H; [simpl; easy|].
    depelim X.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    econstructor; eauto.
    induction X; [easy|].
    depelim H2.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
Qed.

Lemma erases_deps_subst1 Σ Σ' t k u :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' u ->
  erases_deps Σ Σ' (subst1 t k u).
Proof.
  intros.
  apply erases_deps_subst; [|easy].
  now constructor.
Qed.

Lemma erases_deps_csubst Σ Σ' s k t :
  erases_deps Σ Σ' s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (csubst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ ?= _); try constructor; easy.
  - depelim er.
    constructor.
    induction H; [simpl; easy|].
    depelim X.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    econstructor; [easy|easy|easy|easy|].
    induction X; [easy|].
    depelim H2.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now econstructor.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl;easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
  - depelim er.
    constructor.
    induction H in k, H, X |- *; [simpl; easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim X.
    constructor; [|easy].
    now apply e.
Qed.

Lemma erases_deps_substl Σ Σ' s t :
  Forall (fun s => erases_deps Σ Σ' s) s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (substl s t).
Proof.
  intros all exp.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_app in all as (? & erx).
  depelim erx.
  now apply erases_deps_csubst.
Qed.

Lemma Forall_erases_deps_fix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (fix_subst defs).
Proof.
  intros all.
  unfold ETyping.fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma Forall_erases_deps_cofix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (ETyping.cofix_subst defs).
Proof.
  intros all.
  unfold ETyping.cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma erases_deps_cunfold_fix Σ Σ' defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_fix_subst.
Qed.

Lemma erases_deps_cunfold_cofix Σ Σ' defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_cofix_subst.
Qed.

Notation "Σ ⊢ s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma erases_deps_eval {wfl:WcbvFlags} Σ t v Σ' :
  Σ' ⊢ t ▷ v ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' v.
Proof.
  intros ev er.
  induction ev in t, v, ev, er |- *; cbn in *.
  - now constructor.
  - depelim er.
    apply IHev3.
    apply erases_deps_csubst; [easy|].
    intuition auto.
    now depelim H.
  - depelim er.
    now apply IHev2, erases_deps_csubst.
  - depelim er.
    apply IHev2.
    unfold ETyping.iota_red.
    apply erases_deps_mkApps.
    + rewrite nth_nth_error.
      destruct nth_error eqn:nth; [|now constructor].
      eapply nth_error_forall in nth; [|now eauto].
      assumption.
    + intuition auto.
      apply erases_deps_mkApps_inv in H3.
      now apply Forall_skipn.
  - depelim er.
    subst brs; cbn in *.
    depelim H2.
    cbn in *.
    apply IHev2.
    apply erases_deps_mkApps; [easy|].
    apply All_Forall, All_repeat.
    now constructor.
  - depelim er.
    intuition auto.
    eapply erases_deps_mkApps_inv in H as (? & ?).
    depelim H.
    apply IHev3.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_fix.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H as (? & ?).
    constructor; [|easy].
    now apply erases_deps_mkApps.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H3.
    apply IHev.
    econstructor; [easy|easy|easy| |easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix; eauto.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H2.
    apply IHev.
    econstructor; eauto.
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    now apply IHev, H2.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H2 as (? & ?).
    apply IHev2.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; [|now constructor].
    now eapply nth_error_forall in nth.
  - constructor.
  - depelim er.
    now constructor.
  - easy.
Qed.

Hint Resolve erases_deps_eval erases_deps_subst erases_deps_subst1 : core.

Local Existing Instance config.extraction_checker_flags.

Lemma erases_deps_forall_ind Σ Σ'
  (P : Extract.E.term -> Prop)
  (Hbox : P Extract.E.tBox)
  (Hrel : forall i : nat, P (Extract.E.tRel i))
  (Hvar : forall n : ident, P (Extract.E.tVar n))
  (Hevar :
     forall (m : nat) (l : list Extract.E.term),
       Forall P l ->
       Forall (erases_deps Σ Σ') l -> P (Extract.E.tEvar m l))
  (Hlam : forall (na : name) (body : Extract.E.term),
        erases_deps Σ Σ' body -> P body -> P (Extract.E.tLambda na body))
  (Hletin : forall (na : name) (val body : Extract.E.term),
        erases_deps Σ Σ' val ->
        P val -> erases_deps Σ Σ' body -> P body -> P (Extract.E.tLetIn na val body))
  (Happ : forall hd arg : Extract.E.term,
        erases_deps Σ Σ' hd -> P hd -> erases_deps Σ Σ' arg -> P arg -> P (Extract.E.tApp hd arg))
  (Hconst : forall (kn : kername) (cb : PCUICAst.PCUICEnvironment.constant_body) (cb' : EAst.constant_body),
      PCUICAst.declared_constant Σ kn cb ->
      ETyping.declared_constant Σ' kn cb' ->
      erases_constant_body (Σ, cst_universes cb) cb cb' ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> P body) ->
        P (Extract.E.tConst kn))
  (Hconstruct : forall (ind : inductive) (c : nat), P (Extract.E.tConstruct ind c))
  (Hcase : forall (p : inductive × nat) mdecl idecl mdecl' idecl' (discr : Extract.E.term) (brs : list (nat × Extract.E.term)),
        PCUICAst.declared_inductive Σ (fst p) mdecl idecl ->
        ETyping.declared_inductive Σ' (fst p) mdecl' idecl' ->
        erases_one_inductive_body idecl idecl' ->
        erases_deps Σ Σ' discr ->
        P discr ->
        Forall (fun br : nat × Extract.E.term => erases_deps Σ Σ' br.2) brs ->
        Forall (fun br => P br.2) brs ->
        P (Extract.E.tCase p discr brs))
  (Hproj : forall (p : projection) mdecl idecl mdecl' idecl' (t : Extract.E.term),
        PCUICAst.declared_inductive Σ p.1.1 mdecl idecl ->
        ETyping.declared_inductive Σ' p.1.1 mdecl' idecl' ->
        erases_one_inductive_body idecl idecl' ->
        erases_deps Σ Σ' t -> P t -> P (Extract.E.tProj p t))
  (Hfix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tFix defs i))
  (Hcofix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tCoFix defs i)) :
  forall t, erases_deps Σ Σ' t -> P t.
Proof.
  fix f 2.
  intros t ed.
  move f at top.
  destruct ed;
    try solve [match goal with
    | [H: _ |- _] => apply H
    end; auto].
  - apply Hevar; [|assumption].
    revert l H.
    fix f' 2.
    intros l [].
    + now constructor.
    + constructor; [now apply f|now apply f'].
  - eapply Hconst; try eassumption.
    intros.
    apply f.
    now apply H2.
  - eapply Hcase; try eassumption.
    + now apply f.
    + revert brs H2.
      fix f' 2.
      intros brs []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - eapply Hproj; try eassumption.
    now apply f.
  - eapply Hfix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - apply Hcofix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
Defined.

Lemma erases_deps_cons Σ Σ' kn decl decl' t :
  wf ((kn, decl) :: Σ) ->
  erases_deps Σ Σ' t ->
  erases_deps ((kn, decl) :: Σ) ((kn, decl') :: Σ') t.
Proof.
  intros wfΣ er.
  induction er using erases_deps_forall_ind; try solve [now constructor].
  apply lookup_env_Some_fresh in H as not_fresh.
  econstructor.
  - unfold PCUICAst.declared_constant in *; cbn.
    unfold eq_kername.
    inversion wfΣ; subst.
    destruct kername_eq_dec as [<-|]; [congruence|].
    eassumption.
  - unfold ETyping.declared_constant in *; cbn.
    inversion wfΣ; subst.
    destruct kername_eq_dec; [congruence|].
    eassumption.
  - unfold erases_constant_body in *.
    destruct PCUICAst.PCUICEnvironment.cst_body eqn:body.
    + destruct E.cst_body eqn:ebody; [|easy].
      assert (PCUICAst.declared_constant ((kn, decl) :: Σ) kn0 cb).
      { unfold PCUICAst.declared_constant.
        cbn.
        unfold eq_kername.
        inversion wfΣ; subst.
        destruct kername_eq_dec as [<-|]; [congruence|].
        easy. }
      inversion wfΣ; subst.
      eapply PCUICWeakeningEnv.declared_constant_inv in H4; eauto.
      2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      red in H4.
      rewrite body in *.
      cbn in *.
      eapply (erases_extends (_, cst_universes cb)); eauto.
      2: eexists [_]; reflexivity.
      eapply declared_constant_inv in H.
      2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      2: easy.
      2: easy.
      unfold on_constant_decl in H.
      rewrite body in *.
      apply H.
    + now destruct E.cst_body.
  - easy.
  - econstructor; eauto.
    destruct H as [H H'].
    split; eauto. red in H |- *.
    inv wfΣ.
    simpl. unfold eq_kername.
    destruct (kername_eq_dec (inductive_mind p.1) kn); auto. subst.
    eapply lookup_env_Some_fresh in H; eauto. contradiction.
    destruct H0 as [H0 H0'].
    split; eauto. red in H0 |- *.
    inv wfΣ. simpl.
    destruct (kername_eq_dec (inductive_mind p.1) kn); auto. subst.
    destruct H as [H _].
    eapply lookup_env_Some_fresh in H. eauto. contradiction.
  - econstructor; eauto.
    destruct H as [H H'].
    split; eauto. red in H |- *.
    inv wfΣ.
    simpl. unfold eq_kername.
    destruct (kername_eq_dec (inductive_mind p.1.1) kn); auto. subst.
    eapply lookup_env_Some_fresh in H; eauto. contradiction.
    destruct H0 as [H0 H0'].
    split; eauto. red in H0 |- *.
    inv wfΣ. simpl.
    destruct (kername_eq_dec (inductive_mind p.1.1) kn); auto. subst.
    destruct H as [H _].
    eapply lookup_env_Some_fresh in H. eauto. contradiction.
Qed.

Derive Signature for erases_global_decls.
Derive Signature for Forall2.

Definition globals_erased_with_deps Σ Σ' :=
  (forall k cst,
    PCUICAst.declared_constant Σ k cst ->
    exists cst',
      ETyping.declared_constant Σ' k cst' /\
      erases_constant_body (Σ, cst_universes cst) cst cst' /\
      (forall body, cst_body cst' = Some body -> erases_deps Σ Σ' body)) /\
  (forall k mdecl idecl,
      PCUICAst.declared_inductive Σ k mdecl idecl ->
      exists mdecl' idecl',
        ETyping.declared_inductive Σ' k mdecl' idecl' /\
        erases_mutual_inductive_body mdecl mdecl').


Lemma erases_deps_single Σ Σ' t T et :
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ et ->
  globals_erased_with_deps Σ Σ' ->
  erases_deps Σ Σ' et.
Proof.
  intros wf wt er Σer.
  induction er in er, t, T, wf, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor].
  - now apply inversion_Evar in wt.
  - constructor.
    now apply inversion_Lambda in wt as (? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
    now constructor; eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    now constructor; eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    apply Σer in d as d'; destruct d' as (? & ? & ? & ?).
    now econstructor; eauto.
  - todo "case".
  (*apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    destruct (proj2 Σer _ _ _ d) as (? & ? & ? & ?).
    econstructor; eauto.
    destruct H2. destruct d. destruct H1.
    eapply Forall2_All2 in H2. eapply All2_nth_error in H2; eauto.
    clear -wf a X H0 Σer.
    revert brs' x5 a X H0 Σer.
    induction brs; intros brs' x5 brtys typ er deps.
    { now depelim er. }
    depelim brtys.
    depelim typ.
    depelim er.
    destruct p as ((? & ?) & ?).
    destruct p0.
    now constructor; eauto. *)

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    destruct (proj2 Σer _ _ _ (proj1 (proj1 d))) as (? & ? & ? & ?).
    econstructor; eauto. eapply d.
    destruct d as [[[declm decli] declc] _]. destruct H1. destruct H0.
    eapply Forall2_All2 in H1. eapply All2_nth_error in H1; eauto.

  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H Σer.
    revert a0 X H Σer.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p as (?&?&?).
    now constructor; eauto.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H Σer.
    revert a0 X H Σer.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p as (?&?&?).
    now constructor; eauto.
Qed.

Lemma Forall2_nth_error_left {A B} {P} {l : list A} {l' : list B} : Forall2 P l l' ->
  forall n x, nth_error l n = Some x ->
  exists x', nth_error l' n = Some x' /\ P x x'.
Proof.  
  induction 1; destruct n; simpl; auto; try discriminate.
  intros x' [= ->]. eexists; eauto.
Qed.

Lemma erases_global_all_deps Σ Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  globals_erased_with_deps Σ Σ'.
Proof.
  intros wf erg.
  induction Σ as [|(kn, decl) Σ IH] in Σ', wf, erg |- *; cbn in *.
  - depelim erg.
    split; [intros ? ? decl; discriminate decl|].
    intros ? ? ? [decl _]; discriminate decl.
  - split.
    intros kn' cst' decl'.
    destruct (eq_dec kn kn') as [<-|].
    + unfold PCUICAst.declared_constant, ETyping.declared_constant in *; cbn in *.
      rewrite eq_kername_refl in *.
      noconf decl'.
      depelim erg.
      exists cb'.
      cbn.
      destruct kername_eq_dec; [|congruence].
      split; [easy|].
      inversion wf; subst.
      cbn in *.
      split.
      * unfold erases_constant_body, on_constant_decl in *.
        destruct ?; [|easy].
        destruct ?; [|easy].
        eapply (erases_extends (_, cst_universes cst')).
        4: eexists [_]; cbn; reflexivity.
        all: eauto.
      * intros.
        apply erases_deps_cons; [easy|].
        unfold erases_constant_body in *.
        rewrite H0 in *.
        destruct ?; [|easy].
        unfold on_constant_decl in *.
        rewrite E in *.
        cbn in *.
        eapply (erases_deps_single (_, _)); eauto.
        now constructor.
    + assert (exists decl' Σ'', Σ' = (kn, decl') :: Σ'' /\ erases_global Σ Σ'')
        as (erdecl & ? & -> & erg')
          by now depelim erg; eexists _, _.
      apply IH in erg'; [|now inversion wf].
      assert (decl_ext: PCUICAst.declared_constant Σ kn' cst').
      { unfold PCUICAst.declared_constant in *; cbn in *.
        unfold eq_kername in *.
        now destruct kername_eq_dec; [|congruence]. }
      specialize (proj1 erg' kn' cst' decl_ext) as (cst & decl'' & ? & ?).
      exists cst.
      split; [|split].
      * unfold declared_constant in *; cbn.
        now destruct kername_eq_dec; [|congruence].
      * inversion wf; subst.
        eapply declared_constant_inv in decl_ext; eauto.
        2: exact weaken_env_prop_typing.
        unfold on_constant_decl, erases_constant_body in *.
        destruct ?; [|easy].
        destruct ?; [|easy].
        eapply (erases_extends (_, cst_universes cst')).
        4: eexists [_]; cbn; reflexivity.
        all: eauto.
      * intros.
        apply H0 in H1.
        now apply erases_deps_cons.
  + intros k mdecl idecl decli.
    depelim erg.
    * inv wf.
      specialize (IH _ X erg).
      apply proj2 in IH. specialize (IH k mdecl idecl).
      forward IH.
      destruct decli as [decli ?]. split; auto.
      red in decli |- *. simpl in decli |- *.
      unfold eq_kername in decli |- *.
      destruct kername_eq_dec. subst. discriminate. auto.
      destruct IH as [mdecl' [idecl' [decli' er]]].
      exists mdecl', idecl'. split; auto.
      red. destruct decli'; split; auto.
      red in decli.
      unfold declared_minductive in *.
      simpl. destruct kername_eq_dec; subst; auto.
      unfold PCUICAst.declared_minductive in decli.
      simpl in decli. rewrite eq_kername_refl in decli. intuition discriminate.
    * inv wf.
      specialize (IH _ X erg).
      destruct decli as [decli ?]. 
      simpl in decli |- *.
      unfold PCUICAst.declared_minductive in decli.
      simpl in decli.
      unfold eq_kername in decli |- *.
      destruct kername_eq_dec. subst. noconf decli.
      destruct (Forall2_nth_error_left (proj1 H) _ _ H2); eauto.
      eexists _, _; intuition eauto. split; eauto. red.
      simpl. destruct kername_eq_dec; try congruence.
      destruct (proj2 IH _ _ _ (conj decli H2)) as [m' [i' [decli' ei]]].
      eexists _, _; intuition eauto.
      destruct decli'; red; split; eauto.
      red in d |- *. simpl.
      destruct kername_eq_dec; subst; try congruence.
Qed.       

Lemma erases_global_erases_deps Σ t T et Σ' :
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ et ->
  erases_global Σ Σ' ->
  erases_deps Σ Σ' et.
Proof.
  intros.
  eapply erases_deps_single; eauto.
  now eapply erases_global_all_deps.
Qed.
