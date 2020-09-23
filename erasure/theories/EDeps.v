From Coq Require Import Arith List.
From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import
     PCUICAst PCUICAstUtils PCUICTyping
     PCUICInversion PCUICWeakeningEnv.
From MetaCoq.Erasure Require Import
     EAst EAstUtils ECSubst EInduction
     ELiftSubst ESubstitution ETyping Extract
     EWcbvEval Prelim.
From MetaCoq.Template Require Import config utils monad_utils.
Set Asymmetric Patterns.

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
    now depelim H0.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
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
    induction H; [easy|].
    depelim H0.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
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
    induction H; [easy|].
    depelim H0.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
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

Lemma erases_deps_eval Σ t v Σ' :
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
      apply erases_deps_mkApps_inv in H0.
      now apply Forall_skipn.
  - depelim er.
    subst brs; cbn in *.
    depelim H0.
    cbn in *.
    apply IHev2.
    apply erases_deps_mkApps; [easy|].
    apply All_Forall, All_repeat.
    now constructor.
  - depelim er.
    intuition auto.
    eapply erases_deps_mkApps_inv in H0 as (? & ?).
    depelim H0.
    apply IHev3.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_fix.
  - depelim er.
    clear H0.
    intuition auto.
    apply erases_deps_mkApps_inv in H0 as (? & ?).
    constructor; [|easy].
    now apply erases_deps_mkApps.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H1.
    apply IHev.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H0.
    apply IHev.
    constructor.
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    now apply IHev, H3.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H as (? & ?).
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
      PCUICTyping.declared_constant Σ kn cb ->
      ETyping.declared_constant Σ' kn cb' ->
      erases_constant_body (Σ, PCUICAst.cst_universes cb) cb cb' ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> P body) ->
        P (Extract.E.tConst kn))
  (Hconstruct : forall (ind : inductive) (c : nat), P (Extract.E.tConstruct ind c))
  (Hcase : forall (p : inductive × nat) (discr : Extract.E.term) (brs : list (nat × Extract.E.term)),
        erases_deps Σ Σ' discr ->
        P discr ->
        Forall (fun br : nat × Extract.E.term => erases_deps Σ Σ' br.2) brs ->
        Forall (fun br => P br.2) brs ->
        P (Extract.E.tCase p discr brs))
  (Hproj : forall (p : projection) (t : Extract.E.term),
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
  - apply Hcase; try assumption.
    + now apply f.
    + revert brs H.
      fix f' 2.
      intros brs []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - apply Hfix; try assumption.
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
  - unfold PCUICTyping.declared_constant in *; cbn.
    unfold eq_kername.
    inversion wfΣ; subst.
    destruct kername_eq_dec as [<-|]; [congruence|].
    eassumption.
  - unfold ETyping.declared_constant in *; cbn.
    inversion wfΣ; subst.
    destruct kername_eq_dec; [congruence|].
    eassumption.
  - unfold erases_constant_body in *.
    destruct PCUICAst.cst_body eqn:body.
    + destruct E.cst_body eqn:ebody; [|easy].
      assert (PCUICTyping.declared_constant ((kn, decl) :: Σ) kn0 cb).
      { unfold PCUICTyping.declared_constant.
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
Qed.

Derive Signature for erases_global_decls.
Derive Signature for Forall2.

Definition globals_erased_with_deps Σ Σ' :=
  forall k cst,
    PCUICTyping.declared_constant Σ k cst ->
    exists cst',
      ETyping.declared_constant Σ' k cst' /\
      erases_constant_body (Σ, cst_universes cst) cst cst' /\
      (forall body, cst_body cst' = Some body -> erases_deps Σ Σ' body).

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
  - apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    constructor; [now eauto|].
    clear -wf a X H0 Σer.
    revert brs' x5 a X H0 Σer.
    induction brs; intros brs' x5 brtys typ er deps.
    { now depelim er. }
    depelim brtys.
    depelim typ.
    depelim er.
    destruct p as ((? & ?) & ?).
    destruct p0.
    now constructor; eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.
    constructor.
    now eapply IHer; eauto.
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
    destruct p.
    destruct p0 as (?&?&?).
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

Lemma erases_global_all_deps Σ Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  globals_erased_with_deps Σ Σ'.
Proof.
  intros wf erg.
  induction Σ as [|(kn, decl) Σ IH] in Σ', wf, erg |- *; cbn in *.
  - depelim erg.
    intros ? ? decl; discriminate decl.
  - intros kn' cst' decl'.
    destruct (eq_dec kn kn') as [<-|].
    + unfold PCUICTyping.declared_constant, ETyping.declared_constant in *; cbn in *.
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
      assert (decl_ext: PCUICTyping.declared_constant Σ kn' cst').
      { unfold PCUICTyping.declared_constant in *; cbn in *.
        unfold eq_kername in *.
        now destruct kername_eq_dec; [|congruence]. }
      specialize (erg' kn' cst' decl_ext) as (cst & decl'' & ? & ?).
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
