(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import Transform bytestring config utils BasicAst uGraph.
From MetaCoq.Template Require Pretty Environment Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness TemplateToPCUICWcbvEval TemplateToPCUICExpanded.
From MetaCoq.PCUIC Require PCUICExpandLets PCUICExpandLetsCorrectness.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr ERemoveParams EWcbvEval EDeps.
Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

#[local] Instance extraction_checker_flags : checker_flags := 
  {| check_univs := true;
     prop_sub_type := false;
     indices_matter := false;
     lets_in_constructor_types := true |}.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.
Obligation Tactic := idtac.

Obligation Tactic := program_simpl.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ wf Σ ∥) : wf_env := 
  {| wf_env_referenced := {| referenced_impl_env := Σ.(trans_env_env); referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Import EGlobalEnv.

Definition eprogram := 
  (EAst.global_context * EAst.term).

Import EEnvMap.GlobalContextMap (make, global_decls).

Arguments EWcbvEval.eval {wfl} _ _ _.

Definition closed_eprogram (p : eprogram) := 
  closed_env p.1 && ELiftSubst.closedn 0 p.2.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) := 
  EWcbvEval.eval (wfl:=wfl) p.1 p.2 t.

Definition eprogram_env := 
  (EEnvMap.GlobalContextMap.t * EAst.term).

Definition closed_eprogram_env (p : eprogram_env) := 
  let Σ := p.1.(global_decls) in
  closed_env Σ && ELiftSubst.closedn 0 p.2.

Definition eval_eprogram_env (wfl : EWcbvEval.WcbvFlags) (p : eprogram_env) (t : EAst.term) := 
  EWcbvEval.eval (wfl:=wfl) p.1.(global_decls) p.2 t.

Lemma wf_glob_fresh Σ : wf_glob Σ -> EnvMap.EnvMap.fresh_globals Σ.
Proof.
  induction Σ. constructor; auto.
  intros wf; depelim wf. constructor; auto.
Qed.
  
Program Definition erase_pcuic_program (p : pcuic_program) 
  (wfΣ : ∥ wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf _) wfΣ) in
  let wfe' := ErasureFunction.make_wf_env_ext wfe p.1.2 wfΣ in
  let t := ErasureFunction.erase wfe' nil p.2 _ in
  let Σ' := ErasureFunction.erase_global (EAstUtils.term_global_deps t) wfe in
  (EEnvMap.GlobalContextMap.make Σ' _, t).
  
Next Obligation.
  sq. destruct wt as [T Ht].
  cbn in *. subst. now exists T.
Qed.
Next Obligation.
  unfold ErasureFunction.erase_global.
  eapply wf_glob_fresh.
  eapply ERemoveParams.erase_global_decls_wf_glob.
Qed.


(* * The full correctness lemma of erasure from Template programs do λ-box

Lemma erase_template_program_correctness {p : Ast.Env.program} univs
  (Σ := (p.1, univs))
  {wfΣ : ∥ Typing.wf_ext Σ ∥}
  {wt : ∥ ∑ T, Typing.typing (p.1, univs) [] p.2 T ∥} {Σ' t'} :
  erase_template_program p univs wfΣ wt = (Σ', t') ->
  forall v, WcbvEval.eval p.1 p.2 v ->
  exists v',
    PCUICExpandLets.trans_global (trans_global Σ) ;;; [] |- 
      PCUICExpandLets.trans (trans (trans_global Σ) v) ⇝ℇ v' /\ 
    ∥ EWcbvEval.eval (wfl:=EWcbvEval.default_wcbv_flags) Σ' t' v' ∥.
Proof.
  unfold erase_template_program.
  intros [= <- <-] v ev.
  set (expΣ := (PCUICExpandLets.trans_global (trans_global Σ))).
  set (wfexpΣ := build_wf_env _ _).
  pose proof (erase_correct wfexpΣ).
  set (wfexpΣ' := make_wf_env_ext _ _ _) in *.
  set wftΣ : ∥ wf_ext (PCUICExpandLets.trans_global (trans_global Σ)) ∥ :=
    wfexpΣ'.(wf_env_ext_wf).
  specialize (H univs wftΣ (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) (PCUICExpandLets.trans (trans (trans_global Σ) v))).
  set wtp : PCUICSafeLemmata.welltyped (PCUICExpandLets.trans_global (trans_global Σ)) [] 
    (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) :=
    (erase_template_program_obligation_1 p univs wfΣ wt).
  set (t' := erase wfexpΣ' [] (PCUICExpandLets.trans (trans (trans_global_env p.1) p.2)) wtp) in *.
  set (deps := (term_global_deps _)).
  (* change (empty_ext (PCUICExpandLets.trans_global_env (trans_global_env p.1))) with *)
    (* (PCUICExpandLets.trans_global (trans_global Σ)) in *. *)
  specialize (H (erase_global deps wfexpΣ)).
  specialize (H _ deps wtp eq_refl).
  forward H. eapply Kernames.KernameSet.subset_spec. reflexivity.
  specialize (H eq_refl).
  destruct wt, wfΣ.
  have wfmid : wf (trans_global (p.1, univs)).1.
  { now eapply template_to_pcuic_env. }
  forward H.
  { unfold wfexpΣ. simpl.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := (trans_global_env p.1, univs))).
    { destruct s as [T HT].
      eapply (PCUICClosedTyp.subject_closed (Γ := [])). 
      apply (template_to_pcuic_typing (Σ := (p.1, univs)) [] _ T);simpl; eauto.
      eapply w. Unshelve. now eapply template_to_pcuic_env. }
    unshelve eapply trans_wcbvEval; eauto. apply w.
    destruct s as [T HT]. eauto.
    clear -w HT. now eapply TypingWf.typing_wf in HT. }  
  destruct H as [v' [Hv He]].
  sq.
  set (eΣ := erase_global _ _) in *. exists v'. split => //.
Qed. *)

Obligation Tactic := idtac.

Import Extract.

Definition expanded_eprogram (p : eprogram_env) := 
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpandedFix.isEtaExp_env decls && EEtaExpandedFix.isEtaExp decls [] p.2.

Definition expanded_eprogram_cstrs (p : eprogram_env) := 
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpanded.isEtaExp_env decls && EEtaExpanded.isEtaExp decls p.2.
  
Definition erase_program (p : pcuic_program) (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥) : eprogram_env :=
  erase_pcuic_program p (map_squash fst wtp) (map_squash snd wtp).

Module EtaExpE.
  Import EAst ErasureFunction EEtaExpandedFix EDeps.

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

  Definition global_subset (Σ Σ' : global_declarations) := 
    forall kn d, lookup_env Σ kn = Some d -> lookup_env Σ' kn = Some d.
  
  Lemma lookup_env_In d Σ : 
    wf_glob Σ ->
    lookup_env Σ d.1 = Some d.2 <-> In d Σ.
  Proof.
    intros wf.
    split.
    - induction Σ; cbn => //.
      destruct (eqb_spec d.1 a.1). intros [=]. destruct a, d; cbn in *; intuition auto.
      left; subst; auto. depelim wf.
      intros hl; specialize (IHΣ wf hl); intuition auto.
    - induction wf => /= //.
      intros [eq|hin]; eauto. subst d.
      now rewrite eqb_refl.
      specialize (IHwf hin).
      destruct (eqb_spec d.1 kn). subst kn.
      eapply EExtends.lookup_env_Some_fresh in IHwf. contradiction.
      exact IHwf.
  Qed.

  Lemma global_subset_In Σ Σ' : 
    wf_glob Σ -> wf_glob Σ' ->
    global_subset Σ Σ' <-> forall d, In d Σ -> In d Σ'.
  Proof.
    split.
    - intros g d hin.
      specialize (g d.1 d.2).
      eapply lookup_env_In => //.
      apply g. apply lookup_env_In => //.
    - intros hd kn d hl.
      eapply (lookup_env_In (kn, d)) in hl => //.
      eapply (lookup_env_In (kn, d)) => //. eauto.
  Qed.

  Lemma global_subset_cons d Σ Σ' : 
    global_subset Σ Σ' ->
    global_subset (d :: Σ) (d :: Σ').
  Proof.
    intros sub kn d'.
    cbn. case: eqb_spec => [eq|neq] => //.
    eapply sub.
  Qed.

  Lemma fresh_global_subset Σ Σ' kn : 
    wf_glob Σ -> wf_glob Σ' ->
    global_subset Σ Σ' ->
    fresh_global kn Σ' -> fresh_global kn Σ.
  Proof.
    intros wfΣ wfΣ' sub fr.
    unfold fresh_global in *.
    eapply All_Forall, In_All.
    intros [kn' d] hin. cbn.
    intros eq; subst.
    eapply global_subset_In in hin; tea.
    eapply Forall_All in fr. eapply All_In in fr; tea.
    destruct fr. cbn in H. congruence.
  Qed.

  Lemma global_subset_cons_right d Σ Σ' : 
    wf_glob Σ -> wf_glob (d :: Σ') ->
    global_subset Σ Σ' ->
    global_subset Σ (d :: Σ').
  Proof.
    intros wf wf' gs.
    assert (wf_glob Σ'). now depelim wf'.
    rewrite (global_subset_In _ _ wf H) in gs.
    rewrite global_subset_In //.
    intros decl. specialize (gs decl).
    intros hin; specialize (gs hin). cbn. now right.
  Qed.
    
  Lemma lookup_erase_global (cf := config.extraction_checker_flags) {Σ : wf_env} {deps deps'} :
    KernameSet.Subset deps deps' ->
    global_subset (erase_global deps Σ) (erase_global deps' Σ).
  Proof.
    unfold erase_global.
    destruct Σ as [[[univs Σ] wfΣ G wfG] map repr]. cbn in *. clear G wfG.
    revert deps deps' wfΣ map repr.
    induction Σ. cbn => //.
    intros deps deps' wfΣ map repr sub.
    destruct a as [kn' []]; cbn;
    (set (decl := E.ConstantDecl _) || set (decl := E.InductiveDecl _)); hidebody decl;
    set (eg := erase_global_decls _ _ _ _); hidebody eg;
    set (eg' := erase_global_decls _ _ _ _); hidebody eg';
    try (set (eg'' := erase_global_decls _ _ _ _); hidebody eg'');
    try (set (eg''' := erase_global_decls _ _ _ _); hidebody eg''').
    { destruct (KernameSet.mem) eqn:knm => /=.
      + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
        apply global_subset_cons. eapply IHΣ.
        intros x hin. eapply KernameSet.union_spec in hin.
        eapply KernameSet.union_spec. destruct hin. left. now eapply sub.
        right => //.
      + destruct (KernameSet.mem kn' deps') eqn:eq'.
        eapply global_subset_cons_right.
        eapply ERemoveParams.erase_global_wf_glob.
        constructor. eapply ERemoveParams.erase_global_wf_glob.
        eapply ERemoveParams.erase_global_decls_fresh.
        clear -wfΣ. destruct wfΣ. destruct X as [onu ond]; cbn in *.
        now depelim ond.
        eapply IHΣ.
        intros x hin.
        eapply KernameSet.union_spec. left. now eapply sub.
        eapply IHΣ => //. }
    { destruct (KernameSet.mem) eqn:knm => /=.
      + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
        apply global_subset_cons. eapply IHΣ => //.
      + destruct (KernameSet.mem kn' deps') eqn:eq'.
        eapply global_subset_cons_right. eapply ERemoveParams.erase_global_wf_glob.
        constructor. eapply ERemoveParams.erase_global_wf_glob.
        eapply ERemoveParams.erase_global_decls_fresh.
        clear -wfΣ. destruct wfΣ. destruct X as [onu ond]; cbn in *. now depelim ond.
        eapply IHΣ. intros x hin. now eapply sub.
        eapply IHΣ => //. }
  Qed.
  
  Lemma expanded_weakening_global Σ deps deps' Γ t : 
    KernameSet.Subset deps deps' ->
    expanded (erase_global deps Σ) Γ t ->
    expanded (erase_global deps' Σ) Γ t.
  Proof.
    intros hs.
    eapply expanded_ind; intros; try solve [econstructor; eauto].
    eapply expanded_tConstruct_app; tea.
    destruct H. split; tea.
    destruct d; split => //.
    cbn in *. red in H.
    eapply lookup_erase_global in H; tea.
  Qed.

  Lemma expanded_erase (cf := config.extraction_checker_flags) {Σ : wf_env} univs wfΣ t wtp :
    PCUICEtaExpand.expanded Σ [] t ->
    let Σ' := make_wf_env_ext Σ univs wfΣ in
    let et := (erase Σ' [] t wtp) in
    let deps := EAstUtils.term_global_deps et in
    EEtaExpandedFix.expanded (erase_global deps Σ) [] et.
  Proof.
    intros hexp Σ'.
    have [wf] : ∥ wf Σ ∥.
    { destruct wfΣ. sq. exact w. }
    eapply (expanded_erases (Σ := (Σ, univs))); tea.
    eapply (erases_erase (Σ := Σ')). cbn.
    eapply (erases_deps_erase (Σ := Σ) univs wfΣ).
  Qed.

  Lemma expanded_erase_global (cf := config.extraction_checker_flags) deps {Σ: wf_env} :
    EtaExpPCUIC.expanded_global_env Σ ->
    expanded_global_env (erase_global deps Σ).
  Proof.
    intros etaΣ.
    unfold erase_global.
    destruct Σ as [Σ map repr]. cbn in *.
    destruct Σ as [Σ wfΣ G isG]. cbn in *. clear G isG.
    destruct Σ as [univs Σ]; cbn in *.
    red. revert wfΣ. red in etaΣ. cbn in *.
    revert deps map repr.
    induction etaΣ; intros deps. cbn. constructor.
    destruct decl as [kn []];
    destruct (KernameSet.mem kn deps) eqn:eqkn; simpl; rewrite eqkn.
    constructor; [eapply IHetaΣ; auto|].
    red. cbn. red. cbn in *.
    set (deps' := KernameSet.union _ _). hidebody deps'.
    set (wfext := make_wf_env_ext _ _ _). hidebody wfext.
    destruct H.
    destruct c as [cst_na [cst_body|] cst_type cst_rel].
    cbn in *.
    eapply expanded_weakening_global. 
    2:{ eapply expanded_erase; tea. }
    set (et := erase _ _ _ _) in *.
    unfold deps'. unfold hidebody. intros x hin.    
    eapply KernameSet.union_spec. right => //.
    now cbn.
    intros.
    eapply IHetaΣ.
    intros map repr wfΣ.
    constructor. eapply IHetaΣ.
    red. cbn => //.
    intros map repr wfΣ.
    eapply IHetaΣ.
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

  Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1 -?EEtaExpanded.isEtaExp_equation_1.

  Lemma isEtaExpFix_isEtaExp Σ Γ t : isEtaExp Σ Γ t -> EEtaExpanded.isEtaExp Σ t.
  Proof.
    funelim (isEtaExp Σ Γ t); try solve [simp_eta => //].
    - simp_eta in Heqcall. simp_eta.
      intros Ha. eapply In_All in H. solve_all.
    - simp_eta. rtoProp; intuition auto.
    - simp_eta. rtoProp; intuition auto.
      eapply In_All in H0; solve_all.
    - eapply In_All in H. simp_eta; rtoProp; intuition auto. solve_all.
    - eapply In_All in H. simp_eta; rtoProp; intuition auto.
      move: H0; rewrite isEtaExp_mkApps // /=.
      move=> /andP[] etaind etav.
      rewrite EEtaExpanded.isEtaExp_Constructor. apply/andP; split. exact etaind.
      solve_all.
    - eapply In_All in H, H0. simp_eta in Heqcall.
      clear Heqcall.
      rewrite isEtaExp_mkApps // /= => /andP[] /andP[] etafix etamfix etav.
      eapply EEtaExpanded.isEtaExp_mkApps_intro. simp_eta.
      clear -H etamfix. solve_all.
      solve_all.
    - eapply In_All in H. clear Heqcall.
      rewrite isEtaExp_mkApps // /= => /andP[] etarel etav.
      eapply EEtaExpanded.isEtaExp_mkApps_intro. simp_eta. solve_all.
    - eapply In_All in H0. clear Heqcall.
      rewrite isEtaExp_mkApps // /= Heq => /andP[] etau etav.
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

  Lemma expanded_erase_program (cf := config.extraction_checker_flags) p (wtp : ∥ wt_pcuic_program p ∥) :
    EtaExpPCUIC.expanded_pcuic_program p ->
    expanded_eprogram (erase_program p wtp).
  Proof.
    intros [etaenv etat]. apply /andP; split.
    eapply expanded_global_env_isEtaExp_env, expanded_erase_global, etaenv.
    eapply expanded_isEtaExp, expanded_erase, etat.
  Qed.

End EtaExpE.

Program Definition erase_transform : Transform.t pcuic_program eprogram_env term EAst.term eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥ /\ EtaExpPCUIC.expanded_pcuic_program p ;
    transform p hp := erase_program p (proj1 hp) ;
    post p :=
      let decls := p.1.(global_decls) in
      [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram p];
    obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.
Next Obligation.
  cbn -[erase_program].
  intros p [wtp etap].
  destruct erase_program eqn:e.
  split; cbn.
  - unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
    eapply ERemoveParams.erase_global_wf_glob.
  - apply/andP; split.
    * unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
      eapply ErasureFunction.erase_global_closed.
    * unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
      eapply (ErasureFunction.erases_closed _ []). eapply ErasureFunction.erases_erase.
      clear e. destruct wtp as [[wfΣ [T HT]]].
      now eapply (@PCUICClosedTyp.subject_closed _ _) in HT.
  - rewrite -e. cbn.
    now eapply EtaExpE.expanded_erase_program.
Qed.

Next Obligation.
  red. move=> [Σ t] v [[wf [T HT]]]. unfold eval_pcuic_program, eval_eprogram.
  intros ev.
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  eapply (ErasureFunction.erase_correct Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev; try reflexivity.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev as [v' [he [hev]]]. exists v'; split; split => //.
  red. cbn.
  eexact hev.
Qed.

Import EOptimizePropDiscr.

Program Definition optimize_prop_discr_optimization : self_transform eprogram EAst.term (eval_eprogram EWcbvEval.default_wcbv_flags) (eval_eprogram EWcbvEval.opt_wcbv_flags) := 
  {| name := "optimize_prop_discr"; 
    transform p _ := 
      (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2);
    pre := closed_eprogram;
    post := closed_eprogram;
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v
    |}.

Next Obligation.
  move=> [Σ t] /andP[cle clt].
  cbn in *. apply/andP; split.
  move: cle. cbn. induction Σ at 1 3; cbn; auto.
  move/andP => [] cla clg. rewrite (IHg clg) andb_true_r.
  destruct a as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn in cla |- *.
  now eapply EOptimizePropDiscr.closed_optimize.
  now eapply EOptimizePropDiscr.closed_optimize.
Qed.
Next Obligation.
  red. move=> [Σ t] /= v /andP[cle clt] ev.
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
Qed.

Program Definition remove_params (p : eprogram_env) : eprogram :=
  (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2).

Program Definition remove_params_optimization (fl : EWcbvEval.WcbvFlags) : 
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "remove_parameters";
    transform p pre := remove_params p;
    pre p := 
    let decls := p.1.(global_decls) in
     [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram_cstrs p ];
    post := closed_eprogram;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl [Σ t] [wfe /andP[cle clt] etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  apply/andP; split; cbn.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.

Next Obligation.
  red. move=> ? [Σ t] /= v [wfe /andP[cle clt] etap] ev.
  eapply ERemoveParams.strip_eval in ev; eauto.
  all:move/andP: etap => [] => //.
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "remove_parameters_fast";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := 
      let decls := p.1.(global_decls) in
      [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram_cstrs p];
    post := closed_eprogram;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl [Σ t] [wfe /andP[cle clt] etap].
  simpl.
  apply/andP.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  cbn -[ERemoveParams.strip] in *.
  split.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.
Next Obligation.
  red. move=> ? [Σ t] /= v [wfe /andP[cle clt] etap] ev.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  eapply ERemoveParams.strip_eval in ev; eauto.
  all:move/andP: etap => [] => //.
Qed.

Obligation Tactic := program_simpl.

Program Definition erasure_pipeline := 
  template_eta_expand ▷
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  remove_params_optimization _ ▷ 
  optimize_prop_discr_optimization.

Lemma expanded_eprogram_expanded_eprogram_cstrs p : 
  expanded_eprogram p ->
  expanded_eprogram_cstrs p.
Proof.
  move=> /andP[] etaenv etat.
  apply /andP. split; [now eapply EtaExpE.isEtaExpFix_env_isEtaExp_env|
  now eapply EtaExpE.isEtaExpFix_isEtaExp].
Qed.

Next Obligation.
  destruct H. split => //. now eapply expanded_eprogram_expanded_eprogram_cstrs. 
Qed.

Definition run_erase_program := run erasure_pipeline.

Program Definition erasure_pipeline_fast := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  remove_params_fast_optimization _ ▷ 
  optimize_prop_discr_optimization.
Next Obligation.
  destruct H; split => //. now eapply expanded_eprogram_expanded_eprogram_cstrs. 
Qed.

Definition run_erase_program_fast := run erasure_pipeline_fast.

Local Open Scope string_scope.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)
Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program p (todo "wf_env and welltyped term") in
  time "Pretty printing" EPretty.print_program p'.

Program Definition erase_fast_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program_fast p (todo "wf_env and welltyped term") in
  time "pretty-printing" EPretty.print_program p'.
