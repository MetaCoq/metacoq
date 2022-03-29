(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import bytestring config utils BasicAst uGraph.
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

(* Used to show timings of the ML execution *)
 
Definition time : forall {A B}, string -> (A -> B) -> A -> B :=
  fun A B s f x => f x.

Extract Constant time => 
  "(fun c f x -> let s = Caml_bytestring.caml_string_of_bytestring c in Tm_util.time (Pp.str s) f x)".

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Module Transform.
  Section Opt.
     Context {program program' : Type}.
     Context {value value' : Type}.
     Context {eval :  program -> value -> Type}.
     Context {eval' : program' -> value' -> Type}.
     
     Definition preserves_eval pre (transform : forall p : program, pre p -> program') obseq :=
      forall p v (pr : pre p),
        eval p v ->
        let p' := transform p pr in
        exists v',
        ∥ eval' p' v' × obseq p p' v v' ∥.

    Record t := 
    { name : string; 
      pre : program -> Prop; 
      transform : forall p : program, pre p -> program';
      post : program' -> Prop;
      correctness : forall input (p : pre input), post (transform input p);
      obseq : program -> program' -> value -> value' -> Prop;
      preservation : preserves_eval pre transform obseq; }.

    Definition run (x : t) (p : program) (pr : pre x p) : program' := 
      time x.(name) (fun _ => x.(transform) p pr) tt.

  End Opt.
  Arguments t : clear implicits.

  Section Comp.
    Context {program program' program'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program -> value -> Type}.
    Context {eval' : program' -> value' -> Type}.
    Context {eval'' : program'' -> value'' -> Type}.
    
    Obligation Tactic := idtac.
    Program Definition compose (o : t program program' value value' eval eval') (o' : t program' program'' value' value'' eval' eval'') 
      (hpp : (forall p, o.(post) p -> o'.(pre) p)) : t program program'' value value'' eval eval'' :=
      {| 
        name := (o.(name) ^ " -> " ^ o'.(name))%bs;
        transform p hp := run o' (run o p hp) (hpp _ (o.(correctness) _ hp));
        pre := o.(pre);
        post := o'.(post);
        obseq g g' v v' := exists g'' v'', o.(obseq) g g'' v v'' × o'.(obseq) g'' g' v'' v'
        |}.
    Next Obligation.
      intros o o' hpp inp pre.
      eapply o'.(correctness).
    Qed.
    Next Obligation.
      red. intros o o' hpp.
      intros p v pr ev.
      eapply o.(preservation) in ev; auto.
      cbn in ev. destruct ev as [v' [ev]].
      epose proof (o'.(preservation) (o.(transform) p pr) v').
      specialize (H (hpp _ (o.(correctness) _ pr))).
      destruct ev. specialize (H e).
      destruct H as [v'' [[ev' obs']]].
      exists v''. constructor. split => //.
      exists (transform o p pr), v'. now split.
    Qed.
  End Comp.
End Transform.

Import Transform.
Obligation Tactic := idtac.

Definition self_transform program value eval eval' := Transform.t program program value value eval eval'.

Definition template_program := Ast.Env.program.

Definition wt_template_program {cf : checker_flags} (p : template_program) :=
  let Σ := Ast.Env.empty_ext p.1 in
  Template.Typing.wf_ext Σ × ∑ T, Typing.typing Σ [] p.2 T.

Definition eval_template_program (p : Ast.Env.program) (v : Ast.term) :=
  WcbvEval.eval p.1 p.2 v.  

Definition template_expand_obseq (p p' : template_program) (v v' : Ast.term) :=
  v' = EtaExpand.eta_expand p.1.(Ast.Env.declarations) [] v.
  
Module EtaExpTemplate.
  Import Ast.Env EtaExpand.
  Definition eta_expand_global_env g := 
    {| Ast.Env.universes := g.(Ast.Env.universes); 
      Ast.Env.declarations := eta_global_env g.(Ast.Env.declarations) |}.

  Record expanded_constant_decl Σ (cb : Ast.Env.constant_body) : Prop :=
    { expanded_body : on_Some_or_None (expanded Σ []) cb.(Ast.Env.cst_body);
      expanded_type := expanded Σ [] cb.(Ast.Env.cst_type) }.
      
  Definition expanded_decl Σ d :=
    match d with
    | Ast.Env.ConstantDecl cb => expanded_constant_decl Σ cb
    | Ast.Env.InductiveDecl idecl => True
    end.
      
  Inductive expanded_global_declarations (univs : ContextSet.t) : forall (Σ : Ast.Env.global_declarations), Prop :=
  | expanded_global_nil : expanded_global_declarations univs []
  | expanded_global_cons decl Σ : expanded_global_declarations univs Σ -> 
    expanded_decl {| Ast.Env.universes := univs; Ast.Env.declarations := Σ |} decl.2 ->
    expanded_global_declarations univs (decl :: Σ).

  Definition expanded_global_env (g : Ast.Env.global_env) :=
    expanded_global_declarations g.(Ast.Env.universes) g.(Ast.Env.declarations).

  Lemma expanded_irrel_global_env {Σ Σ' Γ t} :   
    (* missing condition: same observations of constructor arguments lengths etc *)
    expanded Σ Γ t -> expanded Σ' Γ t.
  Admitted.

  Lemma eta_expand_global_env_expanded {cf : checker_flags} g :
    Typing.wf g ->
    expanded_global_env (eta_expand_global_env g).
  Proof.
    destruct g as [univs Σ]; cbn.
    unfold expanded_global_env, eta_expand_global_env; cbn.
    unfold Typing.wf, Typing.on_global_env. intros [onu ond].
    cbn in *.
    induction ond; try constructor.
    destruct d as []; cbn; try constructor; auto. 1,3:todo "weakening of eta expansion".
    all:red; cbn => //.
    do 2 red in o0.
    split; cbn. destruct (Ast.Env.cst_body) => /= //.
    set (Σ' := {| universes := univs; |}).
    epose proof (eta_expand_expanded (Σ := Ast.Env.empty_ext Σ') [] [] t0 (Env.cst_type c)).
    cbn in H.
    do 2 (forward H; [todo "eta-expansion preserves well-formedness of global environments"|]).
    forward H by constructor.
    todo "weakening of eta expansion".
  Qed.

  Definition expanded_template_program (p : Ast.Env.program) :=
    expanded_global_env p.1 /\ expanded p.1 [] p.2.
End EtaExpTemplate.

Definition eta_expand_program (p : template_program) : template_program :=
  let Σ' := EtaExpTemplate.eta_expand_global_env p.1 in 
  (Σ', EtaExpand.eta_expand p.1.(Ast.Env.declarations) [] p.2).

Program Definition template_eta_expand {cf : checker_flags} : self_transform template_program Ast.term eval_template_program eval_template_program :=
 {| name := "eta-expansion of template program";
    pre p := ∥ wt_template_program p ∥;
    transform p _ := eta_expand_program p;
    post p := ∥ wt_template_program p ∥ /\ EtaExpTemplate.expanded_template_program p;
    obseq := template_expand_obseq |}.
Next Obligation.
  intros cf [Σ t] [[wfext ht]].
  cbn. split. split. todo "eta-expansion preserves wf ext and typing".
  red.
  destruct ht as [T ht].
  split; cbn. eapply EtaExpTemplate.eta_expand_global_env_expanded. apply wfext.
  eapply EtaExpTemplate.expanded_irrel_global_env.
  epose proof (EtaExpand.eta_expand_expanded (Σ := Ast.Env.empty_ext Σ) [] [] t T).
  forward H. apply wfext. specialize (H ht).
  forward H by constructor. exact H.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_template_program.
  cbn. intros ev.
  exists (EtaExpand.eta_expand (Ast.Env.declarations Σ) [] v). split. split.
  todo "eta-expansion preserves evaluation".
  red. reflexivity.
Qed.

Import PCUICAstUtils PCUICAst TemplateToPCUIC PCUICGlobalEnv PCUICTyping.

Definition pcuic_program : Type := global_env_ext_map * term.
  
Definition wt_pcuic_program {cf : checker_flags} (p : pcuic_program) :=
  wf_ext p.1 × ∑ T, typing p.1 [] p.2 T.

Definition eval_pcuic_program (p : pcuic_program) (v : term) :=
  PCUICWcbvEval.eval p.1.(trans_env_env) p.2 v.

Definition template_to_pcuic_obseq (p : Ast.Env.program) (p' : pcuic_program) (v : Ast.term) (v' : term) :=
  let Σ := Ast.Env.empty_ext p.1 in v' = trans (trans_global Σ) v.

Definition trans_template_program (p : template_program) : pcuic_program :=
  let Σ' := trans_global (Ast.Env.empty_ext p.1) in 
  (Σ', trans Σ' p.2).

Import Transform TemplateToPCUICCorrectness.

Module EtaExpPCUIC.
  Import PCUICAst.PCUICEnvironment PCUICEtaExpand TemplateToPCUIC TemplateToPCUICExpanded TemplateToPCUICCorrectness.

  Record expanded_constant_decl Σ (cb : constant_body) : Prop :=
    { expanded_body : on_Some_or_None (expanded Σ []) cb.(cst_body);
      expanded_type := expanded Σ [] cb.(cst_type) }.
      
  Definition expanded_decl Σ d :=
    match d with
    | ConstantDecl cb => expanded_constant_decl Σ cb
    | InductiveDecl idecl => True
    end.
      
  Inductive expanded_global_declarations (univs : ContextSet.t) : forall (Σ : global_declarations), Prop :=
  | expanded_global_nil : expanded_global_declarations univs []
  | expanded_global_cons decl Σ : expanded_global_declarations univs Σ -> 
    expanded_decl {| universes := univs; declarations := Σ |} decl.2 ->
    expanded_global_declarations univs (decl :: Σ).

  Definition expanded_global_env (g : global_env) :=
    expanded_global_declarations g.(universes) g.(declarations).

  Arguments trans_global_env : simpl never.
  Lemma expanded_trans_global_env {cf : checker_flags} {Σ} {wfΣ : Template.Typing.wf Σ} :
    EtaExpTemplate.expanded_global_env Σ ->
     let Σ' := trans_global_env Σ in
    expanded_global_env Σ'.(trans_env_env).
  Proof.
    destruct Σ as [univs Σ]; cbn -[trans_global_env].
    unfold expanded_global_env, EtaExpTemplate.expanded_global_env; cbn -[trans_global_env].
    intros hexp; induction hexp. cbn. constructor; auto.
    depelim wfΣ. cbn in *. simpl in *.
    depelim o0.  
    forward IHhexp. split. apply o. now cbn.
    constructor => //.
    red.
    red in o2.
    cbn. destruct d => /= //.
    cbn in *. move: H.
    intros []; split => //. cbn in *. red in o2.
    destruct (Ast.Env.cst_body c); cbn in *; auto.
    unshelve eapply trans_expanded in expanded_body0; tc. red. red. split => //.
    cbn in *.
    set (Σ' := trans_env_env (trans_global_env _)) in *.
    set (Σ'' := {| universes := _ |}).
    assert (Σ' = Σ'').
    eapply env_eq; reflexivity. rewrite -H //.
    eapply TypingWf.typing_wf in o2 as [] => //.
  Qed.

  Definition expanded_pcuic_program (p : pcuic_program) :=
    expanded_global_env p.1 /\ expanded p.1 [] p.2.

  Lemma expanded_trans_program {cf : checker_flags} p (t : wt_template_program p) :
    EtaExpTemplate.expanded_template_program p ->
    expanded_pcuic_program (trans_template_program p).
  Proof.
    intros [etaenv etat].
    destruct t as [? [T HT]]. split.
    unshelve eapply expanded_trans_global_env => //; tc. apply w.
    unshelve eapply trans_expanded => //; tc. eapply w.
    now unshelve eapply TypingWf.typing_wf in HT.
  Qed.

End EtaExpPCUIC.

Lemma trans_template_program_wt {cf : checker_flags} p (wtp : wt_template_program p) : wt_pcuic_program (trans_template_program p).
Proof.
  move: p wtp.
  intros [Σ t] [wfext ht].
  unfold wt_pcuic_program, trans_template_program; cbn in *.
  cbn. split. eapply template_to_pcuic_env_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (trans (trans_global_env Σ) T).
  eapply (template_to_pcuic_typing (Σ := Ast.Env.empty_ext Σ) []). apply wfext.
  apply HT.
Qed.

Program Definition template_to_pcuic_transform {cf : checker_flags} : 
  Transform.t template_program pcuic_program Ast.term term 
  eval_template_program eval_pcuic_program :=
 {| name := "template to pcuic";
    pre p := ∥ wt_template_program p ∥ /\ EtaExpTemplate.expanded_template_program p ;
    transform p _ := trans_template_program p ;
    post p := ∥ wt_pcuic_program p ∥ /\ EtaExpPCUIC.expanded_pcuic_program p;
    obseq := template_to_pcuic_obseq |}.
Next Obligation.
  cbn. intros cf p [[wtp] etap].
  split; [split|].
  now eapply trans_template_program_wt.
  now eapply EtaExpPCUIC.expanded_trans_program in etap.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program, eval_template_program.
  cbn. intros ev.
  unshelve eapply TemplateToPCUICWcbvEval.trans_wcbvEval in ev; eauto. apply X.
  eexists; split; split; eauto. red. reflexivity.
  eapply template_to_pcuic_env.
  apply X. destruct X as [wfΣ [T HT]]. apply TypingWf.typing_wf in HT. apply HT. auto.
Qed.

Program Definition build_global_env_map (g : global_env) : global_env_map := 
  {| trans_env_env := g; 
     trans_env_map := EnvMap.EnvMap.of_global_env g.(declarations) |}.
Next Obligation.
  intros g. eapply EnvMap.EnvMap.repr_global_env.
Qed.

Definition let_expansion_obseq (p : pcuic_program) (p' : pcuic_program) (v : term) (v' : term) :=
  v' = PCUICExpandLets.trans v.

Definition expand_lets_program (p : pcuic_program) :=
  let Σ' := PCUICExpandLets.trans_global p.1 in 
  ((build_global_env_map Σ', p.1.2), PCUICExpandLets.trans p.2).

Import PCUICEtaExpand PCUICExpandLets PCUICExpandLetsCorrectness.

Lemma trans_isConstruct t : isConstruct t = isConstruct (trans t).
Proof. destruct t => //. Qed.
Lemma trans_isRel t : isRel t = isRel (trans t).
Proof. destruct t => //. Qed.
Lemma trans_isFix t : isFix t = isFix (trans t).
Proof. destruct t => //. Qed.

Lemma expanded_expand_lets {Σ : global_env} Γ t : PCUICEtaExpand.expanded Σ Γ t -> PCUICEtaExpand.expanded (PCUICExpandLets.trans_global_env Σ) Γ (PCUICExpandLets.trans t).
Proof.
  induction 1 using PCUICEtaExpand.expanded_ind; cbn.
  all:try constructor; auto.
  - rewrite trans_mkApps /=. eapply expanded_tRel; tea. now len. solve_all.
  - solve_all.
  - rewrite trans_mkApps. constructor; eauto; [|solve_all].
    now rewrite -trans_isConstruct -trans_isRel -trans_isFix.
  - do 2 eapply Forall_map. repeat toAll. eapply All_impl; tea. cbn.
    intros x [expb IH].
    rewrite trans_bcontext trans_bbody. len; cbn. rewrite /id.
    todo "needs a lemma".
  - rewrite trans_mkApps. cbn. eapply expanded_tFix. solve_all.
    rewrite rev_map_spec. rewrite rev_map_spec in b.
    rewrite map_map_compose. cbn. exact b. solve_all.
    destruct args => //. now rewrite nth_error_map H4. len. now cbn.
  - solve_all.
  - rewrite trans_mkApps; eapply expanded_tConstruct_app.
    eapply (trans_declared_constructor (empty_ext Σ)) in H; tea. len.
    cbn. now rewrite context_assumptions_smash_context context_assumptions_map /=.
    solve_all.
Qed.
    
Lemma expanded_expand_lets_program {cf : checker_flags} p (wtp : wt_pcuic_program p) :
  EtaExpPCUIC.expanded_pcuic_program p ->
  EtaExpPCUIC.expanded_pcuic_program (expand_lets_program p).
Proof.
  destruct p as [[Σ udecl] t]; intros [etaenv etat].
  destruct wtp as [? [T HT]]. split.
  cbn in *. destruct Σ as [[univs env] map repr]; cbn in *.
  destruct w; cbn in *. clear T HT. red in o; cbn in *.
  red in etaenv; cbn in *. clear etat. red. cbn.
  { destruct o. clear o o0 map repr.
    induction etaenv; cbn; constructor; auto. depelim o1; eauto.
    destruct decl as [kn []]; cbn in *; depelim H => //.
    unfold PCUICExpandLets.trans_constant_body; cbn. constructor. cbn.
    destruct (cst_body c); cbn => //. cbn in expanded_body.
    now eapply expanded_expand_lets in expanded_body. }
  cbn in *.
  now eapply expanded_expand_lets in etat.
Qed.

Program Definition pcuic_expand_lets_transform {cf : checker_flags} : 
  self_transform pcuic_program term eval_pcuic_program eval_pcuic_program :=
 {| name := "let expansion in branches/constructors";
    pre p := ∥ wt_pcuic_program p ∥ /\ EtaExpPCUIC.expanded_pcuic_program p ;
    transform p hp := expand_lets_program p;
    post p := ∥ wt_pcuic_program (cf:=PCUICExpandLetsCorrectness.cf' cf) p ∥ /\ EtaExpPCUIC.expanded_pcuic_program p;
    obseq := let_expansion_obseq |}.
Next Obligation.
  intros cf [Σ t] [[[wfext ht]] etap].
  cbn. split. sq. unfold build_global_env_map. unfold global_env_ext_map_global_env_ext. simpl.
  split. eapply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (PCUICExpandLets.trans T).
  eapply (PCUICExpandLetsCorrectness.pcuic_expand_lets Σ []) => //.
  apply wfext. apply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  now eapply expanded_expand_lets_program.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program.
  cbn. intros ev. destruct X.
  eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ:=global_env_ext_map_global_env_ext Σ)) in ev.
  eexists; split; split; eauto. red. reflexivity.
  destruct s as [T HT]. now apply PCUICClosedTyp.subject_closed in HT.
Qed.

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

Local Notation " o ▷ o' " := (Transform.compose o o' _) (at level 50, left associativity).

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
