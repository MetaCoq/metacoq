(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph Pretty Environment Typing WcbvEval.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness TemplateToPCUICWcbvEval.
From MetaCoq.PCUIC Require PCUICExpandLets PCUICExpandLetsCorrectness.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr ERemoveParams EWcbvEval EDeps.

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

Import EOptimizePropDiscr.

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
        name := o.(name) ^ " -> " ^ o'.(name);
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

Definition pcuic_program := 
  global_env_ext_map * term.

Definition eval_program (p : Ast.Env.program) (v : Ast.term) :=
  WcbvEval.eval p.1 p.2 v.  
  
Definition eval_pcuic_program (p : pcuic_program) (v : term) :=
  PCUICWcbvEval.eval p.1.(trans_env_env) p.2 v.

Definition template_to_pcuic_obseq (p : Ast.Env.program) (p' : pcuic_program) (v : Ast.term) (v' : term) :=
  let Σ := Ast.Env.empty_ext p.1 in v' = trans (trans_global Σ) v.
  
Program Definition template_to_pcuic_transform {cf : checker_flags} : 
  Transform.t Ast.Env.program pcuic_program Ast.term term 
  eval_program eval_pcuic_program :=
 {| name := "template to pcuic";
    pre p :=  
      let Σ := Ast.Env.empty_ext p.1 in
      ∥ Typing.wf_ext Σ × ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥;
    transform p hp := let Σ' := trans_global (Ast.Env.empty_ext p.1) in 
      (Σ', trans Σ' p.2) ;
    post p := ∥ wf_ext p.1 × ∑ T, typing p.1 [] p.2 T ∥;
    obseq := template_to_pcuic_obseq |}.
Next Obligation.
  intros cf [Σ t] [[wfext ht]].
  set (Σ' := trans_global _).
  cbn. sq. split => //. eapply template_to_pcuic_env_ext. apply wfext.
  destruct ht as [T HT]. exists (trans (trans_global_env Σ) T).
  eapply (template_to_pcuic_typing (Σ := Ast.Env.empty_ext Σ) []). apply wfext.
  apply HT.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program, eval_program.
  cbn. intros ev.
  unshelve eapply TemplateToPCUICWcbvEval.trans_wcbvEval in ev; eauto. apply w.
  eexists; split; split; eauto. red. reflexivity.
  eapply template_to_pcuic_env.
  apply w. destruct s as [T HT]. apply TypingWf.typing_wf in HT. apply HT. auto.
Qed.

Program Definition build_global_env_map (g : global_env) : global_env_map := 
  {| trans_env_env := g; 
     trans_env_map := EnvMap.EnvMap.of_global_env g.(declarations) |}.
Next Obligation.
  intros g. eapply EnvMap.EnvMap.repr_global_env.
Qed.

Import EGlobalEnv.

Definition eprogram := 
  (EAst.global_context * EAst.term).

Import EEnvMap.GlobalContextMap (make, global_decls).

Arguments EWcbvEval.eval {wfl} _ _ _.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) := 
  EWcbvEval.eval (wfl:=wfl) p.1 p.2 t.

Program Definition optimize_prop_discr_optimization : self_transform eprogram EAst.term (eval_eprogram EWcbvEval.default_wcbv_flags) (eval_eprogram EWcbvEval.opt_wcbv_flags) := 
  {| name := "optimize_prop_discr"; 
    transform p _ := 
      (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2);
    pre p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    post p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v
    |}.

Next Obligation.
  intros [Σ t] [cle clt].
  cbn in *. split.
  move: cle. induction Σ at 1 3; cbn; auto.
  move/andP => [] cla clg. rewrite (IHg clg) andb_true_r.
  destruct a as [kn []]; cbn in * => //.
  destruct E.cst_body => //. cbn in cla |- *.
  now eapply EOptimizePropDiscr.closed_optimize.
  now eapply EOptimizePropDiscr.closed_optimize.
Qed.
Next Obligation.
  red. move=> [Σ t] /= v [cle clt] ev.
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
Qed.

Lemma wf_glob_fresh Σ : wf_glob Σ -> EnvMap.EnvMap.fresh_globals Σ.
Proof.
  induction Σ. constructor; auto.
  intros wf; depelim wf. constructor; auto.
Qed.

Definition eprogram_env := 
  (EEnvMap.GlobalContextMap.t * EAst.term).

Definition eval_eprogram_env (wfl : EWcbvEval.WcbvFlags) (p : eprogram_env) (t : EAst.term) := 
  EWcbvEval.eval (wfl:=wfl) p.1.(global_decls) p.2 t.

Program Definition remove_params (p : eprogram_env) : eprogram :=
  (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2).

Program Definition remove_params_optimization (fl : EWcbvEval.WcbvFlags) : 
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "remove_parameters";
    transform p pre := remove_params p;
    pre p := 
    let decls := p.1.(global_decls) in
     [/\ wf_glob decls, EEtaExpanded.isEtaExp_env decls, 
      EEtaExpanded.isEtaExp decls p.2, closed_env decls & ELiftSubst.closedn 0 p.2];
    post p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  intros fl [Σ t] [wfe etae etat cle clt].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.
Next Obligation.
  red. move=> ? [Σ t] /= v [wfe etae etat cle clt] ev.
  eapply ERemoveParams.strip_eval in ev; eauto. 
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "remove_parameters_fast";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := 
      let decls := p.1.(global_decls) in
      [/\ wf_glob decls, EEtaExpanded.isEtaExp_env decls, 
       EEtaExpanded.isEtaExp decls p.2, closed_env decls & ELiftSubst.closedn 0 p.2];
    post p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  intros fl [Σ t] [wfe etae etat cle clt].
  simpl.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  cbn -[ERemoveParams.strip] in *.
  split.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.
Next Obligation.
  red. move=> ? [Σ t] /= v [wfe etae etat cle clt] ev.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  eapply ERemoveParams.strip_eval in ev; eauto.
Qed.


Definition let_expansion_obseq (p : pcuic_program) (p' : pcuic_program) (v : term) (v' : term) :=
  v' = PCUICExpandLets.trans v.

Program Definition pcuic_expand_lets_transform {cf : checker_flags} : 
  self_transform pcuic_program term eval_pcuic_program eval_pcuic_program :=
 {| name := "let expansion in branches/constructors";
    pre p :=
      let Σ : global_env_ext := p.1 in
      ∥ wf_ext Σ × ∑ T, typing Σ nil p.2 T ∥;
    transform p hp := 
      let Σ' := PCUICExpandLets.trans_global p.1 in 
      ((build_global_env_map Σ', p.1.2), PCUICExpandLets.trans p.2) ;
    post p := ∥ wf_ext (H:=PCUICExpandLetsCorrectness.cf' cf) p.1 × 
      ∑ T, typing (H:=PCUICExpandLetsCorrectness.cf' cf) p.1 nil p.2 T ∥;
    obseq := let_expansion_obseq |}.
Next Obligation.
  intros cf [Σ t] [[wfext ht]].
  set (Σ' := PCUICExpandLets.trans_global _).
  cbn. sq. unfold build_global_env_map. unfold global_env_ext_map_global_env_ext. simpl.
  split. eapply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (PCUICExpandLets.trans T).
  eapply (PCUICExpandLetsCorrectness.pcuic_expand_lets Σ []) => //.
  apply wfext. apply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program.
  cbn. intros ev.
  unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ:=Σ)) in ev; eauto.
  eexists; split; split; eauto. red. reflexivity.
  destruct s as [T HT]. now apply PCUICClosedTyp.subject_closed in HT.
Qed.

Obligation Tactic := program_simpl.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ wf Σ ∥) : wf_env := 
  {| wf_env_referenced := {| referenced_impl_env := Σ.(trans_env_env); referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Program Definition erase_pcuic_program (p : pcuic_program) 
  (wfΣ : ∥ wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf _) wfΣ) in
  let wfe' := make_wf_env_ext wfe p.1.2 wfΣ in
  let t := ErasureFunction.erase wfe' nil p.2 _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) wfe in
  (EEnvMap.GlobalContextMap.make Σ' _, t).
  
Next Obligation.
  sq. destruct wt as [T Ht].
  cbn in *. subst. now exists T.
Qed.
Next Obligation.
  unfold erase_global.
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

Program Definition erase_transform : Transform.t pcuic_program eprogram_env term EAst.term eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ wf_ext (H := config.extraction_checker_flags) p.1 × ∑ T, typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥;
    transform p hp := erase_pcuic_program p (map_squash fst hp) (map_squash snd hp) ;
    post p :=
      let decls := p.1.(global_decls) in
      [/\ wf_glob decls, closed_env decls & ELiftSubst.closedn 0 p.2];
    obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.
Next Obligation.
  intros [Σ t] [[wfext ht]].
  destruct erase_pcuic_program eqn:e.
  unfold erase_pcuic_program in e. simpl. injection e. intros <- <-. split.
  eapply ERemoveParams.erase_global_wf_glob.
  eapply erase_global_closed.
  eapply (erases_closed _ []). 2:eapply erases_erase.
  clear e. destruct ht as [T HT].
  now eapply (@PCUICClosedTyp.subject_closed _ _) in HT.
Qed.
Next Obligation.
  red. move=> [Σ t] v [[wf [T HT]]]. unfold eval_pcuic_program, eval_eprogram.
  intros ev.
  destruct erase_pcuic_program eqn:e.
  unfold erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  (* assert (wt : PCUICSafeLemmata.welltyped (cf:=config.extraction_checker_flags) Σ [] t). now exists T. *)
  eapply (erase_correct Σ' Σ.2 _ _ _ _ _ (term_global_deps _)) in ev; try reflexivity.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev as [v' [he [hev]]]. exists v'; split; split => //.
  red. cbn.
  eexact hev.
Qed.

Obligation Tactic := program_simpl.

Local Notation " o ▷ o' " := (Transform.compose o o' _) (at level 50, left associativity).

Program Definition erasure_pipeline := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  remove_params_optimization _ ▷ 
  optimize_prop_discr_optimization.

Next Obligation.
  destruct H. split => //. all:todo "etaexp".
Qed.

Definition erase_program := run erasure_pipeline.

Program Definition erasure_pipeline_fast := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  remove_params_fast_optimization _ ▷ 
  optimize_prop_discr_optimization.
Next Obligation.
  destruct H; split => //. all:todo "etaexp".
Qed.

Definition erase_program_fast := run erasure_pipeline_fast.

Local Open Scope string_scope.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)
Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := erase_program p (todo "wf_env and welltyped term") in
  time "Pretty printing" print_program p'.

Program Definition erase_fast_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := erase_program_fast p (todo "wf_env and welltyped term") in
  time "pretty-printing" print_program p'.
