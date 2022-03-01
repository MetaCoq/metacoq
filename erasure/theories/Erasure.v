(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph Pretty Environment Typing WcbvEval.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness TemplateToPCUICWcbvEval.
From MetaCoq.PCUIC Require PCUICExpandLets PCUICExpandLetsCorrectness.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr ERemoveParams EWcbvEval EDeps.

#[local] Instance extraction_checker_flags : checker_flags := 
  {| check_univs := true;
     prop_sub_type := false;
     indices_matter := false;
     lets_in_constructor_types := true |}.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Definition eprogram := 
  (EAst.global_context * EAst.term).

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
    { pre : program -> Prop; 
      transform : forall p : program, pre p -> program';
      post : program' -> Prop;
      correctness : forall input (p : pre input), post (transform input p);
      obseq : program -> program' -> value -> value' -> Prop;
      preservation : preserves_eval pre transform obseq; 
      }.

  End Opt.
  Arguments t : clear implicits.

  Section Comp.
    Context {program program' program'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program -> value -> Type}.
    Context {eval' : program' -> value' -> Type}.
    Context {eval'' : program'' -> value'' -> Type}.
    
  Definition compose (o : t program program' value value' eval eval') (o' : t program' program'' value' value'' eval' eval'') :
    (forall p, o.(post) p -> o'.(pre) p) -> t program program'' value value'' eval eval''.
  Proof.
    intros hpp.
    refine {| 
      transform p hp := o'.(transform) (o.(transform) p hp) (hpp _ (o.(correctness) _ hp));
      pre := o.(pre);
      post := o'.(post);
      obseq g g' v v' := exists g'' v'', o.(obseq) g g'' v v'' × o'.(obseq) g'' g' v'' v'
      |}.
    * intros inp pre.
      eapply o'.(correctness).
    * red.
      intros p v pr ev.
      eapply o.(preservation) in ev; auto.
      cbn in ev. destruct ev as [v' [ev]].
      epose proof (o'.(preservation) (o.(transform) p pr) v').
      specialize (H (hpp _ (o.(correctness) _ pr))).
      destruct ev. specialize (H e).
      destruct H as [v'' [[ev' obs']]].
      exists v''. constructor. split => //.
      exists (transform o p pr), v'. now split.
  Defined.
  End Comp.
End Transform.
Import ETyping.

Definition self_optimization program value eval eval' := Transform.t program program value value eval eval'.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) := 
  EWcbvEval.eval (wfl:=wfl) p.1 p.2 t.

Definition optimize_prop_discr_optimization : self_optimization eprogram EAst.term (eval_eprogram EWcbvEval.default_wcbv_flags) (eval_eprogram EWcbvEval.opt_wcbv_flags).
Import Transform.
  refine {|
    transform p _ := (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2);
    pre p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    post p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v
    |}.
  * intros [Σ t] [cle clt].
    cbn in *. split.
    move: cle. induction Σ at 1 3; cbn; auto.
    move/andP => [] cla clg. rewrite (IHg clg) andb_true_r.
    destruct a as [kn []]; cbn in * => //.
    destruct E.cst_body => //. cbn in cla |- *.
    now eapply EOptimizePropDiscr.closed_optimize.
    now eapply EOptimizePropDiscr.closed_optimize.
  * red. move=> [Σ t] /= v [cle clt] ev.
    eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
Defined.

Definition remove_params_optimization (fl : EWcbvEval.WcbvFlags) : self_optimization eprogram EAst.term (eval_eprogram fl) (eval_eprogram fl).
Import Transform.
  refine {|
    transform p _ := (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2);
    pre p := [/\ wf_glob p.1, ERemoveParams.isEtaExp_env p.1, ERemoveParams.isEtaExp p.1 p.2, closed_env p.1 & ELiftSubst.closedn 0 p.2];
    post p := (closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
  * intros [Σ t] [wfe etae etat cle clt].
    cbn -[ERemoveParams.strip] in *. split.
    move: cle. induction Σ at 1 3; cbn; auto.
    move/andP => [] cla clg. rewrite (IHg clg) andb_true_r.
    destruct a as [kn []]; cbn in * => //.
    destruct E.cst_body => //. cbn -[ERemoveParams.strip] in cla |- *.
    now eapply ERemoveParams.closed_strip.
    now eapply ERemoveParams.closed_strip.
  * red. move=> [Σ t] /= v [wfe etae etat cle clt] ev.
    eapply ERemoveParams.strip_eval in ev; eauto.
Defined.

Program Definition erase_template_program (p : Ast.Env.program) 
  (wfΣ : ∥ Typing.wf_ext (Ast.Env.empty_ext p.1) ∥)
  (wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥)
  : eprogram :=
  let Σ0 := (trans_global (Ast.Env.empty_ext p.1)).1 in
  let Σ := (PCUICExpandLets.trans_global_env Σ0) in
  let wfΣ := map_squash (PCUICExpandLetsCorrectness.trans_wf_ext ∘
    (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1))) wfΣ in
  let t := ErasureFunction.erase (build_wf_env_ext (empty_ext Σ) wfΣ) nil (PCUICExpandLets.trans (trans Σ0 p.2)) _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) Σ (sq_wf_ext wfΣ) in
  (Σ', t).
  
Next Obligation.
  sq. destruct wt as [T Ht].
  cbn.
  set (Σ' := empty_ext _).
  exists (PCUICExpandLets.trans (trans (trans_global_env p.1) T)).
  change Σ' with (PCUICExpandLets.trans_global (trans_global (Ast.Env.empty_ext p.1))).
  change (@nil (@BasicAst.context_decl term)) with (PCUICExpandLets.trans_local (trans_local (trans_global_env p.1) [])).
  eapply (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags)).
  apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1));simpl. apply wfΣ0.
  apply Ht. Unshelve. now eapply template_to_pcuic_env.
Defined.

(** The full correctness lemma of erasure from Template programs do λ-box *)

Lemma erase_template_program_correctness {p : Ast.Env.program}
  (Σ := Ast.Env.empty_ext p.1)
  {wfΣ : ∥ Typing.wf_ext Σ ∥}
  {wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥} {Σ' t'} :
  erase_template_program p wfΣ wt = (Σ', t') ->
  forall v, WcbvEval.eval p.1 p.2 v ->
  exists v',
    PCUICExpandLets.trans_global (trans_global Σ) ;;; [] |- 
      PCUICExpandLets.trans (trans (trans_global Σ) v) ⇝ℇ v' /\ 
    ∥ EWcbvEval.eval (wfl:=EWcbvEval.default_wcbv_flags) Σ' t' v' ∥.
Proof.
  unfold erase_template_program.
  intros [= <- <-] v ev.
  pose proof (erase_correct (PCUICExpandLets.trans_global (trans_global Σ))).
  set wftΣ : ∥ wf_ext (PCUICExpandLets.trans_global (trans_global Σ)) ∥ :=
    (map_squash (PCUICExpandLetsCorrectness.trans_wf_ext ∘ template_to_pcuic_env_ext (Ast.Env.empty_ext p.1)) wfΣ).
  specialize (H wftΣ (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) (PCUICExpandLets.trans (trans (trans_global Σ) v))).
  set wtp : PCUICSafeLemmata.welltyped (PCUICExpandLets.trans_global (trans_global Σ)) [] 
    (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) :=
    (erase_template_program_obligation_1 p wfΣ wt).
  set (t' := erase (build_wf_env_ext (empty_ext (PCUICExpandLets.trans_global (trans_global Σ)))
    wftΣ) [] (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) wtp).
  set (deps := (term_global_deps _)).
  change (empty_ext (PCUICExpandLets.trans_global_env (trans_global_env p.1))) with
    (PCUICExpandLets.trans_global (trans_global Σ)) in *.
  specialize (H (erase_global deps (PCUICExpandLets.trans_global (trans_global Σ)) (sq_wf_ext wftΣ))).
  specialize (H _ deps wtp eq_refl).
  forward H. eapply Kernames.KernameSet.subset_spec. reflexivity.
  specialize (H eq_refl).
  destruct wt, wfΣ.
  have wfmid : wf (trans_global (Ast.Env.empty_ext p.1)).1.
  { now eapply template_to_pcuic_env. }
  forward H.
  { eapply PCUICExpandLetsCorrectness.trans_wcbveval.
    { destruct s as [T HT].
      eapply (PCUICClosedTyp.subject_closed (Γ := [])).
      unshelve apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1) [] _ T);simpl; eauto.
      eapply w. }    
    unshelve eapply trans_wcbvEval; eauto.
    destruct s as [T HT].
    clear -w HT. now eapply TypingWf.typing_wf in HT. }  
  destruct H as [v' [Hv He]].
  sq.
  change (empty_ext (trans_global_env p.1)) with (trans_global Σ).
  set (eΣ := erase_global _ _ _) in *. exists v'. split => //.
Qed.

Definition eval_program (p : Ast.Env.program) (v : Ast.term) :=
  WcbvEval.eval p.1 p.2 v.

Definition erase_transform : Transform.t Ast.Env.program eprogram Ast.term EAst.term eval_program (eval_eprogram EWcbvEval.default_wcbv_flags).
Import Transform.
  unshelve refine {|
    pre p :=  
      let Σ := Ast.Env.empty_ext p.1 in
      ∥ Typing.wf_ext Σ × ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥;
    transform p hp := erase_template_program p (map_squash fst hp) (map_squash snd hp) ;
    post p := (wf_glob p.1 /\ closed_env p.1 /\ ELiftSubst.closedn 0 p.2);
    obseq g g' v v' :=
      let Σ := Ast.Env.empty_ext g.1 in
      PCUICExpandLets.trans_global (trans_global Σ) ;;; [] |- 
      PCUICExpandLets.trans (trans (trans_global Σ) v) ⇝ℇ v' /\ 
      ∥ EWcbvEval.eval (wfl:=EWcbvEval.default_wcbv_flags) g'.1 g'.2 v' ∥ |}.
  * intros [Σ t] [[wfext ht]].
    destruct erase_template_program eqn:e.
    unfold erase_template_program in e. simpl. injection e. intros <- <-. split.
    eapply ERemoveParams.erase_global_wf_glob. split.
    eapply erase_global_closed.
    eapply (erases_closed _ []). 2:eapply erases_erase.
    clear e. destruct ht as [T HT].
    unshelve eapply (template_to_pcuic_typing _ []) in HT; eauto.
    unshelve eapply PCUICClosedTyp.subject_closed in HT.
    now eapply template_to_pcuic_env_ext. simpl in HT.
    now eapply PCUICExpandLetsCorrectness.trans_closedn.  
  * red. move=> [Σ t] v [[wf [T HT]]]. unfold eval_program.
    intros ev.
    destruct erase_template_program eqn:e.
    eapply (erase_template_program_correctness) in e; tea.
    destruct e as [v' [he [hev]]]. exists v'; split; split => //.
Defined.

(* Lemma optimize_correctness (o : Transform.t) (p : eprogram) : 
  o.(pre) p ->
  let p' := o.(optimize) p in
  forall v,
    EWcbvEval.eval (wfl:=o.(input_flags)) p.1 p.2 v -> 
    exists v', ∥ EWcbvEval.eval (wfl:=o.(output_flags)) p'.1 p'.2 v' × o.(obseq) p.1 p'.1 v v' ∥.
Proof.
  intros. now eapply o.(preservation).
Qed. *)

Program Definition erasure_pipeline := 
  Transform.compose erase_transform (Transform.compose (remove_params_optimization _) optimize_prop_discr_optimization _) _.
Next Obligation.
  split => //. all:todo "etaexp".
Qed.

Definition erase_program := erasure_pipeline.(transform).

Local Open Scope string_scope.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)
Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let (Σ', t) := erase_program p (todo "wf_env and welltyped term") in
  print_term Σ' [] true false t ^ nl ^ "in:" ^ nl ^ print_global_context Σ'.
