(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.

From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
     
From MetaCoq.Erasure Require Import EAstUtils EArities Extract Prelim ErasureCorrectness EDeps EExtends
    ErasureFunction ELiftSubst ECSubst EWcbvEval.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors Ee.eval : core.

Set Warnings "-notation-overridden".
Import E.
Set Warnings "+notation-overridden".

Section optimize.
  Context (Σ : global_context).

  Fixpoint optimize (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map optimize args)
    | tLambda na M => tLambda na (optimize M)
    | tApp u v => tApp (optimize u) (optimize v)
    | tLetIn na b b' => tLetIn na (optimize b) (optimize b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd optimize) brs in
      match EGlobalEnv.inductive_isprop_and_pars Σ (fst ind) with
      | Some (true, npars) =>
        match brs' with
        | [(a, b)] => ECSubst.substl (repeat E.tBox #|a|) b
        | _ => E.tCase ind (optimize c) brs'
        end
      | _ => E.tCase ind (optimize c) brs'
      end
    | tProj p c =>
      match EGlobalEnv.inductive_isprop_and_pars Σ p.1.1 with 
      | Some (true, _) => tBox
      | _ => tProj p (optimize c)
      end
    | tFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def optimize) mfix in
      tCoFix mfix' idx
    | tBox => t
    | tVar _ => t
    | tConst _ => t
    | tConstruct _ _ => t
    (* | tPrim _ => t *)
    end.

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof.
    now induction n; simpl; auto; rewrite IHn.
  Qed.
  
  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof. by rewrite map_repeat. Qed.

  Import ECSubst.

  Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
  Proof.
    induction l using rev_ind; simpl; auto.
    rewrite mkApps_app /= IHl.
    now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
  Qed.

  Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
  Proof.
    induction x in k |- * using EInduction.term_forall_list_ind; simpl; auto.
    all:try solve [intros; f_equal; solve_all; eauto].
    intros Hn. eapply Nat.ltb_lt in Hn.
    - destruct (Nat.compare_spec k n); try lia. reflexivity.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
    - move/andP => []. intros. f_equal; solve_all; eauto.
      destruct x0; cbn in *. f_equal; auto.
  Qed.


  Lemma closed_optimize t k : closedn k t -> closedn k (optimize t).
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - move/andP: H => [] clt cll. destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      rewrite IHt //.
      depelim X. cbn in *.
      rewrite andb_true_r in cll.
      specialize (i _ cll).
      eapply closed_substl. solve_all. eapply All_repeat => //.
      now rewrite repeat_length.
      rtoProp; solve_all. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      depelim cll. depelim cll. solve_all.
      rtoProp; solve_all. solve_all.
      rtoProp; solve_all. solve_all.
    - destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|]; cbn; auto.
  Qed.
 
  Lemma subst_csubst_comm l t k b : 
    forallb (closedn 0) l -> closed t ->
    subst l 0 (csubst t (#|l| + k) b) = 
    csubst t k (subst l 0 b).
  Proof.
    intros hl cl.
    rewrite !closed_subst //.
    rewrite distr_subst. f_equal.
    symmetry. solve_all.
    rewrite subst_closed //.
    eapply closed_upwards; tea. lia. 
  Qed.

  Lemma substl_subst s t : 
    forallb (closedn 0) s ->
    substl s t = subst s 0 t.
  Proof.
    induction s in t |- *; cbn; auto.
    intros _. now rewrite subst_empty.
    move/andP=> []cla cls.
    rewrite (subst_app_decomp [_]).
    cbn. rewrite lift_closed //.
    rewrite closed_subst //. now eapply IHs.
  Qed.

  Lemma substl_csubst_comm l t k b : 
    forallb (closedn 0) l -> closed t ->
    substl l (csubst t (#|l| + k) b) = 
    csubst t k (substl l b).
  Proof.
    intros hl cl.
    rewrite substl_subst //.
    rewrite substl_subst //.
    apply subst_csubst_comm => //.
  Qed.

  Lemma optimize_csubst a k b : 
    closed a ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n)%nat; auto.
    - unfold on_snd; cbn.
      destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      * f_equal; auto.
      * depelim X. simpl in *.
        rewrite e //.
        assert (#|br| = #|repeat tBox #|br| |). now rewrite repeat_length.
        rewrite {2}H0.
        rewrite substl_csubst_comm //.
        solve_all. eapply All_repeat => //.
        now eapply closed_optimize.
      * depelim X. depelim X.
        f_equal; eauto. f_equal; eauto.
        f_equal; eauto.
        f_equal; eauto. f_equal; eauto.
        rewrite map_map_compose; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
    - destruct EGlobalEnv.inductive_isprop_and_pars as [[[|] _]|]=> //;
      now rewrite IHb.
  Qed.

  Lemma optimize_substl s t : 
    forallb (closedn 0) s ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof.
    induction s in t |- *; simpl; auto.
    move/andP => [] cla cls.
    rewrite IHs //. f_equal.
    now rewrite optimize_csubst.
  Qed.

  Lemma optimize_iota_red pars args br :
    forallb (closedn 0) args ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof.
    intros cl.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.
  
  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof.
    unfold EGlobalEnv.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof.
    unfold EGlobalEnv.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.fix_subst mfix) ->
    Ee.cunfold_fix mfix idx = Some (n, f) ->
    Ee.cunfold_fix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof.
    intros hfix.
    unfold Ee.cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_fix_subst.
    discriminate.
  Qed.

  Lemma optimize_cunfold_cofix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.cofix_subst mfix) ->
    Ee.cunfold_cofix mfix idx = Some (n, f) ->
    Ee.cunfold_cofix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof.
    intros hcofix.
    unfold Ee.cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_cofix_subst.
    discriminate.
  Qed.

  Lemma optimize_nth {n l d} : 
    optimize (nth n l d) = nth n (map optimize l) (optimize d).
  Proof.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End optimize.


Lemma is_box_inv b : is_box b -> ∑ args, b = mkApps tBox args.
Proof.
  unfold is_box, EAstUtils.head.
  destruct decompose_app eqn:da.
  simpl. destruct t => //.
  eapply decompose_app_inv in da. subst.
  eexists; eauto.
Qed.

Lemma eval_is_box {wfl:Ee.WcbvFlags} Σ t u : Σ ⊢ t ▷ u -> is_box t -> u = EAst.tBox.
Proof.
  intros ev; induction ev => //.
  - rewrite is_box_tApp.
    intros isb. intuition congruence.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?. subst => //.
  - rewrite is_box_tApp. move/IHev1 => ?. subst. cbn in i.
    destruct EWcbvEval.with_guarded_fix => //.
  - destruct t => //.
Qed. 

Lemma isType_tSort {cf:checker_flags} {Σ : global_env_ext} {Γ l A} {wfΣ : wf Σ} : Σ ;;; Γ |- tSort (Universe.make l) : A -> isType Σ Γ (tSort (Universe.make l)).
Proof.
  intros HT.
  eapply inversion_Sort in HT as [l' [wfΓ Hs]]; auto.
  eexists; econstructor; eauto.
Qed.

Lemma isType_it_mkProd {cf:checker_flags} {Σ : global_env_ext} {Γ na dom codom A} {wfΣ : wf Σ} :   
  Σ ;;; Γ |- tProd na dom codom : A -> 
  isType Σ Γ (tProd na dom codom).
Proof.
  intros HT.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto.
  eexists; econstructor; eauto.
Qed.

Lemma erasable_tBox_value (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t T v :
  forall wt : Σ ;;; [] |- t : T,
  Σ |-p t ▷ v -> erases Σ [] v tBox -> ∥ isErasable Σ [] t ∥.
Proof.
  intros.
  depind H.
  eapply Is_type_eval_inv; eauto. eexists; eauto.
Qed.

Lemma erase_eval_to_box (wfl := Ee.default_wcbv_flags) {Σ : wf_env} {univs wfext t v Σ' t' deps} :
  let Σext := make_wf_env_ext Σ univs wfext in
  forall wt : ∀ Σ0 : global_env_ext, abstract_env_rel' Σext Σ0 →  welltyped Σ0 [] t,
  erase Σext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' tBox -> ∥ isErasable Σext [] t ∥.
Proof.
  intros Σext wt.
  intros.
  destruct (erase_correct Σ univs wfext _ _ _ _ _ wt H H0 H1 X) as [ev [eg [eg']]].
  pose proof (Ee.eval_deterministic H2 eg'). subst.
  destruct wfext. destruct (wt _ eq_refl) as [T wt'].
  eapply erasable_tBox_value; eauto.
Qed.

Definition optimize_constant_decl Σ cb := 
  {| cst_body := option_map (optimize Σ) cb.(cst_body) |}.
  
Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (optimize_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Definition optimize_env (Σ : EAst.global_declarations) := 
  map (on_snd (optimize_decl Σ)) Σ.

Import EGlobalEnv.

(* Lemma optimize_extends Σ Σ' : extends Σ Σ' ->
  optimize Σ t = optimize Σ' t. *)

Lemma lookup_env_optimize Σ kn : 
  lookup_env (optimize_env Σ) kn = 
  option_map (optimize_decl Σ) (lookup_env Σ kn).
Proof.
  unfold optimize_env.
  induction Σ at 2 4; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma is_propositional_optimize Σ ind : 
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (optimize_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars.
  rewrite lookup_env_optimize.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto.
Qed.

Lemma closed_iota_red pars c args brs br :
  forallb (closedn 0) args ->
  nth_error brs c = Some br ->
  #|skipn pars args| = #|br.1| ->
  closedn #|br.1| br.2 ->
  closed (iota_red pars args br).
Proof.
  intros clargs hnth hskip clbr.
  rewrite /iota_red.
  eapply ECSubst.closed_substl => //.
  now rewrite forallb_rev forallb_skipn.
  now rewrite List.rev_length hskip Nat.add_0_r.
Qed.

Definition disable_prop_cases fl := {| with_prop_case := false; with_guarded_fix := fl.(@with_guarded_fix) |}.

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma optimize_correct {fl} Σ t v :
  closed_env Σ ->
  @Ee.eval fl Σ t v ->
  closed t ->
  @Ee.eval (disable_prop_cases fl) (optimize_env Σ) (optimize Σ t) (optimize Σ v).
Proof.
  intros clΣ ev.
  induction ev; simpl in *.

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla.
    eapply eval_closed in ev2; tea.
    eapply eval_closed in ev1; tea.
    econstructor; eauto.
    rewrite optimize_csubst // in IHev3.
    apply IHev3. eapply closed_csubst => //.

  - move/andP => [] clb0 clb1. rewrite optimize_csubst in IHev2.
    now eapply eval_closed in ev1.
    econstructor; eauto. eapply IHev2, closed_csubst => //.
    now eapply eval_closed in ev1.

  - move/andP => [] cld clbrs. rewrite optimize_mkApps in IHev1.
    have := (eval_closed _ clΣ _ _ cld ev1); rewrite closedn_mkApps => /andP[] _ clargs.
    rewrite optimize_iota_red in IHev2.
    eapply eval_closed in ev1 => //.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[]|]eqn:isp => //. noconf e.
    eapply Ee.eval_iota; eauto.
    now rewrite -is_propositional_optimize.
    rewrite nth_error_map e0 //. now len.
    eapply IHev2.
    eapply closed_iota_red => //; tea.
    eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
    now rewrite Nat.add_0_r in clbrs.
  
  - move/andP => [] cld clbrs. rewrite e e0 /=.
    subst brs. cbn in clbrs. rewrite Nat.add_0_r andb_true_r in clbrs.
    rewrite optimize_substl in IHev2. 
    eapply All_forallb, All_repeat => //.
    rewrite map_optimize_repeat_box in IHev2.
    apply IHev2.
    eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length Nat.add_0_r.

  - move/andP => [] clf cla. rewrite optimize_mkApps in IHev1.
    simpl in *.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply Ee.eval_fix; eauto.
    rewrite map_length.
    eapply optimize_cunfold_fix; tea.
    eapply closed_fix_subst. tea.
    rewrite optimize_mkApps in IHev3. apply IHev3.
    rewrite closedn_mkApps clargs.
    eapply eval_closed in ev2; tas. rewrite ev2 /= !andb_true_r.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    rewrite closedn_mkApps in ev1.
    move: ev1 => /andP [] clfix clargs.
    eapply eval_closed in ev2; tas.
    rewrite optimize_mkApps in IHev1 |- *.
    simpl in *. eapply Ee.eval_fix_value. auto. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    now rewrite map_length. 
  
  - move/andP => [] clf cla.
    eapply eval_closed in ev1 => //.
    eapply eval_closed in ev2; tas.
    simpl in *. eapply Ee.eval_fix'. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    eapply IHev2; tea. eapply IHev3.
    apply/andP; split => //.
    eapply closed_cunfold_fix; tea.

  - move/andP => [] cd clbrs. specialize (IHev1 cd).
    rewrite closedn_mkApps in IHev2.
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps.
    move/andP => [] clfix clargs.
    forward IHev2.
    { rewrite clargs clbrs !andb_true_r.
      eapply closed_cunfold_cofix; tea. }
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp => //.
    destruct brs as [|[a b] []]; simpl in *; auto.
    simpl in IHev1.
    eapply Ee.eval_cofix_case. tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    apply IHev2.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    simpl in *.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    eapply Ee.eval_cofix_case; tea.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    
  - intros cd. specialize (IHev1 cd).
    move: (eval_closed _ clΣ _ _ cd ev1).
    rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev2.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp; auto.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
  
  - econstructor. red in isdecl |- *.
    rewrite lookup_env_optimize isdecl //.
    now rewrite /optimize_constant_decl e.
    apply IHev.
    eapply lookup_env_closed in clΣ; tea.
    move: clΣ. rewrite /closed_decl e //.
  
  - move=> cld.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps /= => clargs.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars']|] eqn:isp => //.
    rewrite optimize_mkApps in IHev1.
    rewrite optimize_nth in IHev2.
    specialize (IHev1 cld).
    eapply Ee.eval_proj; tea. noconf e.
    now rewrite -is_propositional_optimize.
    eapply IHev2.
    rewrite nth_nth_error.
    destruct nth_error eqn:hnth => //.
    eapply nth_error_forallb in hnth; tea.

  - now rewrite e.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply Ee.eval_app_cong; eauto.
    eapply Ee.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * destruct t => //; rewrite optimize_mkApps /=.
    * destruct with_guarded_fix.
      + destruct t => /= //; rewrite optimize_mkApps /=;
        rewrite (negbTE (isLambda_mkApps _ _ _)) // (negbTE (isBox_mkApps _ _ _)) // /=; rewrite !isFixApp_mkApps //.
      + destruct t => /= //; rewrite optimize_mkApps /=;
        rewrite (negbTE (isLambda_mkApps _ _ _)) // (negbTE (isBox_mkApps _ _ _)) // /=; rewrite !isFix_mkApps //.
    * destruct f0 => //.
      rewrite optimize_mkApps /=.
      unfold Ee.isFixApp in i.
      rewrite decompose_app_mkApps /= in i => //.
      destruct with_guarded_fix; try rewrite orb_true_r /= // in i.
      discriminate.
  - destruct t => //.
    all:constructor; eauto.
Qed.
