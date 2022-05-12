(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion
     PCUICSafeLemmata. (* for welltyped *)
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaCoq.Erasure Require Import EAst EAstUtils EDeps EExtends
    ELiftSubst ECSubst EGlobalEnv EWellformed EWcbvEval Extract Prelim
    EEnvMap EArities EProgram.

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
Hint Constructors eval : core.

Section optimize.
  Context (Σ : GlobalContextMap.t).

  Fixpoint optimize (t : term) : term :=
    match t with
    | tRel i => tRel i
    | tEvar ev args => tEvar ev (List.map optimize args)
    | tLambda na M => tLambda na (optimize M)
    | tApp u v => tApp (optimize u) (optimize v)
    | tLetIn na b b' => tLetIn na (optimize b) (optimize b')
    | tCase ind c brs =>
      let brs' := List.map (on_snd optimize) brs in
      match GlobalContextMap.inductive_isprop_and_pars Σ (fst ind) with
      | Some (true, npars) =>
        match brs' with
        | [(a, b)] => ECSubst.substl (repeat tBox #|a|) b
        | _ => tCase ind (optimize c) brs'
        end
      | _ => tCase ind (optimize c) brs'
      end
    | tProj p c =>
      match GlobalContextMap.inductive_isprop_and_pars Σ p.(proj_ind) with 
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
    | tConstruct ind i args => tConstruct ind i (map optimize args)
    (* | tPrim _ => t *)
    end.

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof using Type.
    now induction n; simpl; auto; rewrite IHn.
  Qed.
  
  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  Import ECSubst.

  Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    rewrite mkApps_app /= IHl.
    now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
  Qed.

  Lemma csubst_closed t k x : closedn k x -> csubst t k x = x.
  Proof using Type.
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
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - move/andP: H => [] clt cll. 
      destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
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
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|]; cbn; auto.
  Qed.
 
  Lemma subst_csubst_comm l t k b : 
    forallb (closedn 0) l -> closed t ->
    subst l 0 (csubst t (#|l| + k) b) = 
    csubst t k (subst l 0 b).
  Proof using Type.
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
  Proof using Type.
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
  Proof using Type.
    intros hl cl.
    rewrite substl_subst //.
    rewrite substl_subst //.
    apply subst_csubst_comm => //.
  Qed.

  Lemma optimize_csubst a k b : 
    closed a ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof using Type.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros cl; try easy; 
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n)%nat; auto.
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      all:unfold on_snd; cbn.
      * f_equal; auto.
      * depelim X. simpl in *.
        rewrite e //.
        assert (#|br| = #|repeat tBox #|br| |). now rewrite repeat_length.
        rewrite {2}H.
        rewrite substl_csubst_comm //.
        solve_all. eapply All_repeat => //.
        now eapply closed_optimize.
      * depelim X. depelim X.
        f_equal; eauto.
        unfold on_snd; cbn. f_equal; eauto.
        f_equal; eauto.
        f_equal; eauto. f_equal; eauto.
        rewrite map_map_compose; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
    - destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|]=> //;
      now rewrite IHb.
  Qed.

  Lemma optimize_substl s t : 
    forallb (closedn 0) s ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof using Type.
    induction s in t |- *; simpl; auto.
    move/andP => [] cla cls.
    rewrite IHs //. f_equal.
    now rewrite optimize_csubst.
  Qed.

  Lemma optimize_iota_red pars args br :
    forallb (closedn 0) args ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof using Type.
    intros cl.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.
  
  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.fix_subst mfix) ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type.
    intros hfix.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_fix_subst.
    discriminate.
  Qed.

  Lemma optimize_cunfold_cofix mfix idx n f : 
    forallb (closedn 0) (EGlobalEnv.cofix_subst mfix) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def optimize) mfix) idx = Some (n, optimize f).
  Proof using Type.
    intros hcofix.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error.
    intros [= <- <-] => /=. f_equal.
    now rewrite optimize_substl // optimize_cofix_subst.
    discriminate.
  Qed.

  Lemma optimize_nth {n l d} : 
    optimize (nth n l d) = nth n (map optimize l) (optimize d).
  Proof using Type.
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

Lemma eval_is_box {wfl:WcbvFlags} Σ t u : Σ ⊢ t ▷ u -> is_box t -> u = EAst.tBox.
Proof.
  intros ev; induction ev => //.
  - rewrite is_box_tApp.
    intros isb. intuition congruence.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?; solve_discr.
  - rewrite is_box_tApp. move/IHev1 => ?. subst => //.
  - rewrite is_box_tApp. move/IHev1 => ?. subst. solve_discr.
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

Definition optimize_constant_decl Σ cb := 
  {| cst_body := option_map (optimize Σ) cb.(cst_body) |}.
  
Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (optimize_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Definition optimize_env Σ := 
  map (on_snd (optimize_decl Σ)) Σ.(GlobalContextMap.global_decls).
  
Import EnvMap.

Program Fixpoint optimize_env' Σ : EnvMap.fresh_globals Σ -> global_context :=
  match Σ with
  | [] => fun _ => []
  | hd :: tl => fun HΣ =>
    let Σg := GlobalContextMap.make tl (fresh_globals_cons_inv HΣ) in 
    on_snd (optimize_decl Σg) hd :: optimize_env' tl (fresh_globals_cons_inv HΣ) 
  end.

Import EGlobalEnv EExtends.

(* Lemma extends_is_propositional {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind, 
  match inductive_isprop_and_pars Σ ind with
  | Some b => inductive_isprop_and_pars Σ' ind = Some b
  | None => inductive_isprop_and_pars Σ' ind = None
  end.
Proof.
  intros wf ex ind.
  rewrite /inductive_isprop_and_pars.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).

Qed. *)

Lemma extends_inductive_isprop_and_pars {efl : EEnvFlags} {Σ Σ' ind} : extends Σ Σ' -> wf_glob Σ' ->
  isSome (lookup_inductive Σ ind) -> 
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars Σ' ind.
Proof.
  intros ext wf; cbn.
  unfold inductive_isprop_and_pars. cbn.
  destruct lookup_env as [[]|] eqn:hl => //.
  rewrite (extends_lookup wf ext hl).
  destruct nth_error => //.
Qed.

Lemma wellformed_optimize_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t : 
  forall n, EWellformed.wellformed Σ n t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  optimize Σ t = optimize Σ' t.
Proof.
  induction t using EInduction.term_forall_list_ind; cbn -[lookup_constant lookup_inductive
    lookup_projection
    GlobalContextMap.inductive_isprop_and_pars]; intros => //.
  all:unfold wf_fix_gen in *; rtoProp; intuition auto.  
  all:try now f_equal; eauto; solve_all.
  - destruct args; inv H2. reflexivity.
  - rewrite !GlobalContextMap.inductive_isprop_and_pars_spec.
    assert (map (on_snd (optimize Σ)) l = map (on_snd (optimize Σ')) l) as -> by solve_all.
    rewrite (extends_inductive_isprop_and_pars H0 H1 H2).
    destruct inductive_isprop_and_pars as [[[]]|].
    destruct map => //. f_equal; eauto.
    destruct l0 => //. destruct p0 => //. f_equal; eauto.
    all:f_equal; eauto; solve_all.
  - rewrite !GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (extends_inductive_isprop_and_pars H0 H1).
    destruct (lookup_projection) as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => //.
    eapply lookup_projection_lookup_constructor in hl.
    eapply lookup_constructor_lookup_inductive in hl. now rewrite hl.
    destruct inductive_isprop_and_pars as [[[]]|] => //.
    all:f_equal; eauto.
Qed.

Lemma wellformed_optimize_decl_extends {wfl: EEnvFlags} {Σ : GlobalContextMap.t} t : 
  wf_global_decl Σ t ->
  forall {Σ' : GlobalContextMap.t}, extends Σ Σ' -> wf_glob Σ' ->
  optimize_decl Σ t = optimize_decl Σ' t.
Proof.
  destruct t => /= //.
  intros wf Σ' ext wf'. f_equal. unfold optimize_constant_decl. f_equal.
  destruct (cst_body c) => /= //. f_equal.
  now eapply wellformed_optimize_extends.
Qed.

Lemma lookup_env_optimize_env_Some {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn d : 
  wf_glob Σ ->
  GlobalContextMap.lookup_env Σ kn = Some d ->
  ∑ Σ' : GlobalContextMap.t, 
    [× extends Σ' Σ, wf_global_decl Σ' d &
      lookup_env (optimize_env Σ) kn = Some (optimize_decl Σ' d)].
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  induction Σ in map, repr, wf |- *; simpl; auto => //.
  intros wfg.
  case: eqb_specT => //.
  - intros ->. cbn. intros [= <-].
    exists (GlobalContextMap.make Σ (fresh_globals_cons_inv wf)). split.
    now eexists [_].
    cbn. now depelim wfg.
    f_equal. symmetry. eapply wellformed_optimize_decl_extends. cbn. now depelim wfg.
    cbn. now exists [a]. now cbn.
  - intros _. 
    set (Σ' := GlobalContextMap.make Σ (fresh_globals_cons_inv wf)).
    specialize (IHΣ (GlobalContextMap.map Σ') (GlobalContextMap.repr Σ') (GlobalContextMap.wf Σ')).
    cbn in IHΣ. forward IHΣ. now depelim wfg.
    intros hl. specialize (IHΣ hl) as [Σ'' [ext wfgd hl']].
    exists Σ''. split => //.
    * destruct ext as [? ->].
      now exists (a :: x).
    * rewrite -hl'. f_equal.
      clear -wfg.
      eapply map_ext_in => kn hin. unfold on_snd. f_equal.
      symmetry. eapply wellformed_optimize_decl_extends => //. cbn.
      eapply lookup_env_In in hin. 2:now depelim wfg.
      depelim wfg. eapply lookup_env_wellformed; tea.
      cbn. now exists [a].
Qed.

Lemma lookup_env_map_snd Σ f kn : lookup_env (List.map (on_snd f) Σ) kn = option_map f (lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  case: eqb_spec => //.
Qed.

Lemma lookup_env_optimize_env_None {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn : 
  GlobalContextMap.lookup_env Σ kn = None ->
  lookup_env (optimize_env Σ) kn = None.
Proof.
  rewrite GlobalContextMap.lookup_env_spec.
  destruct Σ as [Σ map repr wf].
  cbn. intros hl. rewrite lookup_env_map_snd hl //.
Qed.

Lemma lookup_env_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} kn : 
  wf_glob Σ ->
  lookup_env (optimize_env Σ) kn = option_map (optimize_decl Σ) (lookup_env Σ kn).
Proof.
  intros wf.
  rewrite -GlobalContextMap.lookup_env_spec.
  destruct (GlobalContextMap.lookup_env Σ kn) eqn:hl.
  - eapply lookup_env_optimize_env_Some in hl as [Σ' [ext wf' hl']] => /=.
    rewrite hl'. f_equal.
    eapply wellformed_optimize_decl_extends; eauto. auto.
    
  - cbn. now eapply lookup_env_optimize_env_None in hl. 
Qed.

Lemma is_propositional_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind : 
  wf_glob Σ ->
  inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars (optimize_env Σ) ind.
Proof.
  rewrite /inductive_isprop_and_pars => wf.
  rewrite /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_optimize (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.  
  destruct lookup_env as [[decl|]|] => //.
Qed.

Lemma is_propositional_cstr_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} ind c : 
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl (optimize_env Σ) ind c.
Proof.
  rewrite /constructor_isprop_pars_decl => wf.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite (lookup_env_optimize (inductive_mind ind) wf).
  rewrite /GlobalContextMap.inductive_isprop_and_pars /GlobalContextMap.lookup_inductive
    /GlobalContextMap.lookup_minductive.  
  destruct lookup_env as [[decl|]|] => //.
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

Lemma isFix_mkApps t l : isFix (mkApps t l) = isFix t && match l with [] => true | _ => false end.
Proof.
  induction l using rev_ind; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app /=. now destruct l => /= //; rewrite andb_false_r.
Qed.

Lemma lookup_constructor_optimize {efl : EEnvFlags} {Σ : GlobalContextMap.t} {ind c} :
  wf_glob Σ ->
  lookup_constructor Σ ind c = lookup_constructor (optimize_env Σ) ind c.
Proof.
  intros wfΣ. rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite lookup_env_optimize // /=. destruct lookup_env => // /=.
  destruct g => //.
Qed.

Lemma constructor_isprop_pars_decl_inductive {Σ ind c} {prop pars cdecl} :
  constructor_isprop_pars_decl Σ ind c = Some (prop, pars, cdecl)  -> 
  inductive_isprop_and_pars Σ ind = Some (prop, pars).
Proof.
  rewrite /constructor_isprop_pars_decl /inductive_isprop_and_pars /lookup_constructor.
  destruct lookup_inductive as [[mdecl idecl]|]=> /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma optimize_correct {efl : EEnvFlags} {fl} {Σ : GlobalContextMap.t} t v :
  wf_glob Σ ->
  closed_env Σ ->
  @Ee.eval fl Σ t v ->
  closed t ->
  @Ee.eval (disable_prop_cases fl) (optimize_env Σ) (optimize Σ t) (optimize Σ v).
Proof.
  intros wfΣ clΣ ev.
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
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e0).
    eapply eval_iota; eauto.
    now rewrite -is_propositional_cstr_optimize.
    rewrite nth_error_map e1 //. now len. cbn.
    rewrite -e3. rewrite !skipn_length map_length //.
    eapply IHev2.
    eapply closed_iota_red => //; tea.
    eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
    now rewrite Nat.add_0_r in clbrs.
  
  - move/andP => [] cld clbrs.
    have := (eval_closed _ clΣ _ _ cld ev1). intros cl.
    rewrite optimize_iota_red in IHev2.
    eapply eval_closed in ev1 => //.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e0).
    eapply eval_iota_block. eauto. eauto.
    now rewrite -is_propositional_cstr_optimize.
    rewrite nth_error_map e1 //. now len. cbn.
    rewrite -e3. rewrite !skipn_length map_length //.
    eapply IHev2.
    eapply closed_iota_red => //; tea.
    eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
    now rewrite Nat.add_0_r in clbrs.
  
  - move/andP => [] cld clbrs.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite e e0 /=.
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
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec in IHev2 |- *.
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
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec in IHev2 |- *.
    destruct EGlobalEnv.inductive_isprop_and_pars as [[[] pars]|] eqn:isp; auto.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev1, IHev2. simpl in *.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
  
  - rewrite /declared_constant in isdecl.
    move: (lookup_env_optimize c wfΣ).
    rewrite isdecl /= //.
    intros hl.
    econstructor; tea. cbn. rewrite e //.
    apply IHev.
    eapply lookup_env_closed in clΣ; tea.
    move: clΣ. rewrite /closed_decl e //.
  
  - move=> cld.
    eapply eval_closed in ev1; tea.
    move: ev1; rewrite closedn_mkApps /= => clargs.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e0).
    rewrite optimize_mkApps in IHev1.
    specialize (IHev1 cld).
    eapply Ee.eval_proj; tea.
    now rewrite -is_propositional_cstr_optimize.
    now len. rewrite nth_error_map e2 //.
    eapply IHev2.
    eapply nth_error_forallb in e2; tea.

  - move=> cld.
    eapply eval_closed in ev1; tea.
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    rewrite (constructor_isprop_pars_decl_inductive e0).
    specialize (IHev1 cld).
    eapply Ee.eval_proj_block; tea.
    now rewrite -is_propositional_cstr_optimize.
    now len. rewrite nth_error_map e2 //.
    eapply IHev2.
    eapply nth_error_forallb in e2; tea.

  - rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    now rewrite e.

  - move/andP=> [] clf cla.
    rewrite optimize_mkApps.
    eapply eval_construct; tea.
    rewrite -lookup_constructor_optimize //. exact e0.
    rewrite optimize_mkApps in IHev1. now eapply IHev1.
    now len.
    now eapply IHev2.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply Ee.eval_app_cong; eauto.
    eapply Ee.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * destruct t => //; rewrite optimize_mkApps /=.
    * destruct with_guarded_fix.
      + move: i. 
        rewrite !negb_or.
        rewrite optimize_mkApps !isFixApp_mkApps !isConstructApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        rewrite !andb_true_r.
        rtoProp; intuition auto.
        destruct v => /= //. 
        destruct v => /= //.
      + move: i. 
        rewrite !negb_or.
        rewrite optimize_mkApps !isConstructApp_mkApps.
        destruct args using rev_case => // /=. rewrite map_app !mkApps_app /= //.
        destruct v => /= //. 
  - destruct t => //.
    all:constructor; eauto. cbn in *. destruct l; eauto.
Qed.

From MetaCoq.Erasure Require Import EEtaExpanded.

Lemma isLambda_optimize Σ t : isLambda t -> isLambda (optimize Σ t).
Proof. destruct t => //. Qed.
Lemma isBox_optimize Σ t : isBox t -> isBox (optimize Σ t).
Proof. destruct t => //. Qed.

Lemma optimize_expanded {Σ : GlobalContextMap.t} t : expanded Σ t -> expanded Σ (optimize Σ t).
Proof.
  induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  all:rewrite ?optimize_mkApps.
  - eapply expanded_mkApps_expanded => //. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars].
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    2-3:constructor; eauto; solve_all.
    destruct branches eqn:heq.
    constructor; eauto; solve_all. cbn.
    destruct l => /=.
    eapply isEtaExp_expanded.
    eapply isEtaExp_substl. eapply forallb_repeat => //.
    destruct branches as [|[]]; cbn in heq; noconf heq.
    cbn -[isEtaExp] in *. depelim H1. cbn in H1.
    now eapply expanded_isEtaExp.
    constructor; eauto; solve_all.
    depelim H1. depelim H1. do 2 (constructor; intuition auto).
    solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars].
    rewrite GlobalContextMap.inductive_isprop_and_pars_spec.
    destruct inductive_isprop_and_pars as [[[|] _]|] => /= //.
    constructor. all:constructor; auto.
  - cbn. eapply expanded_tFix. solve_all.
    rewrite isLambda_optimize //.
  - eapply expanded_tConstruct_app; tea.
    now len. solve_all.
Qed.

Lemma optimize_expanded_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded Σ t -> expanded (optimize_env Σ) t.
Proof.
  intros wf; induction 1 using expanded_ind.
  all:try solve[constructor; eauto; solve_all].
  eapply expanded_tConstruct_app.
  destruct H as [[H ?] ?].
  split => //. split => //. red.
  red in H. rewrite lookup_env_optimize // /= H //. 1-2:eauto. auto. solve_all. 
Qed.

Lemma optimize_expanded_decl {Σ : GlobalContextMap.t} t : expanded_decl Σ t -> expanded_decl Σ (optimize_decl Σ t).
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded.
Qed.

Lemma optimize_expanded_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t : wf_glob Σ -> expanded_decl Σ t -> expanded_decl (optimize_env Σ) t.
Proof.
  destruct t as [[[]]|] => /= //.
  unfold expanded_constant_decl => /=.
  apply optimize_expanded_irrel.
Qed.

Lemma optimize_env_extends' {efl : EEnvFlags} {Σ Σ' : GlobalContextMap.t} : 
  extends Σ Σ' ->
  wf_glob Σ' -> 
  List.map (on_snd (optimize_decl Σ)) Σ.(GlobalContextMap.global_decls) =
  List.map (on_snd (optimize_decl Σ')) Σ.(GlobalContextMap.global_decls).
Proof.
  intros ext.
  destruct Σ as [Σ map repr wf]; cbn in *.
  move=> wfΣ.
  assert (extends Σ Σ); auto. now exists [].
  assert (wf_glob Σ).
  { eapply extends_wf_glob. exact ext. tea. }
  revert H H0.
  generalize Σ at 1 3 5 6. intros Σ''.
  induction Σ'' => //. cbn.
  intros hin wfg. depelim wfg.
  f_equal.
  2:{ eapply IHΣ'' => //. destruct hin. exists (x ++ [(kn, d)]). rewrite -app_assoc /= //. }
  unfold on_snd. cbn. f_equal.
  eapply wellformed_optimize_decl_extends => //. cbn.
  eapply extends_wf_global_decl. 3:tea.
  eapply extends_wf_glob; tea.
  destruct hin. exists (x ++ [(kn, d)]). rewrite -app_assoc /= //.
Qed.

Lemma optimize_env_eq {efl : EEnvFlags} (Σ : GlobalContextMap.t) : wf_glob Σ -> optimize_env Σ = optimize_env' Σ.(GlobalContextMap.global_decls) Σ.(GlobalContextMap.wf).
Proof.
  intros wf.
  unfold optimize_env.
  destruct Σ; cbn. cbn in wf.
  induction global_decls in map, repr, wf0, wf |- * => //.
  cbn. f_equal.
  destruct a as [kn d]; unfold on_snd; cbn. f_equal. symmetry.
  eapply wellformed_optimize_decl_extends => //. cbn. now depelim wf. cbn. now exists [(kn, d)]. cbn.
  set (Σg' := GlobalContextMap.make global_decls (fresh_globals_cons_inv wf0)).
  erewrite <- (IHglobal_decls (GlobalContextMap.map Σg') (GlobalContextMap.repr Σg')).
  2:now depelim wf.
  set (Σg := {| GlobalContextMap.global_decls := _ :: _ |}).
  symmetry. eapply (optimize_env_extends' (Σ := Σg') (Σ' := Σg)) => //.
  cbn. now exists [a].
Qed.

Lemma optimize_env_expanded {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  wf_glob Σ -> expanded_global_env Σ -> expanded_global_env (optimize_env Σ).
Proof.
  unfold expanded_global_env; move=> wfg.
  rewrite optimize_env_eq //.
  destruct Σ as [Σ map repr wf]. cbn in *.
  clear map repr.
  induction 1; cbn; constructor; auto.
  cbn in IHexpanded_global_declarations.
  unshelve eapply IHexpanded_global_declarations. now depelim wfg. cbn. 
  set (Σ' := GlobalContextMap.make _ _).
  rewrite -(optimize_env_eq Σ'). cbn. now depelim wfg.
  eapply (optimize_expanded_decl_irrel (Σ := Σ')). now depelim wfg.
  now unshelve eapply (optimize_expanded_decl (Σ:=Σ')).
Qed.

Lemma optimize_wellformed {efl : EEnvFlags} {Σ : GlobalContextMap.t} n t :
  has_tBox -> has_tRel ->
  wf_glob Σ -> EWellformed.wellformed Σ n t -> EWellformed.wellformed Σ n (optimize Σ t).
Proof.
  intros wfΣ hbox hrel.
  induction t in n |- * using EInduction.term_forall_list_ind => //.
  all:try solve [cbn; rtoProp; intuition auto; solve_all].
  - cbn. intros. rtoProp; intuition eauto. now destruct args; inv H0.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars lookup_inductive]. move/and3P => [] hasc /andP[]hs ht hbrs.
    destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    destruct l as [|[br n'] [|l']] eqn:eql; simpl.
    all:rewrite ?hasc ?hs /= ?andb_true_r.
    rewrite IHt //.
    depelim X. cbn in hbrs.
    rewrite andb_true_r in hbrs.
    specialize (i _ hbrs).
    eapply wellformed_substl => //. solve_all. eapply All_repeat => //.
    now rewrite repeat_length.
    cbn in hbrs; rtoProp; solve_all. depelim X; depelim X. solve_all.
    do 2 depelim X. solve_all.
    do 2 depelim X. solve_all.
    rtoProp; solve_all. solve_all.
    rtoProp; solve_all. solve_all.
  - cbn -[GlobalContextMap.inductive_isprop_and_pars lookup_inductive]. move/andP => [] /andP[]hasc hs ht.
    destruct GlobalContextMap.inductive_isprop_and_pars as [[[|] _]|] => /= //.
    all:rewrite hasc hs /=; eauto.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now len.
    unfold test_def in *. len. eauto.
  - cbn. unfold wf_fix; rtoProp; intuition auto; solve_all. now len.
    unfold test_def in *. len. eauto.
Qed.

Import EWellformed.

Lemma optimize_wellformed_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} t :
  wf_glob Σ ->
  forall n, wellformed Σ n t -> wellformed (optimize_env Σ) n t.
Proof.
  intros wfΣ. induction t using EInduction.term_forall_list_ind; cbn => //.
  all:try solve [intros; unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct (cst_body c) => //.
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    all: try now (intros; rtoProp; congruence).
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //. subst g.
    destruct nth_error => /= //.
    intros; rtoProp; intuition auto; solve_all.
  - rewrite lookup_env_optimize //.
    destruct lookup_env eqn:hl => // /=.
    destruct g eqn:hg => /= //.
    rewrite andb_false_r => //.
    destruct nth_error => /= //.
    all:intros; rtoProp; intuition auto; solve_all.
Qed.

Lemma optimize_wellformed_decl_irrel {efl : EEnvFlags} {Σ : GlobalContextMap.t} d :
  wf_glob Σ ->
  wf_global_decl Σ d -> wf_global_decl (optimize_env Σ) d.
Proof.
  intros wf; destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply optimize_wellformed_irrel.
Qed.

Lemma optimize_decl_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel -> wf_glob Σ -> 
  forall d, wf_global_decl Σ d -> wf_global_decl (optimize_env Σ) (optimize_decl Σ d).
Proof.
  intros hasb hasr wf d.
  intros hd.
  eapply optimize_wellformed_decl_irrel; tea.
  move: hd.
  destruct d => /= //.
  destruct (cst_body c) => /= //.
  now eapply optimize_wellformed => //.
Qed.

Lemma fresh_global_optimize_env {Σ : GlobalContextMap.t} kn : 
  fresh_global kn Σ ->
  fresh_global kn (optimize_env Σ).
Proof.
  destruct Σ as [Σ map repr wf]; cbn in *.
  induction 1; cbn; constructor; auto.
  now eapply Forall_map; cbn.
Qed.

Lemma optimize_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel -> 
  wf_glob Σ -> wf_glob (optimize_env Σ).
Proof.
  intros hasb hasrel.
  intros wfg. rewrite optimize_env_eq //.
  destruct Σ as [Σ map repr wf]; cbn in *.
  clear map repr.
  induction wfg; cbn; constructor; auto.
  - rewrite /= -(optimize_env_eq (GlobalContextMap.make Σ (fresh_globals_cons_inv wf))) //.
    eapply optimize_decl_wf => //.
  - rewrite /= -(optimize_env_eq (GlobalContextMap.make Σ (fresh_globals_cons_inv wf))) //.
    now eapply fresh_global_optimize_env.
Qed.

Definition optimize_program (p : eprogram_env) :=
  (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2).

Definition optimize_program_wf {efl} (p : eprogram_env) {hastbox : has_tBox} {hastrel : has_tRel} :
  wf_eprogram_env efl p -> wf_eprogram efl (optimize_program p).
Proof.
  intros []; split.
  now eapply optimize_env_wf.
  cbn. eapply optimize_wellformed_irrel => //. now eapply optimize_wellformed.
Qed.

Definition optimize_program_expanded {efl} (p : eprogram_env) :
  wf_eprogram_env efl p ->
  expanded_eprogram_env_cstrs p -> expanded_eprogram_cstrs (optimize_program p).
Proof.
  unfold expanded_eprogram_env_cstrs.
  move=> [wfe wft] /andP[] etae etat.
  apply/andP; split.
  cbn. eapply expanded_global_env_isEtaExp_env, optimize_env_expanded => //.
  now eapply isEtaExp_env_expanded_global_env.
  eapply expanded_isEtaExp.
  eapply optimize_expanded_irrel => //.
  now apply optimize_expanded, isEtaExp_expanded.
Qed.
