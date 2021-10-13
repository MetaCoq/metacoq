(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnv
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.
     
From MetaCoq.Erasure Require Import EAstUtils EArities Extract Prelim ErasureCorrectness EDeps 
    ErasureFunction ELiftSubst.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

Hint Constructors Ee.eval : core.

Set Warnings "-notation-overridden".
Import E.
Set Warnings "+notation-overridden".


Lemma closedn_subst s k t : 
  forallb (closedn k) s -> closedn (#|s| + k) t -> 
  closedn k (subst0 s t).
Proof. Admitted.

Lemma closed_csubst t k u : 
  closedn k t -> 
  closedn (S k) u -> 
  closedn k (ECSubst.csubst t 0 u).
Proof.
  intros.
Admitted.

Lemma closed_substl ts k u : 
  forallb (closedn k) ts -> 
  closedn (#|ts| + k) u -> 
  closedn k (ECSubst.substl ts u).
Proof.
  intros.
Admitted.
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
      match ETyping.is_propositional_ind Σ (fst ind) with
      | Some true =>
        match brs' with
        | [(a, b)] => ECSubst.substl (repeat E.tBox a) b
        | _ => E.tCase ind (optimize c) brs'
        end
      | _ => E.tCase ind (optimize c) brs'
      end
    | tProj p c =>
      match ETyping.is_propositional_ind Σ p.1.1 with 
      | Some true => tBox
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
    | tPrim _ => t
    end.

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof.
    induction l using rev_ind; simpl; auto.
    now rewrite -mkApps_nested /= IHl map_app /= -mkApps_nested /=.
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
    rewrite - mkApps_nested /= IHl.
    now rewrite [EAst.tApp _ _](mkApps_nested _ _ [_]) map_app.
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
    - move/andP: H => [] clt cll. destruct ETyping.is_propositional_ind as [[|]|] => /= //.
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
    - destruct ETyping.is_propositional_ind.
      destruct b => //. cbn; auto.
      cbn; auto.
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
    - destruct (k ?= n); auto.
    - destruct ETyping.is_propositional_ind as [[|]|] => /= //.
      destruct l as [|[br n] [|l']] eqn:eql; simpl.
      * f_equal; auto.
      * depelim X. simpl in *.
        rewrite e //.
        assert (br = #|repeat tBox br|). now rewrite repeat_length.
        rewrite {2}H0.
        rewrite substl_csubst_comm //.
        solve_all. eapply All_repeat => //.
        now eapply closed_optimize.
      * depelim X. depelim X.
        f_equal; eauto. f_equal; eauto. f_equal; eauto.
        f_equal; eauto. f_equal; eauto.
        rewrite map_map_compose; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
      * rewrite ?map_map_compose; f_equal; eauto; solve_all.
    - destruct ETyping.is_propositional_ind as [[|]|]=> //;
      now rewrite IHb.
    - f_equal; solve_all.
      destruct x; unfold EAst.map_def; simpl in *. 
      autorewrite with len. f_equal; eauto.
    - f_equal; solve_all.
      destruct x; unfold EAst.map_def; simpl in *. 
      autorewrite with len. f_equal; eauto.
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
    optimize (ETyping.iota_red pars args br) = ETyping.iota_red pars (map optimize args) (on_snd optimize br).
  Proof.
    intros cl.
    unfold ETyping.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_skipn //.
    now rewrite map_skipn.
  Qed.
  
  Lemma optimize_fix_subst mfix : ETyping.fix_subst (map (map_def optimize) mfix) = map optimize (ETyping.fix_subst mfix).
  Proof.
    unfold ETyping.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : ETyping.cofix_subst (map (map_def optimize) mfix) = map optimize (ETyping.cofix_subst mfix).
  Proof.
    unfold ETyping.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (ETyping.fix_subst mfix) ->
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
    forallb (closedn 0) (ETyping.cofix_subst mfix) ->
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

Lemma erase_eval_to_box (wfl := Ee.default_wcbv_flags) {Σ : global_env_ext}  {wfΣ : wf_ext Σ} {t v Σ' t' deps} :
  forall wt : welltyped Σ [] t,
  erase Σ (sq wfΣ) [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ (sq wfΣ.1) = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' tBox -> ∥ isErasable Σ [] t ∥.
Proof.
  intros [T wt].
  intros.
  destruct (erase_correct Σ wfΣ _ _ _ _ _ _ H H0 H1 X) as [ev [eg [eg']]].
  pose proof (Ee.eval_deterministic H2 eg'). subst.
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

Import ETyping.

(* Lemma optimize_extends Σ Σ' : extends Σ Σ' ->
  optimize Σ t = optimize Σ' t. *)

Lemma lookup_env_optimize Σ kn : 
  lookup_env (optimize_env Σ) kn = 
  option_map (optimize_decl Σ) (lookup_env Σ kn).
Proof.
  unfold optimize_env.
  induction Σ at 2 4; simpl; auto.
  destruct kername_eq_dec => //.
Qed.

Lemma is_propositional_optimize Σ ind : 
  is_propositional_ind Σ ind = is_propositional_ind (optimize_env Σ) ind.
Proof.
  rewrite /is_propositional_ind.
  rewrite lookup_env_optimize.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto.
Qed.

Lemma isLambda_mkApps f l : ~~ isLambda f -> ~~ EAst.isLambda (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite -mkApps_nested.
Qed.
 
Lemma isFixApp_mkApps f l : ~~ Ee.isFixApp f -> ~~ Ee.isFixApp (mkApps f l).
Proof.
  unfold Ee.isFixApp.
  erewrite <- (fst_decompose_app_rec _ l).
  now rewrite /decompose_app decompose_app_rec_mkApps app_nil_r.
Qed.

Lemma isBox_mkApps f l : ~~ isBox f -> ~~ isBox (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite -mkApps_nested.
Qed.

Definition extends (Σ Σ' : global_declarations) := ∑ Σ'', Σ' = Σ'' ++ Σ.

Definition fresh_global kn (Σ : global_declarations) :=
  Forall (fun x => x.1 <> kn) Σ.

Inductive wf_glob : global_declarations -> Type :=
| wf_glob_nil : wf_glob []
| wf_glob_cons kn d Σ : 
  wf_glob Σ ->
  fresh_global kn Σ ->
  wf_glob ((kn, d) :: Σ).
Derive Signature for wf_glob.

Lemma lookup_env_Some_fresh {Σ c decl} :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma extends_lookup {Σ Σ' c decl} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *.
  - simpl. auto.
  - specialize (IHΣ'' c decl). forward IHΣ''.
    + now inv wfΣ'.
    + intros HΣ. specialize (IHΣ'' HΣ).
      inv wfΣ'. simpl in *.
      unfold eq_kername; destruct kername_eq_dec; subst; auto.
      apply lookup_env_Some_fresh in IHΣ''; contradiction.
Qed.

Lemma extends_is_propositional {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind b, is_propositional_ind Σ ind = Some b -> is_propositional_ind Σ' ind = Some b.
Proof.
  intros wf ex ind b.
  rewrite /is_propositional_ind.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).
Qed.

Lemma weakening_eval_env (wfl : Ee.WcbvFlags) {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  ∀ v t, Ee.eval Σ v t -> Ee.eval Σ' v t.
Proof.
  intros wf ex t v ev.
  induction ev; try solve [econstructor; eauto using (extends_is_propositional wf ex)].
  econstructor; eauto.
  red in isdecl |- *. eauto using extends_lookup.
Qed.

Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args in f |- *; simpl; auto.
  ring. rewrite IHargs /=. ring. 
Qed.

(** Evaluation preserves closedness: *)
Lemma eval_closed {wfl : Ee.WcbvFlags} Σ : forall t u, closed t -> Ee.eval Σ t u -> closed u.
Proof.
  move=> t u Hc ev. move: Hc.
  induction ev; simpl in *; auto;
    (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
  - eapply IHev3. rewrite ECSubst.closed_subst //. auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto. cbn. auto.
  - eapply IHev2.
    rewrite ECSubst.closed_subst; auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto.
  - apply IHev2. todo "case".
  - eapply IHev2. solve_all.
    todo "case".
  - eapply IHev3.
    apply/andP.
    split; [|easy].
    specialize (IHev1 Hc).
    rewrite closedn_mkApps in IHev1.
    move/andP: IHev1 => [clfix clargs].
    rewrite closedn_mkApps clargs andb_true_r.
    todo "case".
    (* eapply closed_unfold_fix; [easy|]. *)
    (* now rewrite closed_unfold_fix_cunfold_eq. *)
  - apply andb_true_iff.
    split; [|easy].
    solve_all.
  - eapply IHev. rewrite closedn_mkApps.
    rewrite closedn_mkApps in Hc. move/andP: Hc => [Hfix Hargs].
    repeat (apply/andP; split; auto). 
    todo "case".
     (* rewrite -closed_unfold_cofix_cunfold_eq in e => //. *)
    (* eapply closed_unfold_cofix in e; eauto. *)
  - eapply IHev. rewrite closedn_mkApps in Hc *.
    move/andP: Hc => [Hfix Hargs].
    rewrite closedn_mkApps Hargs.
    todo "casE".
    (* rewrite -closed_unfold_cofix_cunfold_eq in e => //.
    eapply closed_unfold_cofix in e; eauto.
    now rewrite e. *)
  - apply IHev. todo "case".
  - todo "case".
  - rtoProp; intuition auto.
Qed.

Lemma closed_iota_red pars c args brs br :
  forallb (closedn 0) args ->
  nth_error brs c = Some br ->
  #|skipn pars args| = br.1 ->
  closedn br.1 br.2 ->
  closed (iota_red pars args br).
Proof.
  intros clargs hnth hskip clbr.
  rewrite /iota_red.
  eapply closed_substl => //.
  now rewrite forallb_skipn.
  now rewrite hskip Nat.add_0_r.
Qed.

Lemma closed_fix_subst mfix idx : 
  closed (EAst.tFix mfix idx) ->
  forallb (closedn 0) (fix_subst mfix).
Proof. Admitted.

Lemma closed_cofix_subst mfix idx : 
  closed (EAst.tCoFix mfix idx) ->
  forallb (closedn 0) (cofix_subst mfix).
Proof. Admitted.

Lemma closed_cunfold_fix mfix idx n f : 
  closed (EAst.tFix mfix idx) ->
  Ee.cunfold_fix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /Ee.cunfold_fix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld. 
  move=> [=] _ <-.
  eapply closed_substl. now eapply (closed_fix_subst _ idx).
  rewrite fix_subst_length.
  apply cld.
Qed.

Lemma closed_cunfold_cofix mfix idx n f : 
  closed (EAst.tCoFix mfix idx) ->
  Ee.cunfold_cofix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /Ee.cunfold_cofix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld. 
  move=> [=] _ <-.
  eapply closed_substl. now eapply (closed_cofix_subst _ idx).
  rewrite cofix_subst_length.
  apply cld.
Qed.

Lemma optimize_correct Σ t v :
  @Ee.eval Ee.default_wcbv_flags Σ t v ->
  closed t ->
  @Ee.eval Ee.opt_wcbv_flags (optimize_env Σ) (optimize Σ t) (optimize Σ v).
Proof.
  intros ev.
  induction ev; simpl in *; try solve [econstructor; eauto].

  - move/andP => [] cla clt. econstructor; eauto.
  - move/andP => [] clf cla. econstructor; eauto.
    rewrite optimize_csubst in IHev3.
    now eapply eval_closed in ev2.
    apply IHev3. todo "casE".

  - move/andP => [] clb0 clb1. rewrite optimize_csubst in IHev2.
    now eapply eval_closed in ev1.
    econstructor; eauto. eapply IHev2, closed_csubst => //.
    now eapply eval_closed in ev1.

  - move/andP => [] cld clbrs. rewrite optimize_mkApps in IHev1.
    have := (eval_closed _ _ _ cld ev1); rewrite closedn_mkApps => /andP[] _ clargs.
    rewrite optimize_iota_red in IHev2.
    eapply eval_closed in ev1 => //.
    destruct ETyping.is_propositional_ind as [[]|]eqn:isp => //.
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
    now eapply closed_fix_subst.
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
    simpl in *. eapply Ee.eval_fix_value. auto. auto.
    eapply optimize_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    now rewrite map_length. 

  - move/andP => []. rewrite closedn_mkApps. move/andP => [] clfix clargs clbrs.
    forward IHev.
    { rewrite closedn_mkApps clargs clbrs !andb_true_r.
      eapply closed_cunfold_cofix; tea. }
    destruct ETyping.is_propositional_ind as [[]|] eqn:isp => //.
    destruct brs as [|[a b] []]; simpl in *; auto.
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.

  - rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    destruct ETyping.is_propositional_ind as [[]|] eqn:isp; auto.
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite -> optimize_mkApps in IHev |- *. simpl.
    econstructor; eauto.
    apply optimize_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
  
  - econstructor. red in isdecl |- *.
    rewrite lookup_env_optimize isdecl //.
    now rewrite /optimize_constant_decl e.
    apply IHev.
    admit.
  
  - destruct ETyping.is_propositional_ind as [[]|] eqn:isp => //.
    rewrite optimize_mkApps in IHev1.
    rewrite optimize_nth in IHev2.
    econstructor; eauto. now rewrite -is_propositional_optimize.
    eapply IHev2. admit.
  
  - now rewrite e.

  - move/andP => [] clf cla.
    specialize (IHev1 clf). specialize (IHev2 cla).
    eapply Ee.eval_app_cong; eauto.
    eapply Ee.eval_to_value in ev1.
    destruct ev1; simpl in *; eauto.
    * destruct t => //; rewrite optimize_mkApps /=.
    * destruct t => /= //; rewrite optimize_mkApps /=;
      rewrite (negbTE (isLambda_mkApps _ _ _)) // (negbTE (isBox_mkApps _ _ _)) 
        // (negbTE (isFixApp_mkApps _ _ _)) //.
    * destruct f0 => //.
      rewrite optimize_mkApps /=.
      unfold Ee.isFixApp in i.
      rewrite decompose_app_mkApps /= in i => //.
      rewrite orb_true_r /= // in i.
  - destruct t => //.
    all:constructor; eauto.
Admitted.

Lemma All2_All2_mix {A B} {P Q : A -> B -> Type} l l' : 
  All2 P l l' ->
  All2 Q l l' ->
  All2 (fun x y => P x y × Q x y) l l'.
Proof.
  induction 1; intros H; depelim H; constructor; auto.
Qed.

Lemma erases_closed Σ Γ t t' : Σ;;; Γ |- t ⇝ℇ t' -> PCUICAst.closedn #|Γ| t -> closedn #|Γ| t'.
Proof.
  induction 1 using erases_forall_list_ind; cbn; auto; try solve [rtoProp; repeat solve_all].
  - rtoProp. intros []. split; eauto. solve_all.
    eapply Forall2_All2 in H1. eapply All2_All2_mix in X; tea.
    eapply forallb_All in H3. eapply All2_All_mix_left in X; tea. clear H3.
    clear H1.
    solve_all. rewrite -b.
    rewrite app_length inst_case_branch_context_length in a0.
    eapply a0. now move/andP: a => [].
  - unfold test_def in *. solve_all.
    eapply All2_All2_mix in X; tea. solve_all.
    len in a0. rewrite - (All2_length H).
    eapply a0. now move/andP: a.
  - unfold test_def in *. solve_all.
    eapply All2_All2_mix in X; tea. solve_all.
    len in a0. rewrite - (All2_length H).
    eapply a0. now move/andP: a.
Qed.

Lemma erase_opt_correct (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t v Σ' t' :
  forall wt : welltyped Σ [] t,
  erase Σ (sq wfΣ) [] t wt = t' ->
  erase_global (term_global_deps t') Σ (sq wfΣ.1) = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  ∃ v' : term, Σ;;; [] |- v ⇝ℇ v' ∧ 
  ∥ @Ee.eval Ee.opt_wcbv_flags (optimize_env Σ') (optimize Σ' t') (optimize Σ' v') ∥.
Proof.
  intros wt.
  generalize (sq wfΣ.1) as swfΣ.
  intros swfΣ HΣ' Ht' ev.
  pose proof (erases_erase (wfΣ := sq wfΣ) wt); eauto.
  rewrite HΣ' in H.
  destruct wt as [T wt].
  unshelve epose proof (erase_global_erases_deps wfΣ wt H _); cycle 2.
  eapply erases_correct in ev; eauto.
  destruct ev as [v' [ev evv]].
  exists v'. split.
  2:{ sq. apply optimize_correct; tea.
      clear HΣ'. eapply PCUICClosed.subject_closed in wt.
      eapply erases_closed in H; tea. }
  auto. 
  rewrite <- Ht'.
  eapply erase_global_includes.
  intros.
  eapply term_global_deps_spec in H; eauto.
  eapply KernameSet.subset_spec.
  intros x hin; auto.
Qed.
