(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping
  PCUICGuardCondition PCUICGlobalEnv
  PCUICWeakeningEnvConv.
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma subrelations_extends `{CF:checker_flags} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ,φ))) (eq_universe (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed.

Lemma subrelations_leq__extends `{CF:checker_flags} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_universe (global_ext_constraints (Σ,φ))) (leq_universe (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed. 

Lemma weakening_env_convSpec `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convSpec (Σ, φ) Γ M N ->
  convSpec (Σ', φ) Γ M N.
Proof. 
  intros HΣ' Hextends Ind. 
  revert Γ M N Ind Σ' HΣ' Hextends. 
  eapply (convSpec0_ind_all Σ (eq_universe (global_ext_constraints (Σ,φ))) 
            (fun Γ M N => forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> (Σ', φ);;; Γ |- M =s N)); intros; try solve [econstructor; eauto with extends; intuition]. 
  - eapply cumul_Evar. eapply All2_impl. 1: tea. cbn; intros. apply X2.2; eauto.    
  - eapply cumul_Case; intuition.
    * destruct X. repeat split; intuition. 
      + eapply All2_impl. 1: tea. cbn; intros. apply X.2; eauto.
      + eapply R_universe_instance_impl'; eauto. apply subrelations_extends; eauto. 
    * eapply All2_impl. 1: tea. cbn; intros. intuition.  
  - eapply cumul_Fix. eapply All2_impl. 1: tea. cbn; intros. intuition.
  - eapply cumul_CoFix. eapply All2_impl. 1: tea. cbn; intros. intuition.
  - eapply cumul_Ind.
    * eapply R_global_instance_weaken_env; eauto. all: apply subrelations_extends; eauto. 
    * eapply All2_impl. 1: tea. cbn; intros. intuition.  
  - eapply cumul_Construct.
    * eapply R_global_instance_weaken_env; eauto. all: apply subrelations_extends; eauto. 
    * eapply All2_impl. 1: tea. cbn; intros. intuition.  
  - eapply cumul_Sort. eapply eq_universe_subset; eauto.
    now eapply weakening_env_global_ext_constraints.
  - eapply cumul_Const. eapply R_universe_instance_impl'; eauto. apply subrelations_extends; eauto. 
  Defined. 

Ltac subrel := apply subrelations_extends; eauto.

Lemma weakening_env_cumulSpec `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpec (Σ, φ) Γ M N ->
  cumulSpec (Σ', φ) Γ M N.
  intros HΣ' Hextends Ind.
  unfold cumulSpec. 
  pose proof (subrelations_leq__extends _ _  φ Hextends). revert H.
  assert (RelationClasses.subrelation 
          (eq_universe (global_ext_constraints (Σ,φ)))
          (leq_universe (global_ext_constraints (Σ',φ)))). 
  { etransitivity; try apply subrelations_leq__extends; eauto. 
    apply eq_universe_leq_universe.  } revert H.
  generalize (leq_universe (global_ext_constraints (Σ',φ))); intros Rle Hlee Hle . 
  revert Γ M N Ind Σ' Rle Hle Hlee HΣ' Hextends. 
  eapply (cumulSpec0_ind_all Σ (eq_universe (global_ext_constraints (Σ,φ))) 
            (fun Rle Γ M N => forall (Σ' : global_env) Rle', RelationClasses.subrelation Rle Rle' -> RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ,φ))) Rle' -> wf Σ' -> extends Σ Σ' -> cumulSpec0 Σ' (eq_universe (global_ext_constraints (Σ',φ))) Rle' Γ M N)) 
            with (Rle := leq_universe (global_ext_constraints (Σ,φ))); 
              intros; try solve [econstructor; eauto with extends; intuition]. 
  - eapply cumul_Evar. eapply All2_impl. 1: tea. cbn; intros. apply X2.2; eauto; subrel.
  - eapply cumul_Case; intuition.
    * destruct X. repeat split; intuition. 
      + eapply All2_impl. 1: tea. cbn; intros. apply X.2; eauto; subrel.
      + eapply R_universe_instance_impl'; eauto; subrel.
    * eapply All2_impl. 1: tea. cbn; intros. intuition.
  - eapply cumul_Fix. eapply All2_impl. 1: tea. cbn; intros. intuition.
  - eapply cumul_CoFix. eapply All2_impl. 1: tea. cbn; intros. intuition.
  - eapply cumul_Ind.
    * eapply @R_global_instance_weaken_env with (Re := eq_universe (global_ext_constraints (Σ, φ))) (Rle := Rle); eauto. 
      subrel.
    * eapply All2_impl. 1: tea. cbn; intros. intuition.  
  - eapply cumul_Construct.
    * eapply @R_global_instance_weaken_env with (Re := eq_universe (global_ext_constraints (Σ, φ))) (Rle := Rle); eauto. 
      subrel.
    * eapply All2_impl. 1: tea. cbn; intros. intuition. 
  - eapply cumul_Const; eauto. eapply R_universe_instance_impl'; eauto; subrel.  
Defined.

Lemma weakening_env_conv_decls {cf} {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (conv_decls (Σ, φ) Γ Γ') (conv_decls (Σ', φ) Γ Γ').
Proof.
  intros wf ext d d' Hd; depelim Hd; constructor; tas;
    eapply weakening_env_convSpec; tea.
Qed.

Lemma weakening_env_cumul_decls {cf} {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (cumul_decls (Σ, φ) Γ Γ') (cumul_decls (Σ', φ) Γ Γ').
Proof.
  intros wf ext d d' Hd; depelim Hd; constructor; tas;
    (eapply weakening_env_convSpec || eapply weakening_env_cumulSpec); tea.
Qed.

Lemma weakening_env_conv_ctx {cf} {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  conv_context (Σ, φ) Γ Δ ->
  conv_context (Σ', φ) Γ Δ.
Proof.
  intros wf ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_conv_decls.
Qed.

#[global]
Hint Resolve weakening_env_conv_ctx : extends.

Lemma weakening_env_cumul_ctx {cf} {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  cumul_context (Σ, φ) Γ Δ ->
  cumul_context (Σ', φ) Γ Δ.
Proof.
  intros wf ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_cumul_decls.
Qed.
#[global]
Hint Resolve weakening_env_cumul_ctx : extends.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T)
           (fun Σ Γ =>
             forall Σ', wf Σ' -> extends Σ.1 Σ' -> wf_local (Σ', Σ.2) Γ).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - induction X; constructor; eauto 2 with extends.
    + eexists; eapply p; eauto.
    + eexists; eapply p0; eauto.
    + eapply p; eauto.
  - econstructor; eauto 2 with extends.
    now apply extends_wf_universe.
  - econstructor; eauto 2 with extends. all: econstructor; eauto 2 with extends.
    * revert X6. clear -Σ' wfΣ' extΣ.
      induction 1; constructor; eauto with extends.
    * close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply fix_guard_extends; eauto.
    + eapply (All_impl X0); simpl; intuition eauto with extends.
      destruct X as [s Hs]; exists s. intuition eauto with extends.
    + eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply cofix_guard_extends; eauto.
    + eapply (All_impl X0); simpl; intuition eauto with extends.
      destruct X as [s Hs]; exists s. intuition eauto with extends.
    + eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor. 1: eauto.
    + eapply forall_Σ'1; eauto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumulSpec in cumulA; eauto.
Qed.

Lemma weakening_on_global_decl `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_prop P ->
  wf Σ -> wf Σ' -> extends Σ Σ' ->
  on_global_decl P (Σ, φ) kn decl ->
  on_global_decl P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop.
  intros HPΣ wfΣ wfΣ' Hext Hdecl.
  destruct decl.
  1:{
    destruct c. destruct cst_body0.
    - simpl in *.
      red in Hdecl |- *. simpl in *.
      eapply (HPΣ Σ Σ'); eauto.
    - eapply (HPΣ Σ Σ'); eauto.
  }
  simpl in *.
  destruct Hdecl as [onI onP onnP]; constructor; eauto.
  - eapply Alli_impl; eauto. intros.
    destruct X. unshelve econstructor; eauto.
    + unfold on_type in *; intuition eauto.
    + unfold on_constructors in *. eapply All2_impl; eauto.
      intros.
      destruct X as [? ? ? ?]. unshelve econstructor; eauto.
      * unfold on_type in *; eauto.
      * clear on_cindices cstr_eq cstr_args_length.
        revert on_cargs.
        induction (cstr_args x0) in y |- *; destruct y; simpl in *; eauto.
        ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
        ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
      * clear on_ctype on_cargs.
        revert on_cindices.
        generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
        generalize (cstr_indices x0).
        induction 1; constructor; eauto.
      * simpl.
        intros v indv. specialize (on_ctype_variance v indv).
        simpl in *. move: on_ctype_variance.
        unfold cstr_respects_variance. destruct variance_universes as [[[univs u] u']|]; auto.
        intros [args idxs]. split.
        ** eapply (All2_fold_impl args); intros.
           inversion X; constructor; auto.
           ++ eapply weakening_env_cumulSpec; eauto.
           ++ eapply weakening_env_convSpec; eauto.
           ++ eapply weakening_env_cumulSpec; eauto.
        ** eapply (All2_impl idxs); intros.
          eapply weakening_env_convSpec; eauto.
    + unfold check_ind_sorts in *.
      destruct Universe.is_prop; auto.
      destruct Universe.is_sprop; auto.
      split; [apply fst in ind_sorts|apply snd in ind_sorts].
      * eapply Forall_impl; tea; cbn.
        intros. eapply Forall_impl; tea; simpl; intros.
        eapply leq_universe_subset; tea.
        apply weakening_env_global_ext_constraints; tea.
      * destruct indices_matter; [|trivial]. clear -ind_sorts HPΣ wfΣ wfΣ' Hext.
        induction ind_indices; simpl in *; auto.
        -- eapply (extends_wf_universe (Σ:=(Σ,φ)) Σ'); auto.
        -- destruct a as [na [b|] ty]; simpl in *; intuition eauto.
    + intros v onv.
      move: (onIndices v onv). unfold ind_respects_variance.
      destruct variance_universes as [[[univs u] u']|] => //.
      intros idx; eapply (All2_fold_impl idx); simpl.
      intros par par' t t' d.
      inv d; constructor; auto.
      ++ eapply weakening_env_cumulSpec; eauto.
      ++ eapply weakening_env_convSpec; eauto.
      ++ eapply weakening_env_cumulSpec; eauto.
  - red in onP |- *. eapply All_local_env_impl; eauto.
  - move: onVariance.
    rewrite /on_variance. destruct ind_universes => //.
    destruct ind_variance => //.
    intros [univs' [i [i' []]]]. exists univs', i, i'. split => //.
    all:eapply weakening_env_consistent_instance; tea.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop P ->
  wf Σ -> wf Σ' -> extends Σ Σ' -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ wfΣ' Hext HΣ.
  destruct HΣ as [onu onΣ].
  destruct Σ as [univs Σ]; cbn in *.
  induction onΣ; simpl. 1: congruence.
  assert (HH: extends {| universes := univs; declarations := Σ |} Σ'). {
    destruct Hext as [univs' [Σ'' HΣ'']]. split; eauto.
    exists (Σ'' ++ [(kn, d)]). now rewrite <- app_assoc.
  }
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= ->]. subst.
    clear Hext; eapply weakening_on_global_decl. 5:tea. all:eauto.
    destruct wfΣ. split => //. now depelim o2.
  - apply IHonΣ; auto.
    destruct wfΣ. split => //. now depelim o2.
Qed.

Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_prop P ->
  wf Σ -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_lookup_on_global_env; eauto.
  split => //. 
  - split; [lsets|csets].
  - exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constant_inv `{checker_flags} Σ P cst decl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_constant Σ cst decl ->
  on_constant_decl (lift_typing P) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.


Lemma declared_minductive_inv `{checker_flags} {Σ P ind mdecl} :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive (lift_typing P) (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv in Hmdecl; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.


Lemma declared_constructor_inv `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_prop (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor (lift_typing P) (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_projection_inv `{checker_flags} {Σ P mdecl idecl cdecl ref pdecl} :
  forall (HP : weaken_env_prop (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl),
  match idecl.(ind_ctors) return Type with
  | [c] =>
    let oib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in
      let (x, _) := x in x) in
    (match oib.(ind_cunivs) with
     | [cs] => sorts_local_ctx (lift_typing P) (Σ, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args c) cs
     | _ => False
    end) *
    on_projections mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) idecl (idecl.(ind_indices)) c *
    ((snd ref) < context_assumptions c.(cstr_args)) *
    on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) c (snd ref) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in let (x, _) := x in x)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl.
  forward onProjections.
  { eapply nth_error_Some_length in Hcdecl.
    destruct (ind_projs idecl); simpl in *; try lia. congruence. }
  destruct (ind_ctors idecl) as [|? []]; try contradiction.
  destruct ind_cunivs as [|? []]; try contradiction; depelim onConstructors.
  2:{ depelim onConstructors. }
  intuition auto.
  - destruct onProjections.
    destruct (ind_ctors idecl) as [|? []]; simpl in *; try discriminate.
    inv onConstructors. now eapply on_cargs in o.
  - destruct onProjections. eapply nth_error_Some_length in Hcdecl. lia.
  - destruct onProjections.
    eapply nth_error_alli in Hcdecl; eauto.
    eapply Hcdecl.
Qed.


Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop (lift_typing typing).
Proof.
  red. intros * wfΣ' Hext *.
  destruct T; simpl.
  - intros Ht.
    eapply (weakening_env (_, _)). 2:eauto. all:auto.
  - intros [s Ht]. exists s.
    eapply (weakening_env (_, _)). 4: eauto. all:auto.
Qed.

#[global]
 Hint Unfold weaken_env_prop : pcuic.

Lemma on_declared_constant `{checker_flags} {Σ cst decl} :
  wf Σ -> declared_constant Σ cst decl ->
  on_constant_decl (lift_typing typing) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply declared_constant_inv; tea.
  apply weaken_env_prop_typing.
Qed.



Lemma weaken_wf_local `{checker_flags} (Σ : global_env_ext) Σ' Γ :
  wf Σ -> extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros * wfΣ Hext wfΣ' *.
  intros wfΓ.
  eapply (env_prop_wf_local weakening_env); eauto.
Qed.

#[global]
Hint Resolve weaken_wf_local | 100 : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ref mdecl idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros Hdecl.
  split.
  - destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  - apply (declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl}
  {wfΣ : wf Σ}
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
     nth_error (ind_cunivs onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl idecl.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split.
  - apply (on_declared_inductive Hdecl).
  - apply (declared_constructor_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl cdecl pdecl} {wfΣ : wf Σ}
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl) :
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl *
  (idecl.(ind_ctors) = [cdecl]) *
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in let (x, _) := x in x) in
  (match oib.(ind_cunivs) with
  | [cs] => sorts_local_ctx (lift_typing typing) (Σ, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args cdecl) cs
    | _ => False
  end) *
  on_projections mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) idecl (idecl.(ind_indices)) cdecl *
  ((snd ref) < context_assumptions cdecl.(cstr_args)) *
  on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) cdecl (snd ref) pdecl.
Proof.
  have hctors : idecl.(ind_ctors) = [cdecl].
  { pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    move: X. destruct Hdecl. destruct d. cbn in *.
    move: e. destruct (ind_ctors idecl) as [|? []] => //.
    intros [= ->] => //. }
  split.
  - split => //.
    apply (on_declared_inductive Hdecl).
  - pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    destruct Hdecl. cbn in *. destruct d; cbn in *.
    now rewrite hctors in X.
Qed.


