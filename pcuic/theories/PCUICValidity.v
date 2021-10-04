(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICLiftSubst PCUICTyping PCUICSigmaCalculus
     PCUICClosed PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICUnivSubstitution PCUICConfluence
     PCUICUnivSubstitution PCUICConversion PCUICContexts 
     PCUICArities PCUICSpine PCUICInductives
     PCUICWellScopedCumulativity PCUICContexts PCUICWfUniverses.
     
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect ssrbool.

Derive Signature for typing cumul.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Arguments Nat.sub : simpl never.

Section Validity.
  Context `{cf : config.checker_flags}.

  Lemma isType_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isType Σ Γ T).
  Proof.
    red. intros.
    destruct X1 as [u Hu]; exists u; pcuic.
    unshelve eapply (weaken_env_prop_typing _ _ _ _ X0 _ _ (Some (tSort u))); eauto with pcuic.
    red. simpl. destruct Σ. eapply Hu.
  Qed.

  Hint Resolve isType_weaken_full : pcuic.

  Lemma isType_weaken :
    weaken_env_prop
      (lift_typing (fun Σ Γ (_ T : term) => isType Σ Γ T)).
  Proof.
    red. intros.
    unfold lift_typing in *. destruct T. now eapply (isType_weaken_full (_, _)).
    destruct X1 as [s Hs]; exists s. now eapply (isType_weaken_full (_, _)).
  Qed.
  Hint Resolve isType_weaken : pcuic.

  Lemma isType_extends (Σ : global_env) (Σ' : PCUICEnvironment.global_env) (φ : universes_decl) :
    wf Σ' ->
    extends Σ Σ' ->
    forall Γ : context,
    forall t0 : term,
    isType (Σ, φ) Γ t0 -> isType (Σ', φ) Γ t0.
  Proof.
    intros.
    destruct X1 as [s Hs].
    exists s.
    eapply (env_prop_typing PCUICWeakeningEnv.weakening_env (Σ, φ)); auto.
    simpl; auto. now eapply wf_extends.
  Qed.

  Lemma weaken_env_prop_isType :
    weaken_env_prop
    (lift_typing
        (fun (Σ0 : PCUICEnvironment.global_env_ext)
          (Γ0 : PCUICEnvironment.context) (_ T : term) =>
        isType Σ0 Γ0 T)).
  Proof.
    red. intros.
    red in X1 |- *.
    destruct T. now eapply isType_extends.
    destruct X1 as [s Hs]; exists s; now eapply isType_extends.
  Qed.

  Lemma isType_Sort_inv {Σ : global_env_ext} {Γ s} : wf Σ -> isType Σ Γ (tSort s) -> wf_universe Σ s.
  Proof.
    intros wfΣ [u Hu].
    now eapply inversion_Sort in Hu as [? [? ?]].
  Qed.

  Lemma isType_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isType (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isType Σ (subst_instance u Γ) (subst_instance u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [s Hs] X1.
    exists (subst_instance_univ u s).
    eapply (typing_subst_instance_decl _ _ _ (tSort _)); eauto.
  Qed.
  
  Lemma isWfArity_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity Σ (subst_instance u Γ) (subst_instance u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [isTy [ctx [s eq]]] X1.
    split. eapply isType_subst_instance_decl; eauto.
    exists (subst_instance u ctx), (subst_instance_univ u s).
    rewrite (subst_instance_destArity []) eq. intuition auto.
  Qed.
  
  Lemma isType_weakening {Σ Γ T} : 
    wf Σ.1 ->
    wf_local Σ Γ ->
    isType Σ [] T ->
    isType Σ Γ T.
  Proof.
    intros wfΣ wfΓ [s HT].
    exists s; auto.
    eapply (weaken_ctx (Γ:=[])); eauto.
  Qed.

  Lemma nth_error_All_local_env {P : context -> term -> option term -> Type} {Γ n d} :
    nth_error Γ n = Some d ->
    All_local_env P Γ ->
    on_local_decl P (skipn (S n) Γ) d.
  Proof.
    intros heq hΓ.
    epose proof (nth_error_Some_length heq).
    eapply (nth_error_All_local_env) in H; tea.
    now rewrite heq in H.
  Qed.

  Notation type_ctx := (type_local_ctx (lift_typing typing)).
  Lemma type_ctx_wf_univ Σ Γ Δ s : type_ctx Σ Γ Δ s -> wf_universe Σ s.
  Proof.
    induction Δ as [|[na [b|] ty]]; simpl; auto with pcuic.
  Qed.
  Hint Resolve type_ctx_wf_univ : pcuic.
  
  Lemma All2_fold_All2 (P : context_decl -> context_decl -> Type) Γ Δ : 
    All2_fold (fun _ _ => P) Γ Δ <~>
    All2 P Γ Δ.
  Proof.
    split; induction 1; constructor; auto.
  Qed.

  Lemma All2_map2_left {A B C D} {P : A -> A -> Type} Q (R : B -> D -> Type) {f : B -> C -> A} {l l' l'' l'''} : 
   All2 R l l''' ->
   All2 Q l' l'' ->
   #|l| = #|l'| ->
   (forall x y z w, R x w -> Q y z -> P (f x y) z) ->
   All2 P (map2 f l l') l''.
  Proof.
    intros hb ha hlen hPQ.
    induction ha in l, l''', hlen, hb |- *; simpl; try constructor; auto.
    - destruct l => //. simpl. constructor.
    - destruct l => //.
      noconf hlen. depelim hb.
      specialize (IHha _ _ hb H).
      simpl. constructor; auto. eapply hPQ; eauto.
  Qed.

  Lemma All2_map2_left_All3 {A B C} {P : A -> A -> Type} {f : B -> C -> A} {l l' l''} : 
    All3 (fun x y z => P (f x y) z) l l' l'' ->
    All2 P (map2 f l l') l''.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Lemma All3_impl {A B C} {P Q : A -> B -> C -> Type} {l l' l''} : 
    All3 P l l' l'' ->
    (forall x y z, P x y z -> Q x y z) ->
    All3 Q l l' l''.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Lemma map2_app {A B C} (f : A -> B -> C) l0 l0' l1 l1' :
    #|l0| = #|l1| -> #|l0'| = #|l1'| ->
    map2 f (l0 ++ l0') (l1 ++ l1') = 
    map2 f l0 l1 ++ map2 f l0' l1'.
  Proof.
    induction l0 in l0', l1, l1' |- *; simpl; auto.
    - destruct l1 => //.
    - destruct l1 => /= // [=] hl hl'.
      now rewrite IHl0.
  Qed.

  Notation liat := ltac:(lia) (only parsing).

  Lemma eq_binder_annots_eq_ctx (Σ : global_env_ext) (Δ : context) (nas : list aname) :
    All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
    PCUICEquality.eq_context_gen (PCUICEquality.eq_term Σ Σ) (PCUICEquality.eq_term Σ Σ) 
      (map2 set_binder_name nas Δ) Δ.
  Proof.
    induction Δ in nas |- * using PCUICInduction.ctx_length_rev_ind; simpl; intros hlen.
    - depelim hlen. simpl. reflexivity.
    - destruct nas as [|nas na] using rev_case => //;
      pose proof (All2_length hlen) as hlen';len in hlen'; simpl in hlen'; try lia.
      eapply All2_app_inv_l in hlen as (l1'&l2'&heq&alnas&allna).
      depelim allna. depelim allna.
      rewrite map2_app => /= //; try lia. unfold aname. lia.
      eapply app_inj_tail in heq as [<- <-].
      simpl. eapply PCUICContextRelation.All2_fold_app; auto.
      constructor. constructor.
      destruct d as [na' [d|] ty]; constructor; cbn in *; auto;
      try reflexivity.
  Qed.
  
  Lemma eq_term_set_binder_name (Σ : global_env_ext) (Δ : context) T U (nas : list aname) :
    All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
    PCUICEquality.eq_term Σ Σ T U ->
    PCUICEquality.eq_term Σ Σ (it_mkProd_or_LetIn (map2 set_binder_name nas Δ) T) (it_mkProd_or_LetIn Δ U) .
  Proof.
    intros a; unshelve eapply eq_binder_annots_eq_ctx in a; tea.
    eapply All2_fold_All2 in a.
    induction a in T, U |- *.
    - auto.
    - rewrite /= /mkProd_or_LetIn.
      destruct r => /=; intros; eapply IHa;
      constructor; auto. 
  Qed.

  Lemma All2_eq_binder_subst_context_inst l s k i Δ Γ : 
    All2
      (fun (x : binder_annot name) (y : context_decl) =>
        eq_binder_annot x (decl_name y)) l Γ ->
    All2
      (fun (x : binder_annot name) (y : context_decl) =>
      eq_binder_annot x (decl_name y)) l
        (subst_context s k
          (subst_instance i
              (expand_lets_ctx Δ Γ))).
  Proof.
    intros. eapply All2_map_right in X.
    depind X.
    * destruct Γ => //. constructor.
    * destruct Γ => //.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /=
        !lift_context_snoc; simpl.
      rewrite subst_context_snoc /= lift_context_length /=
        subst_instance_cons subst_context_snoc subst_instance_length
        subst_context_length lift_context_length.
        constructor. simpl. simpl in H. now noconf H.
        eapply IHX. simpl in H. now noconf H.
  Qed.

  Lemma wf_pre_case_predicate_context_gen {ci mdecl idecl} {p} :
    wf_predicate mdecl idecl p ->
    All2 (fun (x : binder_annot name) (y : context_decl) => eq_binder_annot x (decl_name y))
      (forget_types (pcontext p)) 
      (pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p)).
  Proof.
    move=> [] hlen /Forall2_All2.
    rewrite /pre_case_predicate_context_gen /ind_predicate_context.
    intros a; depelim a.
    destruct (pcontext p); noconf H.
    cbn.
    rewrite /inst_case_context /= subst_instance_cons subst_context_snoc Nat.add_0_r /subst_decl /map_decl /=.
    constructor. cbn. apply e.
    now eapply All2_eq_binder_subst_context_inst.
  Qed.

  Lemma validity_wf_local {Σ} Γ Δ:
    All_local_env
      (fun (Γ0 : context) (t : term) (T : option term) =>
      match T with
      | Some T0 => isType Σ (Γ,,, Γ0) T0 × Σ ;;; (Γ ,,, Γ0) |- t : T0
      | None => isType Σ (Γ,,, Γ0) t
      end) Δ ->
    ∑ xs, sorts_local_ctx (lift_typing typing) Σ Γ Δ xs.
  Proof.
    induction 1.
    - exists []; cbn; auto. exact tt.
    - destruct IHX as [xs Hxs].
      destruct t0 as [s Hs].
      exists (s :: xs). cbn. split; auto.
    - destruct IHX as [xs Hxs]. destruct t0 as [s Hs].
      exists xs; cbn. split; auto.
  Qed.

  Import PCUICOnFreeVars.

  Theorem validity_env :
    env_prop (fun Σ Γ t T => isType Σ Γ T)
      (fun Σ Γ => wf_local Σ Γ × All_local_env 
        (fun Γ t T => match T with Some T => (isType Σ Γ T × Σ ;;; Γ |- t : T) | None => isType Σ Γ t end) Γ).
  Proof.
    apply typing_ind_env; intros; rename_all_hyps.

    - split => //. induction X; constructor; auto.

    - destruct X as [_ X].
      have hd := (nth_error_All_local_env heq_nth_error X).
      destruct decl as [na [b|] ty]; cbn -[skipn] in *; destruct hd.
      + eapply isType_lift; eauto.
        now apply nth_error_Some_length in heq_nth_error.
      + eapply isType_lift; eauto.
        now apply nth_error_Some_length in heq_nth_error.
        now exists x.

    - (* Universe *) 
       exists (Universe.super (Universe.super u)).
       constructor; auto.
       now apply wf_universe_super.
        
    - (* Product *) 
      eexists.
      eapply isType_Sort_inv in X1; eapply isType_Sort_inv in X3; auto.
      econstructor; eauto.
      now apply wf_universe_product.

    - (* Lambda *)
      destruct X3 as [bs tybs].
      eapply isType_Sort_inv in X1; auto.
      exists (Universe.sort_of_product s1 bs).
      constructor; auto.

    - (* Let *)
      destruct X5 as [u Hu]. red in Hu.
      exists u.
      eapply type_Cumul.
      eapply type_LetIn; eauto. econstructor; pcuic.
      eapply cumul_alt. exists (tSort u), (tSort u); intuition auto.
      apply red1_red; repeat constructor.
      reflexivity.

    - (* Application *)
      destruct X3 as [u' Hu']. exists u'.
      move: (typing_wf_universe wf Hu') => wfu'.
      eapply (substitution0 (n := na) (T := tSort u')); eauto.
      apply inversion_Prod in Hu' as [na' [s1 [s2 Hs]]]; tas. intuition.
      eapply (weakening_equality (le:=true) (Γ' := []) (Γ'' := [vass na A])) in b0; pcuic.
      simpl in b0.
      eapply (type_equality (le:=true)); eauto. pcuic.
      etransitivity; tea.
      eapply into_equality => //.
      all:eauto with fvs.
      2:now eapply typing_wf_local in a0; eauto with fvs.
      do 2 constructor.
      apply leq_universe_product.

    - destruct decl as [ty [b|] univs]; simpl in *.
      * eapply declared_constant_inv in X; eauto.
        red in X. simpl in X.
        eapply isType_weakening; eauto.
        eapply (isType_subst_instance_decl (Γ:=[])); eauto. simpl.
        eapply weaken_env_prop_isType.
      * have ond := on_declared_constant wf H.
        do 2 red in ond. simpl in ond.
        simpl in ond.
        eapply isType_weakening; eauto.
        eapply (isType_subst_instance_decl (Γ:=[])); eauto.
     
     - (* Inductive type *)
      destruct (on_declared_inductive isdecl); pcuic.
      destruct isdecl.
      apply onArity in o0.
      eapply isType_weakening; eauto.
      eapply (isType_subst_instance_decl (Γ:=[])); eauto.

    - (* Constructor type *)
      destruct (on_declared_constructor isdecl) as [[oni oib] [cs [declc onc]]].
      unfold type_of_constructor.
      have ctype := on_ctype onc.
      destruct ctype as [s' Hs].
      exists (subst_instance_univ u s').
      eapply instantiate_minductive in Hs; eauto.
      2:(destruct isdecl as [[] ?]; eauto).
      simpl in Hs.
      eapply (weaken_ctx (Γ:=[]) Γ); eauto.
      eapply (substitution (Γ := []) (s := inds _ _ _) (Δ := []) (T := tSort _)); eauto.
      eapply subslet_inds; eauto. destruct isdecl; eauto.
      now rewrite app_context_nil_l.

    - (* Case predicate application *)
      assert (cu : consistent_instance_ext Σ (ind_universes mdecl) (puinst p)).
      { eapply (isType_mkApps_Ind_inv wf isdecl) in X8 as [parsubst [argsubst Hind]]; 
        repeat intuition auto. } 
      unshelve epose proof (ctx_inst_spine_subst _ X5); tea.
      eapply weaken_wf_local; tea.
      now apply (on_minductive_wf_params_indices_inst isdecl _ cu).
      eapply spine_subst_smash in X2; tea.
      destruct X4.
      destruct (on_declared_inductive isdecl) as [onmind oib].
      rewrite /ptm. exists ps. red.
      eapply type_mkApps; eauto.
      eapply type_it_mkLambda_or_LetIn; tea.
      have typred : isType Σ Γ (it_mkProd_or_LetIn predctx (tSort ps)).
      { eapply All_local_env_app_inv in a0 as [_ onp].
        eapply validity_wf_local in onp as [xs Hs].
        eexists _.
        eapply type_it_mkProd_or_LetIn_sorts; tea.
        exact X3.π2. }
      have wfps : wf_universe Σ ps.
      { pcuic. }
      eapply typing_spine_strengthen; tea.
      2:{ rewrite /predctx /case_predicate_context /case_predicate_context_gen.
          eapply equality_compare. 1-2:eauto with fvs.
          2:{ red.
              instantiate (1 := 
                it_mkProd_or_LetIn (pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p))
                    (tSort ps)).
            eapply PCUICEquality.eq_term_leq_term.
            eapply eq_term_set_binder_name. 2:reflexivity.
            now eapply wf_pre_case_predicate_context_gen. }
          rewrite subst_instance_app_ctx in X2.
          eapply spine_subst_smash_app_inv in X2 as [sppars spidx].
          epose proof (isType_case_predicate (puinst p) _ _ wfΓ isdecl cu wfps sppars).
          eauto with fvs. len.
          rewrite (wf_predicate_length_pars H0).
          now rewrite onmind.(onNpars). } 
      eapply wf_arity_spine_typing_spine; auto.
      rewrite subst_instance_app_ctx in X2.
      eapply spine_subst_smash_app_inv in X2 as [sppars spidx].
      split; auto.
      apply (isType_case_predicate (puinst p) _ _ wfΓ isdecl cu wfps sppars).
      2:{ rewrite (wf_predicate_length_pars H0).
          rewrite context_assumptions_map.
          now rewrite onmind.(onNpars). }
      eapply arity_spine_case_predicate; tea.

    - (* Proj *)
      pose proof isdecl as isdecl'.
      eapply declared_projection_type in isdecl'; eauto.
      subst ty.
      destruct isdecl' as [s Hs]. red in Hs.
      unshelve eapply isType_mkApps_Ind_inv in X2 as [parsubst [argsubst [sppar sparg 
        lenpars lenargs cu]]]; eauto.
      2:eapply isdecl.p1.
      eapply (typing_subst_instance_decl _ _ _ _ _ _ _ wf isdecl.p1.p1.p1) in Hs; eauto.
      simpl in Hs.
      exists (subst_instance_univ u s).
      unfold PCUICTypingDef.typing in *.
      eapply (weaken_ctx Γ) in Hs; eauto.
      rewrite -heq_length in sppar. rewrite firstn_all in sppar.
      rewrite subst_instance_cons in Hs.
      rewrite subst_instance_smash in Hs. simpl in Hs.
      eapply spine_subst_smash in sppar => //.
      eapply (substitution (Δ := [_]) sppar) in Hs.
      simpl in Hs.
      eapply (substitution (Γ' := [_]) (s := [c]) (Δ := [])) in Hs.
      simpl in Hs. rewrite (subst_app_simpl [_]) /= //.
      constructor. constructor.
      simpl. rewrite subst_empty.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ u _ cu); auto.
      rewrite subst_instance_to_extended_list.
      rewrite subst_instance_smash.
      rewrite (spine_subst_subst_to_extended_list_k sppar).
      assumption.
      
    - (* Fix *)
      eapply nth_error_all in X0 as [s Hs]; eauto.
      pcuic.
    
    - (* CoFix *)
      eapply nth_error_all in X0 as [s Hs]; pcuic.

    - (* Conv *)
      now exists s.
  Qed.

End Validity.

Corollary validity {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> isType Σ Γ T.
Proof.
  intros. eapply validity_env; try eassumption.
Defined.

(* To deprecate *)
Notation validity_term wf Ht := (validity (wfΣ:=wf) Ht).

(* This corollary relies strongly on validity to ensure 
   every type in the derivation is well-typed.
   It should be used instead of the weaker [invert_type_mkApps],
   which is only used as a stepping stone to validity.
 *)
Lemma inversion_mkApps {cf} {Σ} {wfΣ :  wf Σ.1} {Γ f u T} :
  Σ ;;; Γ |- mkApps f u : T ->
  ∑ A, Σ ;;; Γ |- f : A × typing_spine Σ Γ A u T.
Proof.
  induction u in f, T |- *. simpl. intros.
  { exists T. intuition pcuic. eapply typing_spine_refl.
    now eapply validity in X. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - pose proof (validity Hf).
    eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]]; tea.
    eexists _; intuition eauto.
    eapply validity in Hf'.
    econstructor; eauto with pcuic.
    constructor. all:eauto with pcuic.
    now eapply isType_apply in Hf'.
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [H' H'']].
    eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. 2:{ eassumption. }
    exists (tProd na' A' B'). intuition; eauto.
    eapply validity in Hf'.
    econstructor; eauto with wf.
    now eapply isType_equality_refl.
    eapply isType_apply in Hf'; tea.
    eapply typing_spine_strengthen; tea.
Qed.

(** "Economical" typing rule for applications, not requiring to check the product type *)
Lemma type_App' {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t na A B u} : 
  Σ;;; Γ |- t : tProd na A B ->
  Σ;;; Γ |- u : A -> Σ;;; Γ |- tApp t u : B {0 := u}.
Proof.
  intros Ht Hu.
  have [s Hs] := validity Ht.
  eapply type_App; eauto.
Qed.

(** This principle is useful when the type [tty] is an arity (of the form [it_mkProd_or_LetIn _ (tSort _)]),
    as it avoids having to give intermediate well-typing and cumulativity proofs. *)
Lemma type_mkApps_arity {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u tty T} :
  Σ;;; Γ |- t : tty ->
  arity_spine Σ Γ tty u T -> 
  Σ;;; Γ |- mkApps t u : T.
Proof.
  intros Ht Hty.
  pose proof (validity Ht).
  eapply type_mkApps; tea.
  eapply wf_arity_spine_typing_spine; tea.
  constructor; tas.
Qed.
