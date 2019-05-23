(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR.
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim ESubstitution EInversion.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Require Import Lia.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Ltac inv H := inversion H; subst; clear H.

Lemma is_constructor_extract `{Fuel} Σ n L L' :
  PCUICTyping.is_constructor n L -> Forall2 (fun (a : PCUICAst.term) (e : E.term) => extract Σ [] a = Checked e) L L' -> is_constructor n L'.
Proof.
Admitted.


(* Lemma mkApps_inj a b l1 l2  : *)
(*   mkApps a l1 = mkApps b l2 -> (~ exists a1 a2, a = tApp a1 a2) -> (~ exists b1 b2, b = tApp b1 b2) -> *)
(*   a = b /\ l1 = l2. *)
(* Proof. *)
(* (*   induction l1 in a, b, l2 |- *; cbn; intros. *) *)
(* (*   - destruct l2; eauto. cbn in H. subst. destruct H0. clear H1. *) *)
(* (*     revert b t; induction l2; cbn. *) *)
(* (*     + eauto. *) *)
(* (*     + intros. edestruct IHl2 as (? & ? & ?). eauto. *) *)
(* (*   - destruct l2; eauto. cbn in H. *) *)
(* (*     + subst. edestruct H1. *) *)
(* (*       clear. revert a a0; induction l1; cbn. *) *)
(* (*       * eauto. *) *)
(* (*       * intros. edestruct IHl1 as (? & ? & ?). eauto. *) *)
(* (*     + cbn in H. *) *)
    

(* (*     epose proof (IHl1 _ _ _ eq_refl). *) *)
(* (* Qed. *)     *)
(* Admitted. *)


(** ** Assumptions on typing of tCase *)

Lemma no_empty_case_in_empty_context Σ ind npar p c T :
  Σ;;; [] |- PCUICAst.tCase (ind, npar) p c [] : T -> False.
Proof.
Admitted.


Lemma prop_case_is_singleton `{Fuel} Σ ind npar p T i u args brs mdecl idecl :
  PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl ->
  PCUICAst.ind_npars mdecl = npar ->
  is_type_or_proof Σ [] (PCUICAst.tConstruct ind i u) = Checked true ->
  Σ;;; [] |- PCUICAst.tCase (ind, npar) p (PCUICAst.mkApps (PCUICAst.tConstruct ind i u) args) brs : T -> #|brs| = 1 /\ i = 0 /\
                                                                                                              Forall (fun a => is_type_or_proof Σ [] a = Checked true) (skipn (npar) args).
Proof.
Admitted.

Inductive extr_pre (Σ : PA.global_context) t T :=
  { extr_typed : Σ ;;; [] |- t : T;
    extr_env_axiom_free : axiom_free (fst Σ) }.

Theorem subject_reduction_eval : forall (Σ : PCUICAst.global_context) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> PCUICWcbvEval.eval Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred % wcbeval_red. eapply subject_reduction; eauto.
Qed.

Lemma cumul_is_arity:
  forall (H : Fuel) (Σ : PCUICAst.global_context) (T' T'' : PCUICAst.term),
    Σ;;; [] |- T'' <= T' -> is_arity Σ [] H T'' = is_arity Σ [] H T'.
Proof.
  intros H Σ T' T''.
Admitted.

Lemma eval_is_type `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) (* T : *)
  (* wf Σ -> Σ ;;; [] |- t : T ->  *) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] t = Checked true -> Extract.is_type_or_proof Σ [] v = Checked true.
Proof. 
  (* intros. *)
  (* unfold is_type_or_proof in *. *)
  (* simpl in *. destruct ? in H0. *)
  (* - destruct (type_of_sound _ X0 E) as []. *)
  (*   eapply subject_reduction_eval in t0; eauto. *)
  (*   destruct ?. *)
  (*   destruct (type_of_sound _ t0 E0) as []. *)
  (*   destruct ? in H0. *)
  (*   + erewrite <- cumul_is_arity in E1. rewrite E1. all:eauto. *)
  (*   + erewrite <- cumul_is_arity in E1. rewrite E1. all:eauto. *)
  (*     destruct ? in H0; inv H0. admit.  *)
  (*   + edestruct type_of_complete; eauto. congruence. *)
  (* - edestruct type_of_complete; eauto. congruence. *)
Admitted.

Lemma eval_is_type_backwards `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) (* T : *)
  (* wf Σ -> Σ ;;; [] |- t : T -> *) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] v = Checked true -> Extract.is_type_or_proof Σ [] t = Checked true.
Proof.
  intros.
  (* destruct (type_of_sound _ X0) as (T' & [] & ?). *)
  (* eapply subject_reduction_eval in t0; eauto. *)
  (* destruct (type_of_sound _ t0) as (T'' & [] & ?). *)
  (* unfold is_type_or_proof in *. rewrite e, e0 in *. *)
  (* simpl in *. *)

  (* destruct (is_arity _ _ _ T') eqn:E1. reflexivity. *)
    
Admitted.
  
(** ** Concerning fixpoints *)

Fixpoint fix_subst' n l :=
  match n with
  | 0 => []
  | S n => PCUICAst.tFix l n :: fix_subst' n l
  end.

Fixpoint fix_subst'' n a l : list PCUICAst.term :=
  match n with
  | 0 => a
  | S n => fix_subst'' n (a ++ [PCUICAst.tFix l n])%list l
  end.


Lemma fix_subst_app l1 l2 : (PCUICTyping.fix_subst (l1 ++ l2) = fix_subst' (#|l1|) (l1 ++ l2) ++ fix_subst' (#|l1|) (l1 ++ l2)) % list.
Admitted.

Fixpoint fix_decls' (acc : list PCUICAst.context_decl) (ds : list (BasicAst.def PCUICAst.term)) {struct ds} :
  list PCUICAst.context_decl :=
  match ds with
  | [] => acc
  | d :: ds0 => fix_decls' (PCUICAst.vass (BasicAst.dname d) (dtype d) :: acc) ds0
  end.

Lemma fix_decls_app A mfix1 mfix2 :
  fix_decls' A (mfix1 ++ mfix2) = fix_decls' (fix_decls' A mfix1) mfix2.
Proof.
  revert A; induction mfix1; cbn; intros.
  - reflexivity.
  - eapply IHmfix1.
Qed.

Lemma subslet_fix_subst' Σ mfix1 mfix2 :
  subslet Σ [] (fix_subst' (#|mfix1|) mfix2) (fix_decls' [] mfix1).
Proof.
  revert mfix2. induction mfix1 using rev_ind; cbn; intros.
  - econstructor.
  - rewrite app_length. cbn. rewrite plus_comm. cbn.
    rewrite fix_decls_app. cbn. econstructor.
    eapply IHmfix1.
    admit (* typing *).
Admitted.

Lemma subslet_fix_subst Σ mfix1 mfix2 :
  subslet Σ [] (PCUICTyping.fix_subst mfix2) (fix_decls mfix1).
Proof.
Admitted.

Lemma fix_subst'_subst mfix :
  fix_subst' (#|mfix|) mfix = PCUICTyping.fix_subst mfix.
Admitted.


Fixpoint efix_subst' n l :=
  match n with
  | 0 => []
  | S n => tFix l n :: efix_subst' n l
  end.
Lemma efix_subst'_subst mfix :
  efix_subst' (#|mfix|) mfix = fix_subst mfix.
Admitted.

Lemma efix_subst_app l1 l2 : (fix_subst (l1 ++ l2) = efix_subst' (#|l1|) (l1 ++ l2) ++ efix_subst' (#|l1|) (l1 ++ l2)) % list.
Admitted.

(** ** Proof inversions *)

Lemma is_type_ind:
  forall (Σ : PCUICAst.global_context) (i : inductive) (u : universe_instance) (T : PCUICAst.term) (fuel : Fuel),
    Σ;;; [] |- tInd i u : T -> is_type_or_proof Σ [] (tInd i u) = Checked true.
Proof.
  
Admitted.

Lemma is_type_App `{Fuel} Σ a l T :
  Σ ;;; [] |- PCUICAst.mkApps a l : T -> 
  is_type_or_proof Σ [] a = Checked true ->
  is_type_or_proof Σ [] (PCUICAst.mkApps a l) = Checked true.
Proof.
Admitted.
  
Lemma is_type_or_proof_lambda `{Fuel} Σ Γ na t b :
  Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) = Checked true ->
  Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b = Checked true.
Admitted.

Lemma is_type_or_proof_mkApps `{Fuel} Σ Γ a l :
  Extract.is_type_or_proof Σ Γ a = Checked true <->
  Extract.is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = Checked true.
Admitted.

Lemma is_type_subst1 `{Fuel} (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) :
  Extract.is_type_or_proof Σ ([],, PCUICAst.vass na t) b = Checked true ->
  Extract.is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked true.
Proof.
Admitted.

(** ** extract and mkApps *)

Lemma extract_Apps `{Fuel} Σ Γ a args x :
  extract Σ Γ (PCUICAst.mkApps a args) = Checked x ->
  {e : _ & (extract Σ Γ a = Checked e) *
           { l : list E.term & (All2 (fun a e => extract Σ Γ a = Checked e) args l) *
                               (* (x = mkApps e l) *)
                               match e with tBox => x = tBox | _ => (x = mkApps e l) end }}%type.
Proof.
  revert a x. induction args using rev_ind; intros.
  - cbn in H0. repeat eexists; eauto. destruct x; eauto.
  - rewrite mkApps_snoc in H0. assert (H17 := H0). simpl in H0.
    destruct ?. destruct a0. all:try congruence.
    + inv H0. exists tBox. split. eapply is_type_extract. admit. 
      eapply is_type_or_proof_mkApps with (l := [x]) in E. 
      eapply is_type_extract in E. eapply IHargs in E as (? & ?  & ? & ? &?).
      Lemma mkApps_tbox:
        forall x0 (x1 : list E.term), E.tBox = mkApps x0 x1 -> x0 = tBox.
      Proof.
        intros.
        induction x1 using rev_ind; rewrite ?emkApps_snoc in *. cbn in H. inv H. eauto.
        inv H.
      Qed.
      destruct x0; try eapply mkApps_tbox in y; inv y.
      destruct (extract Σ Γ x) eqn:EE.
      * repeat eexists; eauto. eapply All2_app. eauto. 
        repeat econstructor. eauto.
      * admit.
    + destruct ?. destruct ?. all:try congruence. inv H0.
      eapply IHargs in E0 as (? & ? & ? & ? & ?).
      exists x0. split. eauto. exists (x1 ++ [a1])%list.
      split. eapply All2_app. eauto. repeat econstructor. eauto.
      rewrite emkApps_snoc. destruct x0; subst; eauto.
      admit.      
Admitted.

Lemma extract_Apps2 `{Fuel} Σ Γ a args e l :
  extract Σ Γ a = Checked e -> Forall2 (fun a e => extract Σ Γ a = Checked e) args l ->                                                                                  extract Σ Γ (PCUICAst.mkApps a args) = Checked (mkApps e l).
Proof.
Admitted.

Lemma extract_tInd `{Fuel} Σ i u t :
  extract Σ [] (tInd i u) = Checked t -> t = tBox.
Proof.
  intros ?. simpl in *. destruct is_type_or_proof eqn:E1; try destruct a; now inv H0.
Qed.

(** ** Concerning extraction of constants *)

Fixpoint extract_global_decls' `{F:Fuel} univs Σ1 Σ : typing_result E.global_declarations :=
  match Σ, Σ1 with
  | [], [] => ret []
  | PCUICAst.ConstantDecl kn cb :: Σ0, _ :: Σ1 =>
      cb' <- extract_constant_body (Σ1, univs) cb;;
      Σ' <- extract_global_decls' univs Σ1 Σ0;; ret (E.ConstantDecl kn cb' :: Σ')
  | PCUICAst.InductiveDecl kn mib :: Σ0, _ :: Σ1 =>
      mib' <- extract_mutual_inductive_body (Σ1, univs) mib;;
           Σ' <- extract_global_decls' univs Σ1 Σ0;; ret (E.InductiveDecl kn mib' :: Σ')
  | _, _ => ret []
   end.

Lemma extract_global_decls_eq `{Fuel} u Σ :
  extract_global_decls u Σ = extract_global_decls' u Σ Σ.
Proof.
  induction Σ.
  - reflexivity.
  - simpl. destruct a.
    + destruct ?; try congruence. now rewrite IHΣ.
    + destruct ?; try congruence. now rewrite IHΣ.
Qed.

Require Import PCUIC.PCUICWeakeningEnv.
Lemma extract_constant:
  forall (Σ : PCUICAst.global_context) (c : ident) (decl : PCUICAst.constant_body) (body : PCUICAst.term)
    (u : universe_instance) (fuel : Fuel) (Σ' : list E.global_decl),
    wf Σ ->
    PCUICTyping.declared_constant Σ c decl ->
    extract_global Σ = Checked Σ' ->
    PCUICAst.cst_body decl = Some body ->
    exists decl' : constant_body, exists ebody,
        declared_constant Σ' c decl' /\
        extract Σ [] (PCUICUnivSubst.subst_instance_constr u body) = Checked ebody /\ cst_body decl' = Some ebody.
Proof.
  intros.

  pose (P := fun  Σ (_ : PCUICAst.context) trm (tp : option PCUICAst.term) => match tp with Some tp => { '(t',tp') : _ & (extract Σ [] trm = Checked t') * (extract Σ [] tp = Checked tp')}%type | None => False end).
  assert (H' := H).
  eapply weaken_lookup_on_global_env with (P0 := P) in H; subst P; eauto.
  - unfold on_global_decl, on_constant_decl in H. rewrite H1 in H.
    destruct H as [[] []].
    exists (Build_constant_body t0 (Some t)), t. simpl. repeat split.
    unfold declared_constant. destruct Σ as [decls univ].
    unfold PCUICTyping.declared_constant in *. simpl in H'.
    admit. admit.
  - unfold weaken_env_prop. intros. destruct T; try tauto. admit.
  - unfold on_global_env. destruct Σ. cbn. revert H0 X. clear.
    (* revert t Σ'; induction g; simpl; intros. *)
    (* + inv H0. econstructor. admit. *)
    (* + destruct ? in H0; inv H0. econstructor. eapply IHg; auto. admit. admit. admit. *)
    (*   destruct a; simpl. *)
    (*   * unfold on_constant_decl. destruct ?. *)
      
Admitted.

(** ** Concerning context conversion *)

Require Import PCUIC.PCUICGeneration.

Inductive red_decls Σ Γ Γ' : forall (x y : PCUICAst.context_decl), Type :=
| conv_vass na na' T T' : isWfArity_or_Type Σ Γ' T' -> red Σ Γ T T' ->
                      red_decls Σ Γ Γ' (PCUICAst.vass na T) (PCUICAst.vass na' T')

| conv_vdef_type na na' b T T' : isWfArity_or_Type Σ Γ' T' -> red Σ Γ T T' ->
                             red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b T')

| conv_vdef_body na na' b b' T : Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
                                                  red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b' T).

Notation red_context := (context_relation red_decls).

Lemma context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
     forall Γ' : PCUICAst.context, red_context Σ Γ Γ' -> Σ;;; Γ' |- t : T).
Admitted.

Lemma extract_context_conversion `{Fuel} :
env_prop
  (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
     forall Γ' : PCUICAst.context, red_context Σ Γ Γ' -> forall a ea, extract Σ Γ a = Checked ea -> extract Σ Γ' a = Checked ea).
Admitted.

(** ** Corrcectness of erasure *)

Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v H. revert T pre.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T pre fuel Σ' t' Ht' HΣ'.
  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq. inv pre.
    destruct a0.
    + inv Ht'.
      exists tBox. split. 2:repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. econstructor. 3:eauto. all: eauto. 
    + destruct (extract Σ [] f) as [ ef | ] eqn:Ef ; try congruence.
      destruct (extract Σ [] a) as [ ea | ] eqn:Ea; try congruence.
      inv Ht'. 
      edestruct (type_mkApps_inv Σ [] f [a] T) as (? & U & [? ?] & ?); eauto. 
      inv t1. inv X2. pose proof (subject_reduction_eval _ [] _ _ _ extr_env_wf t0 H).
      eapply type_Lambda_inv in X2 as (? & ? & [? ?] & ?).
      
      eapply IHeval1 in Ef as (vef & ? & ?) ; eauto.
      eapply IHeval2 in Ea as (vea & ? & ?) ; eauto.
      
      simpl in H2. destruct ?; try now cbn in *; congruence.
      destruct a0.
      * inv H2. eapply is_type_or_proof_lambda in E.
        edestruct (IHeval3) as (? & ? & ?).
        -- econstructor; eauto. eapply substitution0. eauto. eauto. eapply subject_reduction_eval; try eapply H0; eauto. 
           eapply cumul_trans in X0. 2:eauto. eapply cumul_Prod_inv in X0 as []. econstructor. eauto. eauto. eapply c1.
        -- eapply extract_subst1; eauto. 2:{ eapply is_type_extract. eauto. }
           eapply subject_reduction_eval; eauto.
           edestruct cumul_Prod_inv.
           eapply cumul_trans; eauto.
           econstructor; eauto. eapply c1.
        -- eauto.
        -- exists tBox. cbn in H6. split. 2: eapply eval_box; eauto.
           now eapply eval_tBox_inv in H6 as ->.
      * destruct ?; try congruence.
        inv H2. edestruct IHeval3 as (? & ? & ?).
        -- econstructor; eauto.
           eapply substitution0. eauto. eauto. eapply subject_reduction_eval; try eapply H0; eauto. 
           eapply cumul_trans in X0. 2:eauto. eapply cumul_Prod_inv in X0 as []. 
           econstructor. eauto. eauto. eapply c1. 
        -- shelve.
        -- eauto.
        -- exists x2. split. eauto. econstructor. eauto. exact H5. eauto.
           Unshelve. shelve. shelve. eapply extract_subst1; eauto.
           eapply subject_reduction_eval; eauto.
           edestruct cumul_Prod_inv.
           eapply cumul_trans; eauto.
           econstructor; eauto. eapply c1.
      * econstructor; eauto.
      * econstructor; eauto.
    + congruence.
  - simpl in Ht'. inv pre. eapply type_tLetIn_inv in extr_typed0 as (? & U & [[] ?] & ?); eauto.
    destruct Extract.is_type_or_proof eqn:Heq. destruct a; try congruence.
    + inv Ht'.  exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto.
      econstructor; eauto.
    + destruct (extract _ _ b0) as [ eb0 | ] eqn:Eb0; try congruence.
      destruct (extract _ _ b1) as [ eb1 | ] eqn:Eb1; try congruence.
      inv Ht'. 

      eapply IHeval1 in Eb0 as (veb0 & ? & ?). 3:eauto.
      edestruct IHeval2 as (veb1 & ? & ?).
      4:{ exists veb1. split. eauto. econstructor. 2:eauto. eauto. }
      -- econstructor; eauto. eapply substitution_let; eauto.
         eapply context_conversion. 3: eassumption. all:eauto.
         econstructor. econstructor. econstructor 3. eapply subject_reduction_eval; eauto.
         eapply wcbeval_red. eauto.
      -- eapply extract_subst1_vdef; eauto.
         eapply context_conversion. eauto. 2:eauto.
         econstructor. eauto. eauto.
         econstructor. econstructor. econstructor. eapply subject_reduction_eval; eauto.
         eapply wcbeval_red. eauto.
         eapply extract_context_conversion. eauto.
         3:{ econstructor. econstructor. econstructor 3.
             eapply subject_reduction_eval; eauto.
             eapply wcbeval_red. eauto. }
         all: eauto. econstructor. eauto. econstructor; eauto.
      -- eauto.
      -- econstructor; eauto. 
    + congruence.
  - cbn in isdecl. inv isdecl.    
  - cbn in isdecl. inv isdecl.    
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq.
    destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto.
      econstructor; eauto.
    + destruct extract eqn:He; try congruence.
      inv pre. assert (HT := extr_typed0). eapply type_Case_inv in extr_typed0 as [ [[[[[[[[]]]]]]]] [[]]  ].
      destruct p0 as [[[[[]]]]]. 

      assert (t17 := t0).
      eapply subject_reduction_eval in t0; eauto.
      eapply type_mkApps_inv in t0 as (? & ? & [] & ?); eauto.
           
      destruct is_box eqn:Ea.
      * destruct a; inversion Ea; clear Ea. 

        destruct brs eqn:Hbrs.
        -- edestruct (no_empty_case_in_empty_context); eauto.
           
           
          (*  econstructor; eauto. *)

          (* inv Ht'. *)
           
          (*  eapply type_Construct_inv in t0 as [ [[]] ]. destruct y as [[[]]]. *)
          (*  destruct d. cbn in H2. subst. destruct p0. *)
          (*  unfold types_of_case in e. destruct ? in e; inv e. *)
          (*  destruct p0. destruct ? in H5; inv H5. destruct p0. destruct ? in H6; inv H6. *)

          (*  Lemma map_optinons_out_length A (L : list (option A)) L' : *)
          (*    map_option_out L = Some L' -> #|L| = #|L'|. *)
          (*  Proof. *)
          (*    revert L'; induction L; inversion 1; subst; cbn. *)
          (*    - reflexivity. *)
          (*    - destruct a; inv H1. destruct ? in H2; inv H2. cbn. f_equal. *)
          (*      eauto. *)
          (*  Qed. *)
          (*  eapply map_optinons_out_length in E1. inv a0. *)
          (*  unfold build_branches_type in E1. rewrite mapi_length in E1. *)
          (*  destruct o. cbn in E1. destruct ind_ctors; inv E1. *)
          (*  cbn in *. clear Heq. *)
          (*  destruct l1 ; inv e0. *)
        -- eapply is_type_extract in He.
           edestruct prop_case_is_singleton as (? & ? & ?). eauto. eauto. 
           unfold PCUICTyping.declared_inductive.
           eapply is_type_or_proof_mkApps.
           eapply eval_is_type. eauto. eauto.
           eapply subject_reduction. eauto. eapply HT.
           eapply PCUICReduction.red_case. eapply refl_red.
           eapply wcbeval_red. eauto.
           eapply All_All2. 2:{ intros []. unfold on_Trel. cbn. intros. eapply refl_red. } instantiate (1 := fun _ => True).
           econstructor; eauto. clear. induction l3; econstructor; eauto. 
           
           inv a0. destruct l3; inv H1. inv X0. 
           destruct p0. destruct p1. destruct ? in Ht'; inv Ht'.
           unfold PCUICTyping.iota_red in IHeval2. simpl in IHeval2.
           destruct X. destruct y. cbn in e; subst.
           eapply typing_spine_skipn in t1 as [].  
           
           edestruct IHeval2 as (? & ? & ?).
           ++ econstructor; eauto. eapply PCUICGeneration.type_mkApps; eauto.
           ++ eapply extract_Apps2. eauto.
              instantiate (1 := repeat tBox n0). 
              (* unfold types_of_case in *. destruct ? in e; inv e. *)
             (*  destruct p0. destruct ? in H4; inv H4. destruct p0. *)
             (*  destruct ? in H5; inv H5. *)
             (*  unfold build_branches_type in E2. destruct o. destruct ind_ctors. cbn in *. congruence. *)
             (*  destruct ind_ctors; cbn in E2. 2:{  destruct p0. destruct p0. destruct ? in E2. destruct p1. destruct p1. *)
             (*                                      destruct ? in E3. destruct ? in E3. destruct ? in E3. inv E3. *)
             (*                                      destruct ? in E2. inv E2. destruct ? in E3. destruct ? in E2. destruct ? in E2. *)
             (*                                      destruct ? in E2. inv E2. destruct ? in E3. inv E3. inv E3. *)
             (*                                      all: try congruence. } *)
             (*  destruct p0. destruct p0. destruct (instantiate_params (ind_params m) (firstn (PCUICAst.ind_npars m) l) *)
             (* (PCUICLiftSubst.subst (inds (inductive_mind ind) u0 (PCUICAst.ind_bodies m)) 0 *)
             (*                       (PCUICUnivSubst.subst_instance_constr u0 t6))); inv E2. *)
             (*  destruct ? in H4; inv H4. destruct ? in E2. destruct ? in E2. inv E2. *)
           (*  cbn in *. destruct l1; inv e0.  *)
              (* should follow from H3 *) admit.
           ++ eauto.
           ++ exists x2. split; eauto. subst. cbn in e1.
              now rewrite mkAppBox_repeat.
      * destruct monad_map eqn:Em; try congruence.
        inv Ht'. assert (He' := He). eapply IHeval1 in He as (? & ? & ?); eauto.
        2:{ econstructor; eauto. }
        eapply extract_Apps in H1 as (? & ? & ? & ? & ?).
        simpl in e. destruct ? in e; [ | admit (* goes away with fuel *) ]. destruct a3; inv e.
        { subst. exfalso. enough (is_box a = true) by congruence.
          enough (extract Σ [] discr = Checked tBox). rewrite H1 in He'; now inv He'.
          eapply is_type_extract.
          eapply eval_is_type_backwards. eauto. rewrite <- is_type_or_proof_mkApps.
          eauto. }

        eapply type_Construct_inv in t0 as [ [[]] ]. destruct y0 as [[[]]].
        destruct d. cbn in H3. subst. destruct p0.
        unfold types_of_case in e. destruct ? in e; inv e.
        destruct ? in H5; inv H5. destruct p0. destruct ? in H6; inv H6. destruct p0.
        destruct ? in H5; inv H5.
        
    (*     destruct (nth_error brs c) eqn:E3. *)
    (*     2:{  (* if looking up c in (ind.ctors o0) works, looking up c in brs must work *) *)
    (*       (* eapply nth_error_None in E3. *) *)
    (*       (* Lemma All2_length X Y (P : X -> Y -> Type) x y : *) *)
    (*       (*   All2 P x y -> #|x| = #|y|. *) *)
    (*       (* Proof. *) *)
    (*       (*   induction 1; cbn; congruence. *) *)
    (*       (* Qed. *) *)
    (*       (* eapply All2_length in a0. rewrite a0 in *. clear a0. *) *)
    (*       (* pose proof (nth_error_Some (PCUICAst.ind_ctors o0) c). rewrite H4 in H5. *) *)
    (*       (* assert (c < #|PCUICAst.ind_ctors o0|) by (eapply H5; intuition congruence). *) *)
    (*       (* enough (#|l2| = #|PCUICAst.ind_ctors o0|) by omega. *) *)
    (*       admit. *)
    (*     } *)
    (*     pose proof (monad_map_All2 _ _ _ _ _ Em) as [[] [] ] % (All2_nth_error_Some c p0); eauto. *)
    (*     destruct ?; inv e2. *)
    (*     edestruct (All2_nth_error_Some _ _ a0 E3) as ([] & ? & ? & ?). *)
    (*     eapply typing_spine_skipn in t1 as (? & ?). *)
    (*     subst. cbn in e3. subst. edestruct IHeval2 as (? & ? & ?). *)
    (*     -- econstructor; eauto. unfold PCUICTyping.iota_red. *)
    (*        eapply PCUICGeneration.type_mkApps. *)
    (*        rewrite <- nth_default_eq. unfold nth_default. rewrite E3. *)
    (*        eauto. eauto. *)
    (*     -- unfold PCUICTyping.iota_red. eapply extract_Apps2. *)
    (*        rewrite <- nth_default_eq. unfold nth_default. rewrite E3. *)
    (*        eauto.  *)
    (*        eapply Forall2_skipn. now eapply All2_Forall. *)
    (*     -- eauto. *)
    (*     -- exists x2. split. eauto. econstructor. *)
    (*        eassumption. *)
    (*        unfold iota_red. rewrite <- nth_default_eq. *)
    (*        unfold nth_default. rewrite e. cbn. eauto. *)
        (* + congruence. *) admit.
    + admit.
  - pose (Ht'' := Ht'). eapply extract_Apps in Ht'' as (e & He & l & Hl & ?).
    inv pre.
    simpl in He. destruct is_type_or_proof eqn:Heq. destruct a. inv He. subst.
    + exists tBox. split. 2:econstructor; eauto.
      eapply is_type_extract. eapply is_type_App in Heq. eapply eval_is_type.
      2:exact Heq. econstructor; eauto. eauto.      
    + destruct extract_mfix eqn:E. inv He. 2:congruence. subst.
      enough (exists l', Forall2 (eval Σ') l l' /\ Forall2 (fun a e => extract Σ [] a = Checked e) args' l' /\ (PCUICTyping.is_constructor narg args' -> is_constructor narg l')) as (l' & ? & ? & ?).

      assert (E' := E).
      pose proof (monad_map_All2 _ _ (fun d : BasicAst.def PCUICAst.term =>
         dbody' <- extract Σ (fix_decls mfix ++ [])%list (BasicAst.dbody d);;
                ret {| E.dname := BasicAst.dname d; E.dbody := dbody'; E.rarg := BasicAst.rarg d |})).
      eapply H6 in E. clear H6.

      assert (H'' := H).
      unfold PCUICTyping.unfold_fix in H. destruct ? in H; try congruence.
      eapply All2_nth_error_Some in E as (? & ? & ?); eauto.
      inv e0. destruct ? in H7; inv H7. inv H.
      assert (exists s', monad_map (extract Σ []) (PCUICTyping.fix_subst mfix) = Checked s') as [s' ?] by admit. (* this goes away without fuel *)

      edestruct IHeval as (? & ? & ?).
      
      2:{ eapply extract_Apps2; eauto. eapply (extract_subst Σ [] _ []).
          - eauto.
          - eapply subslet_fix_subst.
          - rewrite app_context_nil_l. rewrite app_nil_r in E. eauto.
          - admit.
          - eauto.
          - eapply monad_map_Forall2. eauto. }

      econstructor. eapply subject_reduction.
      eauto. exact extr_typed0. all:eauto.
      etransitivity. eapply PCUICReduction.red_mkApps.
      eapply refl_red. eapply All2_impl. exact X. intros. now eapply wcbeval_red.

      eapply PCUICReduction.red_step. econstructor; eauto. eapply refl_red.

      exists x. split. eauto. econstructor. 

      unfold unfold_fix. rewrite e. simpl. f_equal. eauto. eauto.

      assert (subst0 (fix_subst a) a0 = subst0 s' a0) by admit. (* substituting with extracted fix_subst is the same as substituing with fix_subst on results of extraction (like a0), since variables where they differ (extracted fix_subst is box where fix_subst is fix ... := box) are replaced by box in a0 already *)
      rewrite H8. eauto.

      1:{ clear H1. revert H0  X Hl narg  H extr_typed0 extr_env_axiom_free0 extr_env_wf HΣ'. clear.
          intros H0. intros. revert l Hl T extr_typed0. dependent induction H0 using All2_ind_rev; intros.
          - inv Hl. exists []. repeat split; eauto. unfold PCUICTyping.is_constructor, is_constructor.
            destruct narg; cbn; eauto.
          - eapply All2_app_inv in X as ( []  & [[]]). inv a0. inv X0.
            eapply All2_app_inv in Hl as ( []  & [[]]). inv a1. inv H5.
            eapply last_inv in e as (-> & ->).
            eapply type_mkApps_inv in extr_typed0 as (? & ? & [] & ?) ; eauto.
            eapply typing_spine_inv_app in t0 as [[] []].
            eapply IHAll2 in a as (? & ? & ? & ?).  
            
            eapply r in H3 as (? & ? & ?); eauto. 
            eexists (x2 ++ [x3])%list. repeat split.
            eapply Forall2_app; eauto.
            eapply Forall2_app; eauto.

            Hint Resolve Forall2_app.
            intros.
            eapply is_constructor_extract. eauto. eauto.
              
            econstructor; eauto. all:eauto.
            eapply PCUICGeneration.type_mkApps; eauto. }
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eapply Heq.
      econstructor; eauto.
    + inv Ht'. inv pre.
      edestruct (extract_constant _ c decl body u _ _  extr_env_wf H HΣ' H0) as (decl' & ebody & ? & ? & ?); eauto.
      edestruct IHeval as (? & ? & ?).
      * econstructor; eauto.
        eapply subject_reduction. eauto. exact extr_typed0.
        eapply PCUICReduction.red1_red. econstructor; eauto.
      * eauto.
      * eauto.
      * exists x. split. eauto. econstructor. eauto. eauto. eauto. 
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a0.
    + inv Ht'. exists tBox. split. 2:repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eapply Heq.
      econstructor; eauto.
    + destruct ?; try congruence. inv Ht'. inv pre.
      eapply type_proj_inv in extr_typed0 as ( [[[[args' mdecl] idecl] [pdecl ty]] u'] & [[[]]]).
      assert (H19 := t).
      assert (H17 := H0). eapply subject_reduction_eval in t. 2-3:eauto.
      eapply type_mkApps_inv in t as (? & ? & [] & ?) ; eauto.
      eapply typing_spine_inv in t0 as []; eauto.
      
      eapply IHeval1 in E as (? & ? & ?); eauto. clear IHeval1.
      eapply extract_Apps in H3 as (e' & l & ? & ? & ?).
      eapply (All2_nth_error_Some _ _ a1) in H0 as (? & ? & ?). 
      eapply IHeval2 in e1 as (? & ? & ?); eauto.
      simpl in l. destruct (Extract.is_type_or_proof _ _ (PCUICAst.tConstruct i k u)) eqn:Hc; inv l.
      destruct a2; inv H6; subst.
      * exfalso. assert (forall t, Extract.is_type_or_proof Σ [] (PCUICAst.tProj (i, pars, arg) discr) = Checked t -> Extract.is_type_or_proof Σ [] discr = Checked t).
        cbn. clear. intros ?. destruct type_of; try eauto.
        destruct reduce_to_ind eqn:E.  eauto. inversion 1.
        eapply H5 in Heq. clear H5. eapply eval_is_type_backwards in H.
        2: rewrite <- is_type_or_proof_mkApps; eauto. congruence.
      * exists x5. split. eauto. eapply eval_proj. eauto. rewrite <- nth_default_eq.
        unfold nth_default. rewrite e0. eauto.
      * econstructor; eauto.
      * econstructor; eauto.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor. 
      simpl. rewrite Heq. reflexivity.
    + destruct ?; try congruence.
      inv Ht'. eexists. split. 2:econstructor.
      simpl. now rewrite Heq, E.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      simpl. rewrite Heq. reflexivity.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      simpl. now rewrite Heq. 
    + congruence. 
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      simpl. rewrite Heq. reflexivity.
    + inv Ht'.  exists tBox. split. 2: repeat econstructor.
      simpl. rewrite Heq. reflexivity.
    + congruence.
  - eapply extract_Apps in Ht' as (e & ? & ? & []). subst.
    inv pre. edestruct (type_mkApps_inv _ _ _ _ _ extr_env_wf extr_typed0) as (? & ? & [] & ?) ; eauto. 

    eapply IHeval in e0 as (? & ? & ?); eauto.
    eapply extract_tInd in H1. subst.
    exists tBox. split. eapply is_type_extract. eapply is_type_App. eauto. eapply subject_reduction.
    eauto. 2:{ eapply PCUICReduction.red_mkApps. eapply wcbeval_red. eauto.
               eapply All2_impl. exact X. intros. eapply wcbeval_red. eauto. }
    eauto. eapply is_type_ind. eapply subject_reduction_eval; eauto.
    destruct e; subst; eauto; eapply eval_box_apps; eauto.
    econstructor; eauto.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      simpl. rewrite Heq. reflexivity.
    + inv Ht'. eexists. split.
      simpl. rewrite Heq. reflexivity. econstructor. eauto.
    + congruence.
  - assert (H10 := Ht'). eapply extract_Apps in Ht' as (e & ? & ? & []). subst.
    inv pre. edestruct (type_mkApps_inv _ _ _ _ _ extr_env_wf extr_typed0) as (? & ? & [] & ?) ; eauto. 

    eapply IHeval in e0 as (? & ? & ?); eauto.
    simpl in H1. destruct is_type_or_proof eqn:Heq. destruct a0.
    + inv H1. exists tBox.
      split. eapply is_type_extract. eapply is_type_App. eapply subject_reduction.
      eauto. 2:{ eapply PCUICReduction.red_mkApps. eapply wcbeval_red. eauto.
               eapply All2_impl. exact X. intros. eapply wcbeval_red. eauto. }

      eauto. eauto.
      destruct e; subst; eauto; eapply eval_box_apps; eauto.
    + inv H1. assert (t' = mkApps e x). destruct e; eauto. eapply eval_tBox_inv in H2. inv H2. subst. clear y.
      enough (exists x', Forall2 (eval Σ') x x' /\ Forall2 (fun a e => extract Σ [] a = Checked e) l' x') as (x' & H1 & H12).
      eexists (mkApps (tConstruct i k) x'). split.
      * eapply extract_Apps2. simpl. now rewrite Heq. eauto.
      * econstructor; eauto.
      * clear IHeval. clear H10. revert x a X HΣ' extr_env_axiom_free0 extr_typed0 extr_env_wf.
        clear - H0. intros.
        
        dependent induction H0 using All2_ind_rev.
        -- depelim a. exists []. repeat econstructor.
        -- specialize (All2_app_inv _ _ _ _ _ _  a) as ([] & ([->] & ?)).
           specialize (All2_app_inv _ _ _ _ _ _  X) as ([] & ([] & ?)).
           inv a1. inv H4. 
           inv a3. inv X1.
           eapply last_inv in e as [-> ->].

           rewrite mkApps_snoc in extr_typed0.
           edestruct (type_mkApps_inv _ _ _ [x] _ extr_env_wf extr_typed0) as (? & ? & [] & ?) ; eauto. 
           inv t0.
           
           eapply IHAll2 in a0 as (? & ? & ?).
           all:auto. 2:eauto.
           eapply r in H2 as (? & ? & ?).
           
           exists (x2 ++ [x3])%list. 
           2:econstructor; eauto. 3:eauto. split.
           ++ eapply Forall2_app; eauto.
           ++ eapply Forall2_app; eauto.
           ++ eauto.
    + congruence.
    + econstructor; eauto.
Admitted.
