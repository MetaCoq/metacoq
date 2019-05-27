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

Lemma is_constructor_extract Σ n L :
  PCUICTyping.is_constructor n L ->
  is_constructor n (map (extract Σ []) L).
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


Lemma prop_case_is_singleton  Σ ind npar p T i u args brs mdecl idecl :
  PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl ->
  PCUICAst.ind_npars mdecl = npar ->
  is_type_or_proof Σ [] (PCUICAst.tConstruct ind i u) = true ->
  Σ;;; [] |- PCUICAst.tCase (ind, npar) p (PCUICAst.mkApps (PCUICAst.tConstruct ind i u) args) brs : T -> #|brs| = 1 /\ i = 0 /\
                                                                                                              Forall (fun a => is_type_or_proof Σ [] a = true) (skipn (npar) args).
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

(* Lemma cumul_is_arity: *)
(*   forall (H : Fuel) (Σ : PCUICAst.global_context) (T' T'' : PCUICAst.term), *)
(*     Σ;;; [] |- T'' <= T' -> is_arity Σ [] H T'' = is_arity Σ [] H T'. *)
(* Proof. *)
(*   intros H Σ T' T''. *)
(* Admitted. *)

Lemma eval_is_type (Σ : PCUICAst.global_context) (t v : PCUICAst.term) (* T : *)
  (* wf Σ -> Σ ;;; [] |- t : T ->  *) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] t = Extract.is_type_or_proof Σ [] v.
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

(* Lemma eval_is_type_backwards `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) (* T : *) *)
(*   (* wf Σ -> Σ ;;; [] |- t : T -> *) : *)
(*   PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] v = Checked true -> Extract.is_type_or_proof Σ [] t = Checked true. *)
(* Proof. *)
(*   intros. *)
(*   (* destruct (type_of_sound _ X0) as (T' & [] & ?). *) *)
(*   (* eapply subject_reduction_eval in t0; eauto. *) *)
(*   (* destruct (type_of_sound _ t0) as (T'' & [] & ?). *) *)
(*   (* unfold is_type_or_proof in *. rewrite e, e0 in *. *) *)
(*   (* simpl in *. *) *)

(*   (* destruct (is_arity _ _ _ T') eqn:E1. reflexivity. *) *)
    
(* Admitted. *)
  
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
  forall (Σ : PCUICAst.global_context) (i : inductive) (u : universe_instance) (T : PCUICAst.term),
    Σ;;; [] |- tInd i u : T -> is_type_or_proof Σ [] (tInd i u).
Proof.
  
Admitted.

Lemma is_type_App  Σ a l T :
  Σ ;;; [] |- PCUICAst.mkApps a l : T -> 
  is_type_or_proof Σ [] a = is_type_or_proof Σ [] (PCUICAst.mkApps a l).
Proof.
Admitted.
  
Lemma is_type_or_proof_lambda  Σ Γ na t b :
  Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) =  
  Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b. 
Admitted.

(* Lemma is_type_or_proof_mkApps  Σ Γ a l : *)
(*   Extract.is_type_or_proof Σ Γ a = Checked true <-> *)
(*   Extract.is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = Checked true. *)
(* Admitted. *)

Lemma is_type_subst1  (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) :
  Extract.is_type_or_proof Σ ([],, PCUICAst.vass na t) b = 
  Extract.is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b).
Proof.
Admitted.

(** ** extract and mkApps *)

Lemma extract_Apps  Σ Γ a args :
  extract Σ Γ (PCUICAst.mkApps a args) = if is_type_or_proof Σ Γ a then tBox else mkApps (extract Σ Γ a) (map (extract Σ Γ) args).
Proof.
  
  
  (* revert a x. induction args using rev_ind; intros. *)
  (* - cbn in H0. repeat eexists; eauto. destruct x; eauto. *)
  (* - rewrite mkApps_snoc in H0. assert (H17 := H0). simpl in H0. *)
  (*   destruct ?. destruct a0. all:try congruence. *)
  (*   + inv H0. exists tBox. split. eapply is_type_extract. admit.  *)
  (*     eapply is_type_or_proof_mkApps with (l := [x]) in E.  *)
  (*     eapply is_type_extract in E. eapply IHargs in E as (? & ?  & ? & ? &?). *)
  (*     Lemma mkApps_tbox: *)
  (*       forall x0 (x1 : list E.term), E.tBox = mkApps x0 x1 -> x0 = tBox. *)
  (*     Proof. *)
  (*       intros. *)
  (*       induction x1 using rev_ind; rewrite ?emkApps_snoc in *. cbn in H. inv H. eauto. *)
  (*       inv H. *)
  (*     Qed. *)
  (*     destruct x0; try eapply mkApps_tbox in y; inv y. *)
  (*     destruct (extract Σ Γ x) eqn:EE. *)
  (*     * repeat eexists; eauto. eapply All2_app. eauto.  *)
  (*       repeat econstructor. eauto. *)
  (*     * admit. *)
  (*   + destruct ?. destruct ?. all:try congruence. inv H0. *)
  (*     eapply IHargs in E0 as (? & ? & ? & ? & ?). *)
  (*     exists x0. split. eauto. exists (x1 ++ [a1])%list. *)
  (*     split. eapply All2_app. eauto. repeat econstructor. eauto. *)
  (*     rewrite emkApps_snoc. destruct x0; subst; eauto. *)
  (*     admit.       *)
Admitted.

(* Lemma extract_Apps2  Σ Γ a args e l : *)
(*    = Checked e -> Forall2 (fun a e => extract Σ Γ a = Checked e) args l ->                                                                                  extract Σ Γ (PCUICAst.mkApps a args) = Checked (mkApps e l). *)
(* Proof. *)
(* Admitted. *)

Lemma extract_tInd Σ i u :
  extract Σ [] (tInd i u) = tBox.
Proof.
  cbn. destruct is_type_or_proof eqn:E1; try destruct a; reflexivity. 
Qed.

(** ** Concerning extraction of constants *)

Fixpoint extract_global_decls' univs Σ1 Σ : E.global_declarations :=
  match Σ, Σ1 with
  | [], [] => []
  | PCUICAst.ConstantDecl kn cb :: Σ0, _ :: Σ1 =>
      let cb' := extract_constant_body (Σ1, univs) cb in
      let Σ' := extract_global_decls' univs Σ1 Σ0 in (E.ConstantDecl kn cb' :: Σ')
  | PCUICAst.InductiveDecl kn mib :: Σ0, _ :: Σ1 =>
    let mib' := extract_mutual_inductive_body (Σ1, univs) mib in
    let Σ' := extract_global_decls' univs Σ1 Σ0 in (E.InductiveDecl kn mib' :: Σ')
  | _, _ => []
   end.

Lemma extract_global_decls_eq  u Σ :
  extract_global_decls u Σ = extract_global_decls' u Σ Σ.
Proof.
  induction Σ.
  - reflexivity.
  - simpl. destruct a; congruence.
Qed.

Require Import PCUIC.PCUICWeakeningEnv.
Lemma extract_constant:
  forall (Σ : PCUICAst.global_context) (c : ident) (decl : PCUICAst.constant_body) (body : PCUICAst.term)
    (u : universe_instance),
    wf Σ ->
    PCUICTyping.declared_constant Σ c decl ->
    PCUICAst.cst_body decl = Some body ->
    exists decl' : constant_body, 
        declared_constant (extract_global Σ) c decl' /\
        cst_body decl' = Some (extract Σ [] (PCUICUnivSubst.subst_instance_constr u body)).
Proof.
  intros.

  (* pose (P := fun  Σ (_ : PCUICAst.context) trm (tp : option PCUICAst.term) => match tp with Some tp => { '(t',tp') : _ & (extract Σ [] trm = Checked t') * (extract Σ [] tp = Checked tp')}%type | None => False end). *)
  (* assert (H' := H). *)
  (* eapply weaken_lookup_on_global_env with (P0 := P) in H; subst P; eauto. *)
  (* - unfold on_global_decl, on_constant_decl in H. rewrite H1 in H. *)
  (*   destruct H as [[] []]. *)
  (*   exists (Build_constant_body t0 (Some t)), t. simpl. repeat split. *)
  (*   unfold declared_constant. destruct Σ as [decls univ]. *)
  (*   unfold PCUICTyping.declared_constant in *. simpl in H'. *)
  (*   admit. admit. *)
  (* - unfold weaken_env_prop. intros. destruct T; try tauto. admit. *)
  (* - unfold on_global_env. destruct Σ. cbn. revert H0 X. clear. *)
  (*   (* revert t Σ'; induction g; simpl; intros. *) *)
  (*   (* + inv H0. econstructor. admit. *) *)
  (*   (* + destruct ? in H0; inv H0. econstructor. eapply IHg; auto. admit. admit. admit. *) *)
  (*   (*   destruct a; simpl. *) *)
  (*   (*   * unfold on_constant_decl. destruct ?. *) *)
      
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

Lemma extract_context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
     forall Γ' : PCUICAst.context, red_context Σ Γ Γ' -> forall a, extract Σ Γ a = extract Σ Γ' a).
Admitted.

(** ** Corrcectness of erasure *)
Hint Constructors PCUICWcbvEval.eval.

Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v H. revert T pre.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T pre.
  - (** beta case, done *) cbn.
    destruct Extract.is_type_or_proof eqn:Heq.
    + rewrite is_type_extract. econstructor. econstructor.
      erewrite <- eval_is_type. eauto. eauto.
    + inv pre. edestruct (type_mkApps_inv Σ [] f [a] T) as (? & U & [? ?] & ?); eauto. 
      inv t1. inv X2. pose proof (subject_reduction_eval _ [] _ _ _ extr_env_wf t0 H).
      eapply type_Lambda_inv in X2 as (? & ? & [? ?] & ?).

      cbn in IHeval1. 
      erewrite <- is_type_App with (l := [a]) in Heq; eauto.
      erewrite eval_is_type in Heq; try exact H.
      rewrite Heq in IHeval1.
      econstructor. eapply IHeval1. econstructor; eauto.
      eapply IHeval2. econstructor; eauto.

      assert (Σ ;;; [] |- a' : t). {
        eapply subject_reduction_eval; try eapply H0; eauto. 
        eapply cumul_trans in X0. 2:eauto. eapply cumul_Prod_inv in X0 as []. econstructor. eauto. eauto. eapply c1.
      }

      erewrite <- extract_subst1; eauto.
      eapply IHeval3. econstructor; eauto.

      eapply substitution0; eauto.
  - (** zeta case, done *)
    inv pre. eapply type_tLetIn_inv in extr_typed0 as (? & U & [[] ?] & ?); eauto. cbn.
    destruct Extract.is_type_or_proof eqn:Heq. 
    + rewrite is_type_extract. now econstructor.
      erewrite <- eval_is_type. eassumption.
      eauto.
    + econstructor.
      * eapply IHeval1. econstructor; eauto.
      * assert (extract Σ [PCUICAst.vdef na b0 t] b1 = extract Σ [PCUICAst.vdef na b0' t] b1) as ->. {
          eapply extract_context_conversion. 3: eassumption. all:eauto.
          econstructor. econstructor. cbn. eauto. econstructor 3. econstructor.
          econstructor. eapply subject_reduction_eval; eauto.
          eapply wcbeval_red. eauto.
        }
        assert (Σ ;;; [] |- b0' : t). {
          eapply subject_reduction_eval; eauto.
        }
        
        erewrite <- extract_subst1_vdef; eauto.
        eapply IHeval2. econstructor; eauto.
        eapply substitution_let; eauto.
        
        eapply (context_conversion _ _ _ _ _ _ t2).
        
        Hint Constructors context_relation red_decls.
        Hint Resolve wcbeval_red.
        econstructor; eauto.

        eapply (context_conversion _ _ _ _ _ _ t2).
        econstructor; eauto.
  - (** rel_def, trivial *) cbn in isdecl. inv isdecl.    
  - (** rel_undef, trivial *) cbn in isdecl. inv isdecl.    
  - (** iota case (tCase) *)
    cbn. destruct Extract.is_type_or_proof eqn:Heq.
    + rewrite is_type_extract. econstructor; eauto.
      erewrite <- eval_is_type. eassumption.
      econstructor; eauto.
    + inv pre. assert (HT := extr_typed0). eapply type_Case_inv in extr_typed0 as [ [[[[[[[[]]]]]]]] [[]]  ].
      destruct p0 as [[[[[]]]]]. 

      assert (t17 := t0).
      eapply subject_reduction_eval in t0; eauto.
      eapply type_mkApps_inv in t0 as (? & ? & [] & ?); eauto.
           
      destruct is_box eqn:Ea.
      * destruct extract; inversion Ea; clear Ea. 

        destruct brs eqn:Hbrs.
        -- edestruct (no_empty_case_in_empty_context); eauto.
        -- destruct p1.
           admit.
           (*  this is the case where the discriminee extract to a box *)
      * rewrite extract_Apps in IHeval1. 
        cbn in IHeval1. destruct is_type_or_proof eqn:He.
        -- eapply eval_iota_sing. eapply IHeval1. econstructor; eauto.
           (* if the discriminee reduces to a constructor of a proof, there was only one branch, TODO *) admit.
           admit.
        (* -- econstructor. eapply IHeval1. econstructor; eauto. *)
        -- cbn in IHeval2.
           unfold PCUICTyping.iota_red in *. unfold iota_red.
           rewrite extract_Apps in IHeval2.
           destruct is_type_or_proof eqn: Hee in IHeval2.
           ++ econstructor. eapply IHeval1. econstructor; eauto.
              unfold iota_red.
              assert (extract Σ [] res = tBox) as ->.
              eapply eval_tBox_inv. eapply IHeval2.
              econstructor; eauto. admit.

              admit.
           ++ 
              
              
              
           destruct (nth_error brs c) eqn:Hnth.
           2:{  (* Branches can't be too few, ensured by typing *)
             admit. }
           
           Lemma nth_map {A B} (f : A -> B) n l d d2 :
             n < #|l| -> nth n (map f l) d2 = f (nth n l d).
           Proof.
             induction n in l |- *; destruct l; simpl; auto.
           Admitted.

           econstructor. eapply IHeval1. econstructor; eauto.


           unfold iota_red.
           rewrite <- nth_default_eq in *. unfold nth_default in *.
           rewrite Hnth in *.
           epose proof (map_nth_error _ _ _ Hnth).
           rewrite H1 in *. cbn.
           
           rewrite <- map_skipn. eapply IHeval2.
           econstructor; eauto.
           eapply type_mkApps.

           (* branches of case are typed *) admit.
           (* after taking away things in a spine, it's still typed *)  admit.
  - (** fix case *) rewrite extract_Apps.
    cbn. destruct is_type_or_proof eqn:Heq.
    + inv pre. rewrite is_type_extract.
      econstructor. eauto.
      erewrite <- eval_is_type.
      erewrite is_type_App in Heq.
      eassumption. eauto.
      econstructor; eauto.
    + inv pre.
      eapply type_mkApps_inv in extr_typed0 as (? & ? & [] & ?); eauto.

      unfold unfold_fix, PCUICTyping.unfold_fix in *.
      destruct nth_error eqn:En in H; try now inv H.
      inv H. unfold extract_mfix.
      
      econstructor.
      * unfold unfold_fix. erewrite map_nth_error.  reflexivity.
        eauto.
      * Lemma Forall2_map {A B C D} (R : C -> D -> Prop) (f : A -> C) (g : B -> D) l l' :
          Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
        Proof. induction 1; simpl; constructor; try congruence. Qed.
        eapply Forall2_map.
        eapply All2_Forall.
        Lemma All2_impl {A B} {P Q : A -> B -> Type} {l l'} :
          All2 P l l' ->
          (forall x y, In x l -> In y l' -> P x y -> Q x y) ->
          All2 Q l l'.
        Proof.
          revert l'. induction l; intros; inversion X.
          - econstructor.
          - subst. econstructor.  eapply X0. firstorder. firstorder. eauto.
            eapply IHl. eauto. intros.
            eapply X0. now right. now right. eauto.
        Qed.
        
        eapply All2_impl. eassumption.
        intros; cbn in *.
        eapply H4. econstructor ; eauto. (* follows with typing_spine_inv *) admit.
      * unfold PCUICTyping.is_constructor, is_constructor_or_box in *.
        destruct nth_error eqn:He in H1; try now inv H1.
        erewrite map_nth_error. 2:eassumption.
        unfold isConstruct_app in H1.
        destruct decompose_app eqn:Ha in H1.
        cbn in H1. destruct t2; try now inv H1.
        eapply PCUICConfluence.decompose_app_inv in Ha.
        subst.
        rewrite extract_Apps.
        destruct (is_type_or_proof _ _ (PCUICAst.tConstruct _ _ _)) eqn:Hp.
        -- eauto.
        -- cbn. rewrite Hp.
           Lemma decompose_app_mkApps f l :
             isApp f = false -> EAstUtils.decompose_app (mkApps f l) = (f, l).
           Proof. Admitted.
           rewrite decompose_app_mkApps. destruct ?; eauto.
           cbn. reflexivity.
      * cbn.
        eapply type_tFix_inv in t as (? & ? & ? & [] & ?).
        rewrite extract_Apps in IHeval.
        destruct is_type_or_proof eqn:He.
        -- admit.
        -- erewrite (extract_subst Σ [] (fix_decls mfix) []) in IHeval.
           cbn in IHeval.
           

           enough ((map (extract Σ []) (PCUICTyping.fix_subst mfix)) = fix_subst
              (map
                 (fun d0 : BasicAst.def PCUICAst.term =>
                  {|
                  E.dname := BasicAst.dname d0;
                  E.dbody := extract Σ (fix_decls mfix ++ [])%list (BasicAst.dbody d0);
                  E.rarg := BasicAst.rarg d0 |}) mfix)).
           rewrite <- H. eapply IHeval.
           econstructor. eapply type_mkApps.
           all:cbn; eauto.
           ++ admit (* typing of fix_subst *).
           ++ admit (* typing_spine and eval *).
           ++ rewrite <- efix_subst'_subst.
              rewrite map_length.
              rewrite <- fix_subst'_subst.
              generalize (#|mfix|). intros n.
              induction n; cbn.
              ** reflexivity.
              ** rewrite IHn.

              (*  Substituting with the two substitutions is the same. The points where they differ are boxes in the term to be substituted in anyways! *) admit. 
           ++ eapply subslet_fix_subst.
           ++ admit.
        -- eauto.
  (*   destruct extract_mfix eqn:E. inv He. 2:congruence. subst. *)
    (*   enough (exists l', Forall2 (eval Σ') l l' /\ Forall2 (fun a e => extract Σ [] a = Checked e) args' l' /\ (PCUICTyping.is_constructor narg args' -> is_constructor narg l')) as (l' & ? & ? & ?). *)

    (*   assert (E' := E). *)
    (*   pose proof (monad_map_All2 _ _ (fun d : BasicAst.def PCUICAst.term => *)
    (*      dbody' <- extract Σ (fix_decls mfix ++ [])%list (BasicAst.dbody d);; *)
    (*             ret {| E.dname := BasicAst.dname d; E.dbody := dbody'; E.rarg := BasicAst.rarg d |})). *)
    (*   eapply H6 in E. clear H6. *)

    (*   assert (H'' := H). *)
    (*   unfold PCUICTyping.unfold_fix in H. destruct ? in H; try congruence. *)
    (*   eapply All2_nth_error_Some in E as (? & ? & ?); eauto. *)
    (*   inv e0. destruct ? in H7; inv H7. inv H. *)
    (*   assert (exists s', monad_map (extract Σ []) (PCUICTyping.fix_subst mfix) = Checked s') as [s' ?] by admit. (* this goes away without fuel *) *)

    (*   edestruct IHeval as (? & ? & ?). *)
      
    (*   2:{ eapply extract_Apps2; eauto. eapply (extract_subst Σ [] _ []). *)
    (*       - eauto. *)
    (*       - eapply subslet_fix_subst. *)
    (*       - rewrite app_context_nil_l. rewrite app_nil_r in E. eauto. *)
    (*       - admit. *)
    (*       - eauto. *)
    (*       - eapply monad_map_Forall2. eauto. } *)

    (*   econstructor. eapply subject_reduction. *)
    (*   eauto. exact extr_typed0. all:eauto. *)
    (*   etransitivity. eapply PCUICReduction.red_mkApps. *)
    (*   eapply refl_red. eapply All2_impl. exact X. intros. now eapply wcbeval_red. *)

    (*   eapply PCUICReduction.red_step. econstructor; eauto. eapply refl_red. *)

    (*   exists x. split. eauto. econstructor.  *)

    (*   unfold unfold_fix. rewrite e. simpl. f_equal. eauto. eauto. *)

    (*   assert (subst0 (fix_subst a) a0 = subst0 s' a0) by admit. (* substituting with extracted fix_subst is the same as substituing with fix_subst on results of extraction (like a0), since variables where they differ (extracted fix_subst is box where fix_subst is fix ... := box) are replaced by box in a0 already *) *)
    (*   rewrite H8. eauto. *)

    (*   1:{ clear H1. revert H0  X Hl narg  H extr_typed0 extr_env_axiom_free0 extr_env_wf HΣ'. clear. *)
    (*       intros H0. intros. revert l Hl T extr_typed0. dependent induction H0 using All2_ind_rev; intros. *)
    (*       - inv Hl. exists []. repeat split; eauto. unfold PCUICTyping.is_constructor, is_constructor. *)
    (*         destruct narg; cbn; eauto. *)
    (*       - eapply All2_app_inv in X as ( []  & [[]]). inv a0. inv X0. *)
    (*         eapply All2_app_inv in Hl as ( []  & [[]]). inv a1. inv H5. *)
    (*         eapply last_inv in e as (-> & ->). *)
    (*         eapply type_mkApps_inv in extr_typed0 as (? & ? & [] & ?) ; eauto. *)
    (*         eapply typing_spine_inv_app in t0 as [[] []]. *)
    (*         eapply IHAll2 in a as (? & ? & ? & ?).   *)
            
    (*         eapply r in H3 as (? & ? & ?); eauto.  *)
    (*         eexists (x2 ++ [x3])%list. repeat split. *)
    (*         eapply Forall2_app; eauto. *)
    (*         eapply Forall2_app; eauto. *)

    (*         Hint Resolve Forall2_app. *)
    (*         intros. *)
    (*         eapply is_constructor_extract. eauto. eauto. *)
              
    (*         econstructor; eauto. all:eauto. *)
    (*         eapply PCUICGeneration.type_mkApps; eauto. } *)
    (* + congruence. *)
  - (** delta case, done up to lemma*) cbn. destruct Extract.is_type_or_proof eqn:Heq. 
    + erewrite is_type_extract. econstructor; eauto.
      erewrite <- eval_is_type. eassumption. eauto.
    + inv pre.
      destruct (extract_constant _ c decl body u extr_env_wf H H0) as (decl' & ? & ?); eauto.
      econstructor.
      * eauto.
      * eauto.
      * eapply IHeval. econstructor; eauto.
        eapply subject_reduction. eauto. exact extr_typed0.
        eapply PCUICReduction.red1_red. econstructor; eauto.
  - (** proj case, needs check in typing *) cbn. destruct Extract.is_type_or_proof eqn:Heq. 
    + rewrite is_type_extract. econstructor; eauto.
      erewrite <- eval_is_type. eassumption. eauto.
    + inv pre.
      eapply type_proj_inv in extr_typed0 as ( [[[[args' mdecl] idecl] [pdecl ty]] u'] & [[[]]]).
      assert (H19 := t).
      assert (H17 := H0). eapply subject_reduction_eval in t. 2-3:eauto.
      eapply type_mkApps_inv in t as (? & ? & [] & ?) ; eauto.
      eapply typing_spine_inv in t0 as []; eauto.

      rewrite extract_Apps in IHeval1 (* ok because if projection is a non-proof, constructor was no proof *).
      cbn in IHeval1. destruct ? in IHeval1.
      * admit. (* same *)
      * econstructor. eapply IHeval1. econstructor; eauto.
        eapply map_nth_error in H17.
        rewrite <- nth_default_eq. unfold nth_default.
        rewrite H17. eapply IHeval2. econstructor; eauto.
  - (** abs case, trivial *) cbn. destruct Extract.is_type_or_proof eqn:Heq. 
    + econstructor; eauto. 
    + econstructor.
  - (** prod case, trivial *) cbn. destruct Extract.is_type_or_proof eqn:Heq. 
    + econstructor; eauto. 
    + econstructor; eauto.
  - (** app_ind nil case, trivial *) cbn. destruct Extract.is_type_or_proof eqn:Heq; econstructor; eauto.
  - (* app_ind non-nil case *) inv pre. edestruct (type_mkApps_inv _ _ _ _ _ extr_env_wf extr_typed0) as (? & ? & [] & ?) ; eauto. 
    rewrite !is_type_extract.
    + econstructor; eauto.
    + erewrite <- is_type_App. eapply is_type_ind. eapply subject_reduction_eval; eauto.
      eapply subject_reduction_eval. eauto. 2:eauto.
      eapply type_mkApps; eauto.
    + admit. (* if you reduce to tInd, you are a type *)
  - (** app_constr nil case *)cbn. destruct Extract.is_type_or_proof eqn:Heq. 
    + econstructor; eauto. 
    + econstructor; eauto.
  - (** app_constr nonnil case *) inv pre. edestruct (type_mkApps_inv _ _ _ _ _ extr_env_wf extr_typed0) as (? & ? & [] & ?) ; eauto.

    rewrite !extract_Apps.
    cbn.
    destruct is_type_or_proof eqn:Heq.
    + erewrite <- eval_is_type, Heq.
      2: eauto. econstructor; eauto.
    + cbn in *. destruct (is_type_or_proof Σ [] (PCUICAst.tConstruct _ _ _)).
      * eapply eval_box_apps. eapply IHeval. econstructor; eauto.
      * econstructor. eapply IHeval. econstructor; eauto.
        eapply Forall2_map. eapply All2_Forall.
        eapply All2_impl. eassumption.
        intros. cbn in *. eapply H3.
        (* follows with typing_spine_inv *) admit.
Admitted.
