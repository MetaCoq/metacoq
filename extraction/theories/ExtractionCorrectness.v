(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR.
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.


Inductive extr_pre (Σ : PA.global_context) t T :=
  { extr_typed : Σ ;;; [] |- t : T;
    extr_env_axiom_free : axiom_free (fst Σ) }.

(* Lemma is_type_or_proof `{F:Fuel} : *)
(*   env_prop (fun Σ Γ t T => Γ = [] -> { U & (type_of Σ [] t = Checked U) * cumul Σ [] U T }%type). *)
(* Proof. *)
(*   eapply typing_ind_env; simpl; intros **; try rewrite HeqΓ in *. rewrite H0 in *. *)

(*   + rewrite H. eexists. split; eauto. *)
(*   + eexists; split; eauto. admit. *)

(*   + admit. *)
(*  (* + destruct IHX1 as [T [HT HTs]]. *) *)
(*  (*    destruct IHX2 as [U [HU HUs]]. *) *)
(*  (*    unfold type_of_as_sort. *) *)
(*  (*    rewrite HT. simpl. *) *)
(*  (*    destruct reduce_to_sort eqn:Heq'. *) *)
(*  (*    rewrite HU. *) *)
(*  (*    destruct (reduce_to_sort _ _ U) eqn:Heq''. *) *)
(*  (*    eexists; split; eauto. *) *)
(*  (*    admit. *) *)
(*  (*    admit. *) *)
(*  (*    admit. *) *)

(* Admitted. *)

Ltac inv H := inversion H; subst; clear H.

Tactic Notation "destruct" "?" :=
  let E := fresh "E" in
  match goal with
    [ |- context[match ?X with _ => _ end]] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E
  end.

Lemma eval_is_type `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] t = Checked true -> Extract.is_type_or_proof Σ [] v = Checked true.
Proof.
  unfold Extract.is_type_or_proof.
Admitted.


Lemma eval_is_type_backwards `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] v = Checked true -> Extract.is_type_or_proof Σ [] t = Checked true.
Proof.
  unfold Extract.is_type_or_proof.
Admitted.


Lemma is_type_extract `{Fuel} (Σ : PCUICAst.global_context) Γ (t : PCUICAst.term) :
  Extract.is_type_or_proof Σ Γ t = Checked true -> extract Σ Γ t = Checked E.tBox.
Proof.
  intros H1.
  destruct t; simpl; try rewrite H1; try reflexivity.
  all: inversion H1.  
Qed.

(* Lemma is_proof_app `{Fuel} Σ f a : *)
(*   Extract.is_type_or_proof Σ [] f = Extract.is_type_or_proof Σ [] (PCUICAst.tApp f a). *)
(* Proof. *)
(*   unfold Extract.is_type_or_proof. cbn [type_of]. destruct type_of as [T|]; try reflexivity. *)
(*   unfold bind at 1 4. cbn -[bind]. *)
(*   unfold is_arity at 1.  *)
  
(* Admitted. *)


Theorem subject_reduction_eval : forall (Σ : PCUICAst.global_context) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> PCUICWcbvEval.eval Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred % wcbeval_red. eapply subject_reduction; eauto.
Qed.

Lemma extract_subst1 
  (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) (fuel : Fuel) (a0 : E.term) :
    extract Σ [PCUICAst.vass na t] b = Checked a0 ->
    forall vea : E.term,
      extract Σ [] a' = Checked vea -> extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked (a0 {0 := vea}).
Proof.
  intros.
Admitted.

Lemma extract_subst1_vdef
      (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) (fuel : Fuel) (a0 : E.term) a'' :
  PCUICWcbvEval.eval Σ [] a'' a' ->
    extract Σ [PCUICAst.vdef na a'' t] b = Checked a0 ->
    forall vea : E.term,
      extract Σ [] a' = Checked vea -> extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked (a0 {0 := vea}).
Proof.
  intros.
Admitted.


Lemma is_type_or_proof_lambda `{Fuel} Σ Γ na t b :
  Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) = Checked true ->
  Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b = Checked true.
Admitted.


Lemma is_type_or_proof_mkApps `{Fuel} Σ Γ a l :
  Extract.is_type_or_proof Σ Γ a = Checked true ->
  Extract.is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = Checked true.
Admitted.

Lemma is_type_subst `{Fuel} (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) :
  Extract.is_type_or_proof Σ ([],, PCUICAst.vass na t) b = Checked true ->
  Extract.is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked true.
Proof.
Admitted.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.


Lemma extract_Apps `{Fuel} Σ Γ a args x :
  extract Σ Γ (PCUICAst.mkApps a args) = Checked x -> {e : _ & (extract Σ Γ a = Checked e) *
                                                              { l : list E.term & (All2 (fun a e => extract Σ Γ a = Checked e) args l) *
                                                                                  (x = mkApps e l)
                                                                                  (* match e with tBox => x = tBox | _ => (x = mkApps e l) end *) }}%type.
Proof.
Admitted.

Lemma is_type_App `{Fuel} Σ a l T :
  Σ ;;; [] |- PCUICAst.mkApps a l : T -> 
  is_type_or_proof Σ [] a = Checked true ->
  is_type_or_proof Σ [] (PCUICAst.mkApps a l) = Checked true.
Proof.
Admitted.
  
Lemma typing_spine_inv:
  forall (Σ : PCUICAst.global_context) (i : inductive) (pars arg : nat) (args : list PCUICAst.term) 
    (a T : PCUICAst.term) (args' : list PCUICAst.term) (u' : universe_instance)
    (H17 : nth_error args (pars + arg) = Some a) (x2 x3 : PCUICAst.term),
    PCUICGeneration.typing_spine Σ [] x2 args x3 ->
    Σ;;; [] |- x3 <= PCUICAst.mkApps (tInd (fst (fst (i, pars, arg))) u') args' -> {T & Σ;;; [] |- a : T}.
Proof.
  intros Σ i pars arg args a T args' u' H17 x2 x3 t0 c0.
Admitted.

Lemma extract_tInd `{Fuel} Σ i u t :
  extract Σ [] (tInd i u) = Checked t -> t = tBox.
Proof.
  intros ?. simpl in *. destruct is_type_or_proof eqn:E1; try destruct a; now inv H0.
Qed.

Lemma eval_box_apps:
  forall (Σ' : list E.global_decl) (e : E.term) (x : list E.term), eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2.
Admitted.

Lemma All2_ind_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Prop),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Admitted.

Lemma All2_app : forall (A B : Type) (R : A -> B -> Type),
    forall l1 l2 l1' l2', All2 R l1 l1' -> All2 R l2 l2' -> All2 R (l1 ++ l2) (l1' ++ l2').
Proof.
Admitted.

Lemma All2_app_inv : forall (A B : Type) (R : A -> B -> Type),
    forall l l1 l2, All2 R (l1 ++ l2) l -> { '(l1',l2') : _ & (l = l1' ++ l2')%list * (All2 R l1 l1') * (All2 R l2 l2')}%type.
Proof.
  intros. revert l2 l X. induction l1; intros; cbn in *.
  - exists ([], l). eauto.
  - inversion X. subst.
    eapply IHl1 in X1 as ( [] & ? & ?). destruct p.  subst.
    eexists (y :: l, l0). repeat split; eauto.
Qed.

Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v H. revert T pre.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T pre fuel Σ' t' Ht' HΣ'.

  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq.
    destruct a0.
    + inv Ht'.
      exists tBox. split. 2:repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto. econstructor;eauto.
    + destruct (extract Σ [] f) as [ ef | ] eqn:Ef ; try congruence.
      destruct (extract Σ [] a) as [ ea | ] eqn:Ea; try congruence.
      inv Ht'. 
      inv pre. edestruct (type_mkApps_inv Σ [] f [a] T) as (? & U & [? ?] & ?); eauto. 
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
        -- eapply extract_subst1. eapply is_type_extract. eauto. eauto.
        -- eauto.
        -- exists tBox. cbn in H6. split. 2: eapply eval_box; eauto.
           eapply is_type_extract. eapply eval_is_type. eauto.
           eapply is_type_subst. eauto.
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
      * econstructor; eauto.
      * econstructor; eauto.
    + congruence.
  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq. destruct a; try congruence.
    + inv Ht'.  exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto.
      econstructor; eauto.
    + destruct (extract _ _ b0) as [ eb0 | ] eqn:Eb0; try congruence.
      destruct (extract _ _ b1) as [ eb1 | ] eqn:Eb1; try congruence.
      inv Ht'. inv pre. eapply type_tLetIn_inv in extr_typed0 as (? & U & [[] ?] & ?); eauto.

      eapply IHeval1 in Eb0 as (veb0 & ? & ?). 3:eauto.
      eapply extract_subst1_vdef in Eb1. 2:eauto. 2:eauto.
      eapply IHeval2 in Eb1 as (veb1 & ? & ?). 3:eauto.
      -- exists veb1. split. eauto. econstructor; eauto.
      -- econstructor; eauto. eapply substitution_let; eauto.
         eapply context_conversion. 3: eassumption. all:eauto.
         econstructor. econstructor. econstructor 3. eapply subject_reduction_eval; eauto.
         admit. (* context subject reduction needed *)        
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
      destruct is_box eqn:Ea.
      * destruct a; inversion Ea; clear Ea.
        admit.
             
      * destruct monad_map eqn:Em; try congruence.
        inv Ht'.
        econstructor. econstructor. 
        admit.
        admit. (* tCase *)
    + congruence.
  - admit. (* tFix *)
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eapply Heq.
      econstructor; eauto.
    + inv Ht'. inv pre. edestruct IHeval as (? & ? & ?).
      * econstructor; eauto. admit.
      * shelve.
      * eauto.
      * exists x. split. eauto. econstructor. 3:eauto. admit. admit. (* tConst *)
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
      eapply IHeval2 in e2 as (? & ? & ?); eauto.
      simpl in l. destruct (Extract.is_type_or_proof _ _ (PCUICAst.tConstruct i k u)) eqn:Hc; inv l.
      destruct a2; inv H6; subst.
      * assert (forall t, Extract.is_type_or_proof Σ [] (PCUICAst.tProj (i, pars, arg) discr) = Checked t -> Extract.is_type_or_proof Σ [] discr = Checked t).
        cbn. clear. intros ?. destruct type_of; try eauto.
        destruct reduce_to_ind eqn:E.  eauto. inversion 1.
        eapply H5 in Heq. clear H5. eapply eval_is_type_backwards in H.
        2: eapply is_type_or_proof_mkApps; eauto. congruence.
      * exists x5. split. eauto. eapply eval_proj. eauto. rewrite <- nth_default_eq.
        unfold nth_default. rewrite e1. eauto.
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
    eauto. (* is_proof of tInd *) admit.
    eapply eval_box_apps. eauto. econstructor; eauto.
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

      eauto. eauto. eapply eval_box_apps. eauto.
    + inv H1. enough (exists x', Forall2 (eval Σ') x x') as [x']. eexists (mkApps (tConstruct i k) x'). split. admit.
      econstructor; eauto. clear IHeval. clear H10. revert x a X HΣ' extr_env_axiom_free0 extr_typed0 extr_env_wf.
      clear - H0. intros.
        
      dependent induction H0 using All2_ind_rev.
      * depelim a. exists []. econstructor.
      * specialize (All2_app_inv _ _ _ _ _ _  a) as ([] & ([->] & ?)).
        specialize (All2_app_inv _ _ _ _ _ _  X) as ([] & ([] & ?)).
        inv a1. inv H4. 
        Lemma last_inv A (l1 l2 : list A) x y :
          (l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y)%list.
        Proof.
        Admitted.
        inv a3. inv X1.
        eapply last_inv in e as [-> ->].
        eapply IHAll2 in a0 as [].
        all:auto. 2:eauto.
        eapply r in H2 as (? & ? & ?).
        
        exists (x0 ++ [x1])%list. 
        2:econstructor; eauto. 3:eauto. eapply Forall2_app; eauto.
        admit. admit.
    + congruence.
    + econstructor; eauto.
Admitted.
