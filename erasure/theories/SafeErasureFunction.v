
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICTyping PCUICMetaTheory PCUICWcbvEval PCUICLiftSubst PCUICInversion
     PCUICConfluence PCUICCumulativity PCUICSR PCUICNormal PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker PCUICSafeRetyping.
From MetaCoq.Erasure Require EAst ELiftSubst ETyping EWcbvEval Extract ErasureCorrectness.
From Equations Require Import Equations.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.
Local Set Keyed Unification.

Require Import EArities Extract Prelim.
Section fix_sigma.
Local Existing Instance extraction_checker_flags.
Variable Σ : global_env_ext.
Variable HΣ : ∥wf Σ∥.

Definition term_rel : Relation_Definitions.relation (∑ Γ t, wellformed Σ Γ t) :=
  fun '(Γ2; B; H) '(Γ1; t1; H2) =>
    ∥∑ na A, red (fst Σ) Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.

Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

Lemma wf_cod : WellFounded cod.
Proof.
  clear HΣ.
  sq. intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
Qed.

Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
Proof.
  clear HΣ.
  eapply Subterm.WellFounded_trans_clos. exact wf_cod.
Qed.

Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
Proof.
  induction 1. intros. eapply H0; eauto.
Qed.

Ltac sq' := try (destruct HΣ; clear HΣ);
  repeat match goal with
         | H : ∥ _ ∥ |- _ => destruct H; try clear H
         end; try eapply sq.

Instance wf_reduction : WellFounded term_rel.
Proof.
  intros (Γ & s & H). sq'.
  induction (normalisation' Σ Γ s X H) as [s _ IH].
  induction (wf_cod' s) as [s _ IH_sub] in Γ, H, IH |- *.
  econstructor.
  intros (Γ' & B & ?) [(na & A & ? & ?)]. subst.
    inversion r.
    + subst. eapply IH_sub. econstructor. cbn. reflexivity.
      intros. eapply IH.
      inversion H0.
      * subst. econstructor. eapply prod_red_r. eassumption.
      * subst. eapply cored_red in H2 as [].
        eapply cored_red_trans. 2: eapply prod_red_r. 2:eassumption.
        eapply PCUICReduction.red_prod_r. eauto.
      * repeat econstructor.
    + subst. eapply IH.
      * eapply red_neq_cored. exact r. intros ?. subst.
        eapply cored_red_trans in X0; eauto.
        eapply Acc_no_loop in X0. eauto.
        eapply @normalisation'; eauto.
      * repeat econstructor.
Grab Existential Variables.
- eapply red_wellformed; sq. 3:eauto. all:eauto.
- destruct H as [[] |[]].
  -- eapply inversion_Prod in X0 as (? & ? & ? & ? & ?) ; auto.
     eapply cored_red in H0 as [].
     econstructor. econstructor. econstructor. eauto. eapply subject_reduction; eauto.
  -- eapply cored_red in H0 as [].
     eapply isWfArity_prod_inv in X0 as [_ ?].
     econstructor 2. sq.
     eapply isWfArity_red in i; eauto.
     destruct i as (? & ? & ? & ?).
     exists (x ++ [vass na A])%list, x0. cbn; split.
     2:{ unfold snoc, app_context in *. rewrite <- app_assoc. eassumption. }
     change ([] ,, vass na A) with ([vass na A] ,,, []).
     rewrite destArity_app_aux. rewrite e. cbn. reflexivity.
Qed.

Ltac sq := try (destruct HΣ as [wfΣ]; clear HΣ);
  repeat match goal with
         | H : ∥ _ ∥ |- _ => destruct H
         end; try eapply sq.

Equations is_arity Γ (HΓ : ∥wf_local Σ Γ∥) T (HT : wellformed Σ Γ T) :
  typing_result ({Is_conv_to_Arity Σ Γ T} + {~ Is_conv_to_Arity Σ Γ T})
  by wf ((Γ;T;HT) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
  {
    is_arity Γ HΓ T HT with (@reduce_to_sort _ Σ HΣ Γ T HT) => {
    | Checked H => ret (left _) ;
    | TypeError _ with inspect (@reduce_to_prod _ Σ HΣ Γ T _) => {
      | exist (Checked (na; A; B; H)) He =>
        match is_arity (Γ,, vass na A) _ B _ with
        | Checked (left  H) => ret (left _)
        | Checked (right H) => ret (right _)
        | TypeError t => TypeError t
        end;
      | exist (TypeError (NotAProduct _ _)) He => ret (right _);
      | exist (TypeError t) He => TypeError t }
    }
  }.
Next Obligation.
  sq. econstructor. split. sq. eassumption. econstructor.
Qed.
Next Obligation.
  clear He.
  destruct HT as [ [] | [] ]; sq.
  - eapply subject_reduction in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    econstructor. eauto. cbn. eauto. auto.
  - econstructor. eauto.
    eapply isWfArity_red in X; eauto.
    cbn. eapply isWfArity_prod_inv; eauto.
Qed.
Next Obligation.
  clear He.
  sq. destruct HT as [ [] | [] ].
  - eapply subject_reduction in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    do 2 econstructor. eauto. auto.
  - econstructor 2. sq.
    eapply isWfArity_red in X; eauto.
    eapply isWfArity_prod_inv; eauto.
Qed.
Next Obligation.
  sq. repeat eexists. eassumption.
Qed.
Next Obligation.
  destruct H as (? & ? & ?). eexists (tProd _ _ _). split; sq.
  etransitivity. eassumption. eapply PCUICReduction.red_prod. econstructor.
  eassumption. now cbn.
Qed.
Next Obligation.
  clear He.
  destruct HΣ as [wΣ].
  destruct H1 as (? & ? & ?). sq.
  destruct H.
  edestruct (red_confluence wfΣ X0 X) as (? & ? & ?); eauto.
  eapply invert_red_prod in r as (? & ? & [] & ?); eauto. subst.

  eapply invert_cumul_arity_l in H2. 2:eauto. 3: eapply PCUICCumulativity.red_cumul. 3:eauto. 2:eauto.
  destruct H2 as (? & ? & ?). sq.

  eapply invert_red_prod in X2 as (? & ? & [] & ?); eauto. subst. cbn in *.
  exists x4; split; eauto.

  destruct HT as [ [] | [] ].
  ++ sq. pose proof (X2). pose proof X2.

     eapply subject_reduction in X4. 2:eauto. 2:{ etransitivity. exact X. exact r0. }
     eapply inversion_Prod in X4 as (? & ? & ? & ? & ?) ; auto.

     eapply subject_reduction in X3. 2:eauto. 2:{ exact X0. }
     eapply inversion_Prod in X3 as (? & ? & ? & ? & ?) ; auto.

     etransitivity. eassumption.

     eapply context_conversion_red; eauto. econstructor.

     eapply conv_context_refl; eauto. econstructor.

     eapply PCUICConversion.conv_sym, red_conv; eauto.
  ++ sq. etransitivity. eassumption.

     eapply context_conversion_red; eauto. econstructor.

     eapply conv_context_refl; eauto.

     econstructor.

     eapply PCUICConversion.conv_sym, red_conv; eauto.
Qed.

Next Obligation.
Admitted. (* reduce to prod, if it returns a TypeError (NotAProduct _) just means it is not an arity *)

End fix_sigma.

Local Existing Instance extraction_checker_flags.
Definition wf_ext_wf Σ : wf_ext Σ -> wf Σ := fst.
Hint Resolve wf_ext_wf.

Program Definition is_erasable (Sigma : PCUICAst.global_env_ext) (HΣ : ∥wf_ext Sigma∥) (Gamma : context) (t : PCUICAst.term) (Ht : welltyped Sigma Gamma t) :
  typing_result ({∥isErasable Sigma Gamma t∥} +{∥(isErasable Sigma Gamma t -> False)∥}) :=
  mlet (T; _) <- @type_of extraction_checker_flags Sigma _ _ Gamma t Ht ;;
  mlet b <- is_arity Sigma _ Gamma _ T _ ;;
  if b : {_} + {_} then
    ret (left _)
  else mlet (K; _) <- @type_of extraction_checker_flags Sigma _ _ Gamma T _ ;;
       mlet (u;_) <- @reduce_to_sort _ Sigma _ Gamma K _ ;;
      match is_prop_sort u with true => ret (left _) | false => ret (right _) end
.
Next Obligation. sq; eauto. Qed.
Next Obligation.
  sq. red in X. red in X. apply X.
Qed.
Next Obligation.
  sq. apply X1.
Qed.
Next Obligation.
  sq. eauto using typing_wf_local.
Qed.
Next Obligation.
  sq. eapply validity in X. destruct X. destruct i. right. sq. apply i. left.  destruct i. econstructor. apply t0.
  apply X1. eauto using typing_wf_local.
Qed.
Next Obligation.
  destruct H as [T' [redT' isar]].
  sq. econstructor. split. eapply type_reduction; eauto.
  eauto using typing_wf_local.
  eauto.
Qed.
Next Obligation.
  sq. apply X1.
Qed.
Next Obligation.
  sq. apply X1.
Qed.
Next Obligation.
  sq. eapply validity in X as [validΣ [|]]. (* contradiction *)
  todo "~ Is_conv_to_Arity pat -> isWfArity pat -> False".
  destruct i as [s Hs]. econstructor; eauto. eapply X1. eauto using typing_wf_local.
Qed.
Next Obligation.
  sq. apply X2.
Qed.
Next Obligation.
  sq. eapply typing_wellformed; eauto. sq; auto. sq; auto. apply X2.
Qed.
Next Obligation.
  sq. red. eexists; split; eauto.
  right. exists pat; split; eauto.
  eapply type_reduction; eauto using typing_wf_local.
Qed.
Next Obligation.
  rename pat0 into T.
  rename pat1 into K.
  rename pat into u.
  sq.
  intros (? & ? & ?).
  destruct s as [ | (? & ? & ?)].
  + destruct H. eapply arity_type_inv; eauto using typing_wf_local.
  + eapply principal_typing in X2 as (? & ? & ? &?). 2:eauto. 2:exact t0.
    eapply cumul_prop1 in c; eauto.
    eapply cumul_prop2 in c0; eauto.

    eapply type_reduction in X0; eauto.

    eapply principal_typing in c0 as (? & ? & ? & ?). 2:eauto. 2:{ exact X0. }

    eapply cumul_prop1 in c; eauto.

    destruct (invert_cumul_sort_r _ _ _ _ c0) as (? & ? & ?).
    destruct (invert_cumul_sort_r _ _ _ _ c1) as (? & ? & ?).
    eapply red_confluence in r as (? & ? & ?); eauto.

    eapply invert_red_sort in r.
    eapply invert_red_sort in r1. subst. inv r1.

    eapply leq_universe_prop in l0 as []; cbn; eauto.
    eapply leq_universe_prop in l as []; cbn; eauto.
    eauto using typing_wf_local.
Qed.

(* Program Definition is_erasable (Sigma : PCUICAst.global_env_ext) (HΣ : ∥wf_ext Sigma∥) (Gamma : context) (HΓ : ∥wf_local Sigma Gamma∥) (t : PCUICAst.term) : *)
(*   typing_result ({∥isErasable Sigma Gamma t∥} +{∥(isErasable Sigma Gamma t -> False) × welltyped Sigma Gamma t∥}) := *)
(*   mlet (T; _) <- @make_graph_and_infer _ _ HΣ Gamma HΓ t ;; *)
(*   mlet b <- is_arity Sigma _ Gamma _ T _ ;; *)
(*   if b : {_} + {_} then *)
(*     ret (left _) *)
(*   else mlet (K; _) <-  @make_graph_and_infer _ _ HΣ Gamma HΓ T ;; *)
(*        mlet (u;_) <- @reduce_to_sort _ Sigma _ Gamma K _ ;; *)
(*       match is_prop_sort u with true => ret (left _) | false => ret (right _) end *)
(* . *)
(* Next Obligation. sq; eauto. Qed. *)
(* Next Obligation. *)
(*   sq. eapply PCUICValidity.validity in X as [_]; eauto.  destruct i. *)
(*   right. sq. eauto. destruct i. econstructor. econstructor. eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   destruct H as (? & ? & ?). *)
(*   sq. exists x. split. *)
(*   eapply type_reduction in X; eauto. eauto. *)
(* Qed. *)
(* Next Obligation. sq; eauto. Qed. *)
(* Next Obligation. *)
(*   sq. eapply PCUICValidity.validity in X as [_]; eauto.  destruct i. *)
(*   econstructor 2. sq. eauto. destruct i. econstructor. econstructor. eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   sq. econstructor. split. eauto. *)
(*   right. exists pat. split; eauto. eapply type_reduction; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   rename pat0 into T. *)
(*   rename pat1 into K. *)
(*   rename pat into u. *)
(*   sq. split. *)
(*   - intros (? & ? & ?). sq. *)
(*      destruct s as [ | (? & ? & ?)]. *)
(*      + destruct H. eapply arity_type_inv; eauto. *)
(*      + eapply principal_typing in X2 as (? & ? & ? &?). 2:eauto. 2:exact t0. *)

(*        eapply cumul_prop1 in c; eauto. *)
(*        eapply cumul_prop2 in c0; eauto. *)

(*        eapply type_reduction in X0; eauto. *)

(*        eapply principal_typing in c0 as (? & ? & ? & ?). 2:eauto. 2:{ exact X0. } *)

(*        eapply cumul_prop1 in c; eauto. *)

(*        destruct (invert_cumul_sort_r _ _ _ _ c0) as (? & ? & ?). *)
(*        destruct (invert_cumul_sort_r _ _ _ _ c1) as (? & ? & ?). *)
(*        eapply red_confluence in r as (? & ? & ?); eauto. *)

(*        eapply invert_red_sort in r. *)
(*        eapply invert_red_sort in r1. subst. inv r1. *)

(*        eapply leq_universe_prop in l0 as []; cbn; eauto. *)
(*        eapply leq_universe_prop in l as []; cbn; eauto. *)
(*   - sq. econstructor. eauto. *)
(* Qed. *)

Section Erase.

  Definition is_box c :=
    match c with
    | E.tBox => true
    | _ => false
    end.

  Fixpoint mkAppBox c n :=
    match n with
    | 0 => c
    | S n => mkAppBox (E.tApp c E.tBox) n
    end.

  Definition on_snd_map {A B C} (f : B -> C) (p : A * B) :=
    (fst p, f (snd p)).

  Variable (Σ : global_env_ext)( HΣ :∥ wf_ext Σ ∥).

  Ltac sq' := try (destruct HΣ; clear HΣ);
             repeat match goal with
                    | H : ∥ _ ∥ |- _ => destruct H; try clear H
                    end; try eapply sq.

  Section EraseMfix.
    Context (erase : forall  (Γ : context) (t : term) (Ht : welltyped Σ Γ t), typing_result E.term).

    Program Definition erase_mfix Γ (defs : mfixpoint term) : typing_result (EAst.mfixpoint E.term) :=
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
      monad_map (fun d => H <- _ ;;
                   dbody' <- erase Γ' d.(dbody) H;;
                          ret ({| E.dname := d.(dname); E.rarg := d.(rarg);
                                  E.dbody := dbody' |})) defs.
    Next Obligation.
      clear erase.
      destruct (wf_ext_is_graph HΣ) as [].
      apply Checked. todo "well-typed fix body".
    Defined.
      (* epose proof ((fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix} *)
      (*         : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥) *)
      (*         := match mfix with *)
      (*            | [] => ret (sq wf_local_rel_nil) *)
      (*            | def :: mfix => *)
      (*  (* probably not tail recursive but needed so that next line terminates *) *)
      (*              W <- infer_type _ (infer _ _ _ _) Γ HΓ (dtype def) ;; *)
      (*              let W' := weakening_sq acc _ _ W.π2 in *)
      (*              bind (Monad := typing_monad) (check_types mfix *)
      (*                (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def))) *)
      (*                (wf_local_rel_abs_sq Hacc (W.π1; W'))) (fun Z => *)
      (*              ret (wf_local_rel_app_inv_sq *)
      (*                     (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)) *)
      (*            end) *)
      (*      defs [] (sq wf_local_rel_nil)). *)
      (* destruct X. econstructor. *)
    (*   sq'. eapply wf_local_local_rel. *)
    (*   eapply wf_local_rel_app_inv. eapply wf_local_rel_local. eauto. *)
    (*   change fix_context with (fix_context_i #|@nil context_decl|). *)
    (*   now rewrite app_context_nil_l. *)
    (*   sq. econstructor 2. exact t. *)
    (*   Unshelve. all:sq'; eauto. firstorder. *)
    (*   eapply wf_local_app_inv. eauto. eauto. *)
    (* Qed. *)

  End EraseMfix.

  Equations(noind) erase (Γ : context) (t : term) (Ht : welltyped Σ Γ t) : typing_result E.term :=
    erase Γ t Ht with (is_erasable Σ HΣ Γ t Ht) :=
    {
      erase Γ _ Ht (Checked (left _)) := ret (E.tBox);
      erase Γ _ Ht (TypeError t) := TypeError t ;
      erase Γ (tRel i) Ht _ := ret (E.tRel i) ;
      erase Γ (tVar n) Ht _ := ret (E.tVar n) ;
      erase Γ (tEvar m l) Ht _ := l' <- monad_map (fun x => erase Γ x _) l;; ret (E.tEvar m l') ;
      erase Γ (tSort u) Ht _ := ret E.tBox

      ; erase Γ (tConst kn u) Ht _ := ret (E.tConst kn)
      ; erase Γ (tInd kn u) Ht _ := ret E.tBox
      ; erase Γ (tConstruct kn k u) Ht _ := ret (E.tConstruct kn k)
      ; erase Γ (tProd na b t) Ht _ := ret E.tBox
      ; erase Γ (tLambda na b t) Ht _ :=
                           t' <- erase (vass na b :: Γ) t _;;
                              ret (E.tLambda na t')
      ; erase Γ (tLetIn na b t0 t1) Ht _ :=
                              b' <- erase Γ b _;;
                                 t1' <- erase (vdef na b t0 :: Γ) t1 _;;
                                 ret (E.tLetIn na b' t1')
      ; erase Γ (tApp f u) Ht _ :=
                     f' <- erase Γ f _;;
                     l' <- erase Γ u _;;
                     ret (E.tApp f' l')
      ; erase Γ (tCase ip p c brs) Ht _ :=
          c' <- erase Γ c _;;
          if is_box c' then
            match brs with
            | (a, b) :: brs => b' <- erase Γ b _ ;; ret (E.mkApps b' (repeat E.tBox a))
            | [] => ret (E.tCase ip c' [])
            end
          else
            brs' <- monad_map (T :=typing_result) (fun x => x' <- erase Γ (snd x) _;; ret (fst x, x')) brs;;
            ret (E.tCase ip c' brs')
      ; erase Γ (tProj p c) Ht _ :=
          c' <- erase Γ c _;;
          if is_box c' then ret (E.tBox) else
          ret (E.tProj p c')
      ; erase Γ (tFix mfix n) Ht _ :=
          mfix' <- erase_mfix erase Γ mfix;;
          ret (E.tFix mfix' n)
      ; erase Γ (tCoFix mfix n) Ht _ :=
                          mfix' <- erase_mfix (erase) Γ mfix;;
                                ret (E.tCoFix mfix' n)
    }.
  Next Obligation. todo "monad_map enhancement for erasing lists". Qed.
  Next Obligation. 
    destruct Ht.
    destruct HΣ.
    eapply inversion_Lambda in X as (? & ? & ? & ? & ?) ; auto.
    exists x0; auto.
  Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.
  Next Obligation. todo "inversion". Qed.

End Erase.

Require Import ErasureCorrectness.
Arguments iswelltyped {cf Σ Γ t A}.
Lemma erases_erase (Σ : global_env_ext) Γ t T (wfΣ : ∥wf_ext Σ∥) t' :
  Σ ;;; Γ |- t : T ->
                 forall (wt : welltyped Σ Γ t),
  erase Σ wfΣ Γ t wt = Checked t' ->
  erases Σ Γ t t'.
Proof.
  Hint Constructors typing erases.
  intros. sq.
  (* pose proof (typing_wf_local X0). *)


  pose (wfΣ' := sq w).
  pose (wfΓ := typing_wf_local X).
  change (erase Σ wfΣ' Γ t wt = Checked t') in H.


  revert H.
  clearbody wfΣ' wfΓ.

  revert Γ wfΓ t T X wt t' wfΣ'.
  eapply(typing_ind_env (fun Σ Γ t T =>
       forall (wt : welltyped Σ Γ t) (t' : E.term) (wfΣ' : ∥ wf_ext Σ ∥),
  erase Σ wfΣ' Γ t wt = Checked t' -> Σ;;; Γ |- t ⇝ℇ t'
         )); intros.

  all:eauto.

  all: simp erase in *.
  all: unfold erase_clause_1 in *.
  all:sq.
  all: unfold bind in *.
  all: cbn in *; repeat (try destruct ?;  repeat match goal with
                                          [ H : Checked _ = Checked _ |- _ ] => inv H
                                        | [ H : TypeError _ = Checked _ |- _ ] => inv H
                                        | [ H : welltyped _ _ _ |- _ ] => destruct H as []
                                             end; sq; eauto).

  - repeat econstructor; eauto.
  - econstructor. econstructor. clear E.
    eapply inversion_Prod in X2 as (? & ? & ? & ? & ?) ; auto.
    split. econstructor; eauto. left. econstructor.
  - econstructor. eauto. econstructor. clear E.
    eapply inversion_Ind in X1 as (? & ? & ? & ? & ? & ?) ; auto.
    split. econstructor; eauto. left. subst.
    eapply isArity_subst_instance.
    eapply isArity_ind_type; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* - econstructor. *)
  (*   eapply elim_restriction_works. eauto. eauto. eauto. intros. *)
  (*   eapply f, isErasable_Proof. eauto. eauto. *)

  (*   pose proof (Prelim.monad_map_All2 _ _ _ brs a2 E2). *)

  (*   eapply All2_All_left in X3. 2:{ intros. destruct X4. exact e. } *)

  (*   eapply All2_impl. *)
  (*   eapply All2_All_mix_left. eassumption. eassumption. *)
  (*   intros. destruct H5. *)
  (*   destruct ?; inv e0. cbn. eauto. *)
  - econstructor.
    clear E.
    admit.
    (* destruct isdecl as (? & ? & ?). *)
    (* eapply elim_restriction_works_proj; eauto. intros. *)
    (* eapply isErasable_Proof in X2. eauto. *)

    (* eauto. *)
  - clear E. econstructor.
    unfold erase_mfix in *.
    repeat destruct ?; try congruence.
    (* pose proof (Prelim.monad_map_All2 _ _ _ mfix a1 E1). *)
    (* eapply All2_impl. eapply All2_All_mix_left. exact X0. eassumption. *)

    (* intros. destruct X1. cbn in *. unfold bind in e. cbn in e. *)
    (* repeat destruct ?; try congruence; inv e. *)

    (* cbn. repeat split; eauto. *)
    (* eapply p. eauto. *)
  (* - clear E. inv t; discriminate. *)
Admitted.

Lemma erase_Some_typed {Σ wfΣ Γ t wft r} :
  erase Σ wfΣ Γ t wft = Checked r -> exists T, ∥Σ ;;; Γ |- t : T∥.
Proof.
  rewrite erase_equation_1.
  destruct is_erasable; cbn; intros; try congruence. clear H.
  destruct a as [ [(? & ? &?)] | []]. exists x; sq; eauto.
  destruct wft as [i Hi]. exists i; sq; eauto.
Qed.

Definition optM {M : Type -> Type} `{Monad M} {A B} (x : option A) (f : A -> M B) : M (option B) :=
  match x with
  | Some x => y <- f x ;; ret (Some y)
  | None => ret None
  end.

Lemma wf_local_nil {Σ} : ∥ wf_local Σ [] ∥.
Proof. repeat econstructor. Qed.

Program Definition erase_constant_body Σ wfΣ (cb : constant_body)
  (Hcb : ∥ on_constant_decl (lift_typing typing) Σ cb ∥) : typing_result E.constant_body :=
  (* ty <- erase Σ wfΣ [] cb.(cst_type) _ ;; *)
  body <- match cb.(cst_body) with
          | Some b =>
            t <- (erase Σ wfΣ [] b _) ;;
            ret (Some t)
          | None => ret None
          end;;
  ret {| E.cst_body := body; |}.
Next Obligation.
Proof.
  sq. red in X. rewrite <-Heq_anonymous in X. simpl in X.
  eexists; eauto.
Qed.

Definition lift_opt_typing {A} (a : option A) (e : type_error) : typing_result A :=
  match a with
  | Some x => ret x
  | None => raise e
  end.

Program
Definition erase_one_inductive_body (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) npars
  (arities : context)
           (oib : one_inductive_body) : typing_result E.one_inductive_body :=

  decty <- lift_opt_typing (decompose_prod_n_assum [] npars oib.(ind_type))
        (NotAnInductive oib.(ind_type)) ;;
  let '(params, arity) := (decty : context * term) in
  (* type <- erase Σ wfΣ [] wf_local_nil oib.(ind_type) ;; *)
  ctors <- monad_map (A:=(ident * term) * nat) (fun '((x, y), z) => y' <- erase Σ wfΣ arities y _;; ret (x, y', z)) oib.(ind_ctors);;
  (* FIXME not used! let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in *)
  projs <- monad_map (fun '(x, y) => y' <- erase Σ wfΣ [] (y : term) _;; ret (x, y')) oib.(ind_projs);;
  ret {| E.ind_name := oib.(ind_name);
         E.ind_kelim := oib.(ind_kelim);
         E.ind_ctors := ctors;
         E.ind_projs := projs |}.
Next Obligation.
  intros. todo "welltyped threading".
Qed.
Next Obligation.
  intros. todo "welltyped threading".
Qed.

Program Definition erase_mutual_inductive_body Σ wfΣ
           (mib : mutual_inductive_body)
: typing_result E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  bodies <- monad_map (erase_one_inductive_body Σ wfΣ mib.(ind_npars) arities) bds ;;
  ret {| E.ind_npars := mib.(ind_npars);
         E.ind_bodies := bodies; |}.

Program Fixpoint erase_global_decls Σ : ∥ wf Σ ∥ -> typing_result E.global_declarations := fun wfΣ =>
  match Σ with
  | [] => ret []
  | ConstantDecl kn cb :: Σ =>
    cb' <- erase_constant_body (Σ, cst_universes cb) _ cb _;;
    Σ' <- erase_global_decls Σ _;;
    ret (E.ConstantDecl kn cb' :: Σ')
  | InductiveDecl kn mib :: Σ =>
    mib' <- erase_mutual_inductive_body (Σ, ind_universes mib) _ mib ;;
    Σ' <- erase_global_decls Σ _;;
    ret (E.InductiveDecl kn mib' :: Σ')
  end.
Next Obligation.
  sq. split. cbn.
  eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
  now inversion X; subst.
Qed.
Next Obligation.
  sq.
  inv X. apply X1.
Qed.
Next Obligation.
  sq. inv X. apply X0.
Qed.


Next Obligation.
  sq. split. cbn.
  eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
  now inversion X; subst.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.

Program Definition erase_global Σ : ∥wf Σ∥ -> _:=
  fun wfΣ  =>
  Σ' <- erase_global_decls Σ wfΣ ;;
  ret Σ'.


Lemma erase_global_correct Σ (wfΣ : ∥ wf Σ∥) Σ' :
  erase_global Σ wfΣ = Checked Σ' ->
  erases_global Σ Σ'.
Proof.
  induction Σ in wfΣ, Σ' |- *; intros; sq.
  - inv H. econstructor.
  - cbn in H. unfold bind in *. cbn in *. repeat destruct ?; try congruence.
    + inv H. inv E.
      unfold erase_constant_body in E1.
      unfold bind in E1. cbn in E1. repeat destruct ?; try congruence.
      inv E1. econstructor.
      all:todo "finish".
(*    * unfold optM in E0. destruct ?; try congruence.
        -- unfold erases_constant_body.
          cbn. cbn in *.
           destruct ( erase (Σ, _)
           (erase_global_decls_obligation_1 (ConstantDecl k c :: Σ)
              (sq w) k c Σ eq_refl) [] wf_local_nil t) eqn:E5;
             rewrite E5 in E0; inv E0.
           rewrite E1.
           eapply erases_erase. 2:eauto.
           instantiate (1 := cst_type c).
           (* admit. *)
           clear - w E1.
           inv w. cbn in X0.
           cbn in *. unfold on_constant_decl in X0.
           rewrite E1 in X0. cbn in X0. eassumption.
        -- cbn. inv E0. unfold erases_constant_body.
           rewrite E1. cbn. econstructor.
      * eapply IHΣ. unfold erase_global. rewrite E2. reflexivity.
    + inv H. inv E. inv E1.
      unfold erase_mutual_inductive_body, bind in H0. cbn in H0.
      destruct ?; try congruence. inv H0.
      econstructor.
      * econstructor; cbn; eauto.
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E).
        eapply All2_Forall2.
        eapply All2_impl. eassumption.

        intros. cbn in H0.
        unfold erase_one_inductive_body, bind in H0. cbn in H0.
        repeat destruct ?; try congruence.
        inv H0.
        unfold erases_one_inductive_body. cbn. destruct ?; cbn.
        (* unfold lift_opt_typing in E. *)
        (* destruct decompose_prod_n_assum eqn:E6; inv E. cbn. *)
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E3).
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E4). repeat split; eauto.
        -- eapply All2_Forall2.
           eapply All2_impl_In. eassumption.
           intros. destruct x0, p, y, p. cbn in *.
           destruct ?; try congruence.
           inv H4. split; eauto.

           (* pose (t' := t). inv t'. cbn in *. *)
           destruct (erase_Some_typed E5) as [? []].

           eapply erases_erase. 2:eauto. eauto.
        -- eapply All2_Forall2.
           eapply All2_impl_In. eassumption.
           intros. cbn in H2. destruct x0, y.
           destruct ?; try congruence;
             inv H4. split; eauto.

           (* pose (t' := t). inv t'. cbn in *. *)
           destruct (erase_Some_typed E5) as [? []].

           eapply erases_erase.
           2:{ eauto. } eauto.
  * eapply IHΣ. unfold erase_global. rewrite E2. reflexivity. *)
    + todo "finish".
Qed.
