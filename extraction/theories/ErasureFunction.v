(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSafeChecker PCUICLiftSubst.
From MetaCoq.Extraction Require EAst ELiftSubst ETyping EWcbvEval Extract ExtractionCorrectness.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.

Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

Require Import Extract.

Parameter is_type_or_proof :
  forall (Sigma : PCUICAst.global_context) (HΣ : ∥wf Sigma∥) (Gamma : context) (HΓ : ∥wf_local Sigma Gamma∥) (t : PCUICAst.term),
    {r : typing_result bool & match r with
                           | Checked true => Is_Type_or_Proof Sigma Gamma t 
                           | Checked false => (Is_Type_or_Proof Sigma Gamma t -> False) × PCUICSafeLemmata.welltyped Sigma Gamma t
                           | _ => True
                           end}.


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

  Section EraseMfix.
    Context (extract : forall (Σ : global_context) (wfΣ : ∥ wf Σ ∥) (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result E.term).

    Program Definition extract_mfix Σ (wfΣ : ∥wf Σ∥) Γ (HΓ : ∥wf_local Σ Γ∥) (defs : mfixpoint term) : typing_result (EAst.mfixpoint E.term) :=
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
      monad_map (fun d => H <- _ ;;
                   dbody' <- extract Σ wfΣ Γ' H d.(dbody);;
                          ret ({| E.dname := d.(dname); E.rarg := d.(rarg);
                                  E.dbody := dbody' |})) defs.
    Next Obligation.
      clear extract.
      
      epose proof ((fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix}
              : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥)
              := match mfix with
                 | [] => ret (sq wf_local_rel_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening_sq acc _ _ W.π2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (wf_local_rel_abs_sq Hacc (W.π1; W')) ;;
                   ret (wf_local_rel_app_inv_sq
                          (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)
                 end)
           defs [] (sq _)).
      destruct X. econstructor .
      sq. eapply wf_local_local_rel.
      eapply wf_local_rel_app_inv. eapply wf_local_rel_local. eauto.
      change fix_context with (fix_context_i #|@nil context_decl|).
      now rewrite app_context_nil_l.
      sq. econstructor 2. exact t.
      Unshelve. (* I believe those go away once infer works on squashed assumptions *)
    Admitted.
      
  End EraseMfix.

  Fixpoint extract (Σ : global_context) (HΣ : ∥wf Σ∥) (Γ : context) (HΓ : ∥wf_local Σ Γ∥) (t : term) {struct t} : typing_result E.term.
  Proof.
    destruct (is_type_or_proof Σ HΣ Γ HΓ t) eqn:E1.
    destruct x as [b | ] eqn:E2.
    destruct b eqn:E3.
    - exact (ret (E.tBox)).
    - revert y E1. refine (match t with
             | tRel i => fun _ _ => ret (E.tRel i)
             | tVar n => fun _ _ =>  ret (E.tVar n)
             | tEvar m l => fun _ _ => 
               l' <- monad_map (extract Σ HΣ Γ HΓ) l;;
                  ret (E.tEvar m l')
             | tSort u => fun _ _ =>  ret E.tBox
             | tConst kn u => fun _ _ =>  ret (E.tConst kn)
             | tInd kn u => fun _ _ =>  ret E.tBox
             | tConstruct kn k u => fun _ _ =>  ret (E.tConstruct kn k)
             | tProd na b t => fun _ _ =>  ret E.tBox
             | tLambda na b t => fun _ _ => 
               t' <- extract Σ HΣ (vass na b :: Γ) _ t;;
                  ret (E.tLambda na t')
             | tLetIn na b t0 t1 => fun _ _ => 
               b' <- extract Σ HΣ Γ HΓ b;;
                  t1' <- extract Σ HΣ (vdef na b t0 :: Γ) _ t1;;
                  ret (E.tLetIn na b' t1')
             | tApp f u => fun _ _ => 
               f' <- extract Σ HΣ Γ HΓ f;;
                  l' <- extract Σ HΣ Γ HΓ u;;
                  ret (E.tApp f' l') (* if is_dummy f' then ret dummy else *)
             | tCase ip p c brs => fun _ _ => 
               c' <- extract Σ HΣ Γ HΓ c;;
                  brs' <- monad_map (T:=typing_result) (fun x => x' <- extract Σ HΣ Γ HΓ (snd x);; ret (fst x, x')) brs;;
                  ret (E.tCase ip c' brs')
             | tProj p c => fun _ _ => 
               c' <- extract Σ HΣ Γ HΓ c;;
                  ret (E.tProj p c')
             | tFix mfix n => fun _ _ =>  
                 mfix' <- extract_mfix (extract) Σ HΣ Γ HΓ mfix;;
                 ret (E.tFix mfix' n)
             | tCoFix mfix n => fun _ _ =>  
                 mfix' <- extract_mfix (extract) Σ HΣ Γ HΓ mfix;;
                 ret (E.tCoFix mfix' n)
              end).
      
      + destruct p as [? []]. sq. clear e.
        Require Import MetaCoq.PCUIC.PCUICInversion. 
        
        eapply inversion_Lambda in t1 as (? & ? & ? & ? & ?).
        econstructor; cbn; eauto.
      + destruct p as [? []]. sq. clear e.
                
        eapply inversion_LetIn in t2 as (? & ? & ? & ? & ? & ?).
        econstructor; cbn; eauto.
    - exact (TypeError t0).
  Defined.

End Erase.

Require Import Extract ExtractionCorrectness.

Lemma erases_extract Σ Γ t T (wfΣ : ∥wf Σ∥) (wfΓ : ∥wf_local Σ Γ∥) t' :
  Σ ;;; Γ |- t : T ->
  extract Σ (wfΣ) Γ (wfΓ) t = Checked t' ->                
  erases Σ Γ t t'.
Proof.
  Hint Constructors typing erases.
  Hint Resolve is_type_or_proof_spec.
  intros. sq.
  (* pose proof (typing_wf_local X0). *)

    
  pose (wfΣ' := sq t0).
  pose (wfΓ' := sq a).
  change (extract Σ wfΣ' Γ wfΓ' t = Checked t') in H.

  revert H.
  generalize wfΣ' wfΓ'. clear wfΣ' wfΓ'.
  
  revert Σ t0 Γ a t T X t'.
  eapply (typing_ind_env (fun Σ Γ t T =>   forall (t' : E.term) (wfΣ' : ∥ wf Σ ∥) (wfΓ' : ∥ wf_local Σ Γ ∥),
  extract Σ wfΣ' Γ wfΓ' t = Checked t' -> Σ;;; Γ |- t ⇝ℇ t'
         )); intros.

  all: (cbn in *; repeat destruct ?;
                                 repeat match goal with
                                          [ H : Checked _ = Checked _ |- _ ] => inv H
                                        | [ H : TypeError _ = Checked _ |- _ ] => inv H
                                        | [ H : _ × PCUICSafeLemmata.welltyped _ _ _ |- _ ] => destruct H as [? []]
                                        end; eauto); subst.

  - repeat econstructor; eauto.
  - econstructor. econstructor. clear E.
    eapply inversion_Prod in t0 as (? & ? & ? & ? & ?).
    split. eauto. left. econstructor.
  - econstructor. econstructor. clear E.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?).
    split. eauto. left.
    eapply isArity_subst_instance. eapply isArity_ind_type.
  - econstructor.
    eapply elim_restriction_works. intros.
    eapply f, Is_Type_or_Proof_Proof. eauto. eauto.
    
    pose proof (Prelim.monad_map_All2 _ _ _ brs a1 E3).
    
    eapply All2_All_left in X3. 2:{ intros. destruct X4. exact e. }

    eapply All2_impl.
    eapply All2_All_mix_left. eassumption. eassumption.
    intros. destruct H5.
    destruct ?; inv e0. cbn. eauto.
  - econstructor.

    eapply elim_restriction_works_proj. intros.
    eapply Is_Type_or_Proof_Proof in X2. eauto.

    eauto.
  - econstructor.
    unfold extract_mfix in *.
    pose proof (Prelim.monad_map_All2 _ _ _ mfix a0 E2).
    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.

    intros. destruct X1. cbn in *. repeat destruct ?; inv e. 
    cbn. repeat split; eauto. 
    eapply p. eauto. 
  - econstructor.
    unfold extract_mfix in *.
    pose proof (Prelim.monad_map_All2 _ _ _ mfix a0 E2).
    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.

    intros. destruct X1. cbn in *. repeat destruct ?; inv e.
    cbn. repeat split; eauto. 
    eapply p. eauto. 
Qed.

Definition optM {M : Type -> Type} `{Monad M} {A B} (x : option A) (f : A -> M B) : M (option B) :=
  match x with
  | Some x => y <- f x ;; ret (Some y)
  | None => ret None
  end.

Lemma wf_local_nil {Σ} : ∥ wf_local Σ [] ∥.
Proof. repeat econstructor. Qed.

Definition extract_constant_body Σ wfΣ (cb : constant_body) : typing_result E.constant_body :=
  ty <- extract Σ wfΣ [] wf_local_nil cb.(cst_type) ;;
  body <- optM cb.(cst_body) (fun b => extract Σ wfΣ [] wf_local_nil b);;
  ret {| E.cst_body := body; |}.

Definition lift_opt_typing {A} (a : option A) (e : type_error) : typing_result A :=
  match a with
  | Some x => ret x
  | None => raise e
  end.

Definition extract_one_inductive_body Σ wfΣ npars arities Har
           (oib : one_inductive_body) : typing_result E.one_inductive_body :=
  decty <- lift_opt_typing (decompose_prod_n_assum [] npars oib.(ind_type))
        (NotAnInductive oib.(ind_type)) ;;
  let '(params, arity) := decty in
  type <- extract Σ wfΣ [] wf_local_nil oib.(ind_type) ;;
  ctors <- monad_map (fun '(x, y, z) => y' <- extract Σ wfΣ arities Har y;; ret (x, y', z)) oib.(ind_ctors);;
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  projs <- monad_map (fun '(x, y) => y' <- extract Σ wfΣ [] wf_local_nil y;; ret (x, y')) oib.(ind_projs);;
  ret {| E.ind_name := oib.(ind_name);
         E.ind_kelim := oib.(ind_kelim);
         E.ind_ctors := ctors;
         E.ind_projs := projs |}.

Program Definition extract_mutual_inductive_body Σ wfΣ
           (mib : mutual_inductive_body) (Hm :   ∥ wf_local Σ (arities_context (ind_bodies mib)) ∥)
: typing_result E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  bodies <- monad_map (extract_one_inductive_body Σ wfΣ mib.(ind_npars) arities _) bds ;;
  ret {| E.ind_npars := mib.(ind_npars);
         E.ind_bodies := bodies; |}.

Program Fixpoint extract_global_decls univs Σ : ∥ wf (Σ, univs) ∥ -> typing_result E.global_declarations := fun wfΣ =>
  match Σ with
  | [] => ret []
  | ConstantDecl kn cb :: Σ => 
    cb' <- extract_constant_body (Σ, univs) _ cb;;
    Σ' <- extract_global_decls univs Σ _;;
    ret (E.ConstantDecl kn cb' :: Σ')
  | InductiveDecl kn mib :: Σ => 
    mib' <- extract_mutual_inductive_body (InductiveDecl kn mib :: Σ, univs) _ mib _ ;;
    Σ' <- extract_global_decls univs Σ _;;
    ret (E.InductiveDecl kn mib' :: Σ')
  end.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.
Next Obligation.
  Require Import MetaCoq.PCUIC.PCUICWeakeningEnv.
  sq. eapply PCUICSubstitution.wf_arities_context. eauto.
  
  cbn. instantiate (1 := kn). unfold declared_minductive.
  cbn. destruct (ident_eq_spec kn kn). all:try congruence.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.

Program Definition extract_global Σ : ∥wf Σ∥ -> _:=
  match Σ with (Σ, univs) => fun wfΣ  =>
  Σ' <- extract_global_decls univs Σ wfΣ ;;
  ret Σ' end.

Lemma extract_global_correct Σ (wfΣ : ∥ wf Σ∥) Σ' :
  extract_global Σ wfΣ = Checked Σ' ->
  erases_global Σ Σ'.
Proof.
  destruct Σ as (Σ, univs).
  induction Σ in wfΣ, Σ' |- *; cbn; intros.
  - inv H. econstructor.
  - repeat destruct ?; try congruence.
    + inv H. inv E. inv E1. econstructor.
      * unfold erases_constant_body.
        unfold optM in E4. destruct ?; try congruence.
        -- cbn. cbn in *.
           destruct (         extract (Σ, univs)
           (extract_global_decls_obligation_1 univs (ConstantDecl k c :: Σ) wfΣ k c Σ
              eq_refl) [] wf_local_nil t
                    ) eqn:E5;
             rewrite E5 in E4; inv E4.
           eapply erases_extract. 2:eauto.
           admit.
        -- cbn. inv E4. econstructor.
      * eapply IHΣ. unfold extract_global. rewrite E2. reflexivity.
    + inv H. inv E. inv E1.
      econstructor.
      * econstructor; cbn; eauto.
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E3).
        eapply All2_Forall.
        eapply All2_impl. eassumption.

        intros. cbn in H0. repeat destruct ?; try congruence.
        inv H0. unfold erases_one_inductive_body. cbn.
        unfold lift_opt_typing in E.
        destruct decompose_prod_n_assum eqn:E6; inv E. cbn.
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E4). 
        pose proof (Prelim.monad_map_All2 _ _ _ _ _ E5). repeat split; eauto.
        -- eapply All2_Forall.
           eapply All2_impl. eassumption.
           intros. destruct x0, p, y, p. cbn in *.
           destruct ?; try congruence.
           inv H2. split; eauto.
           eapply erases_extract. 2:eauto. admit. admit.
        -- eapply All2_Forall.
           eapply All2_impl. eassumption.
           intros. cbn in H2. destruct x0, y.
           destruct ?; try congruence.
           inv H2. split; eauto.
           eapply erases_extract. 2:eauto. admit. admit.
      * eapply IHΣ. unfold extract_global. rewrite E2. reflexivity.
Admitted.
