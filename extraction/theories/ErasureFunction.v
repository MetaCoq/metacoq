
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICChecker PCUICMetaTheory PCUICWcbvEval PCUICSafeChecker PCUICLiftSubst PCUICInversion PCUICSR PCUICNormal PCUICSafeReduce.
From MetaCoq.Extraction Require EAst ELiftSubst ETyping EWcbvEval Extract ExtractionCorrectness.
From Equations Require Import Equations.
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

Fixpoint infer' Σ (HΣ : ∥wf Σ∥) (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) {struct t}
  : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }).
Admitted.

Definition Is_conv_to_Arity Σ Γ T := exists T', ∥red Σ Γ T T'∥ /\ isArity T'.

Ltac terror := try match goal with [t : type_error |- typing_result _] => exact (TypeError t) end.

Fixpoint is_arity Σ (HΣ : wf Σ) Γ (HΓ : wf_local Σ Γ) T (HT : PCUICSafeLemmata.wellformed Σ Γ T) : typing_result ({Is_conv_to_Arity Σ Γ T} + {~ Is_conv_to_Arity Σ Γ T}).
Proof.
  edestruct @reduce_to_sort with (t := T) as [[u] | ]; try eassumption.
  - left. left. sq. econstructor. split.
    sq. eassumption. econstructor.
  - clear t. edestruct @reduce_to_prod with (t := T); try eassumption.
    + destruct a as (? & ? & ? & ?).
      edestruct (is_arity Σ HΣ (Γ ,, vass x x0)) with (T := x1).
      * enough (∥ wf_local Σ (Γ,, vass x x0) ∥) by admit. destruct HT as [ [] | []];  sq.
        -- econstructor; cbn; eauto.
           eapply subject_reduction in X; eauto.
           eapply inversion_Prod in X as (? & ? & ? & ? & ?). eauto.
        -- econstructor; cbn; eauto.
           eapply PCUICSafeReduce.isWfArity_red in X; eauto. 
           2: exact RedFlags.default.
           destruct X as (? & ? & ? & ?). cbn in *.
           admit.           
      * sq. destruct HT as [ [] | [] ].
        -- eapply subject_reduction in X; eauto.
           eapply inversion_Prod in X as (? & ? & ? & ? & ?). 
           do 2 econstructor. eauto.
        -- econstructor 2. sq.
           eapply PCUICSafeReduce.isWfArity_red in X; eauto. 2:exact RedFlags.default.
           admit.           
      * left. destruct a.
        -- left. destruct i as (? & ? & ?). exists (tProd x x0 x2). split; sq.
           etransitivity. eassumption. eapply PCUICReduction.red_prod. econstructor.
           eassumption. now cbn.
        -- right. intros (? & ? & ?). sq. 
Admitted.      

(* Fixpoint is_proposition Σ (HΣ : wf Σ) Γ (HΓ : wf_local Σ Γ) T (HT : PCUICSafeLemmata.wellformed Σ Γ T) : *)
(*   typing_result *)

Lemma arity_type_inv Σ Γ t T1 T2 :
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
Admitted.

Lemma proposition_type_inv Σ Γ t T u :
  Σ ;;; Γ |- t : tSort u -> is_prop_sort u -> Σ ;;; Γ |- t : T -> red Σ Γ T (tSort u).
Proof.
Admitted.

Definition is_type_or_proof :
  forall (Sigma : PCUICAst.global_context) (HΣ : ∥wf Sigma∥) (Gamma : context) (HΓ : ∥wf_local Sigma Gamma∥) (t : PCUICAst.term),
    {r : typing_result bool & match r with
                           | Checked true => Is_Type_or_Proof Sigma Gamma t 
                           | Checked false => (Is_Type_or_Proof Sigma Gamma t -> False) × PCUICSafeLemmata.welltyped Sigma Gamma t
                           | _ => True
                           end}.
Proof.
  intros. destruct (@infer' _ HΣ Gamma HΓ t) as [ [T] | ].
  2:{ exists (TypeError t0). eauto. }
  edestruct is_arity with (Σ := Sigma) (Γ := Gamma)(T := T) as [[ | ] | ].
  - admit.
  - admit.
  - sq. eapply PCUICValidity.validity in X as [_]; eauto.  destruct i.
    econstructor 2. sq. eauto. destruct i. econstructor. econstructor. eauto.
  - exists (Checked true). econstructor. split. admit. admit.
  - destruct (@infer' _ HΣ Gamma HΓ T) as [ [K] | ].
    + destruct @reduce_to_sort with (Σ := Sigma) ( Γ := Gamma) (t := K).
      * admit.
      * sq. eapply PCUICValidity.validity in X as [_]; eauto.  destruct i.
        econstructor 2. sq. eauto. destruct i. econstructor. econstructor. eauto.
      * destruct a. destruct (is_prop_sort x) eqn:E.
        -- exists (Checked true). econstructor. split. admit.
           right. exists x. admit.
        -- exists (Checked false). split.
           ++ admit.
           ++ sq. econstructor. eauto.
      * exists (TypeError t0). econstructor.
    + exists (TypeError t0). econstructor.
  - exists (TypeError t0). econstructor.
Admitted.

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

  Variable (Σ : global_context)( HΣ :∥ wf Σ ∥).
      
  Ltac sq :=
    repeat match goal with
           | H : ∥ _ ∥ |- _ => destruct H; try clear H
           end; try eapply sq.

  Section EraseMfix.
    Context (erase : forall  (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result E.term).

    Program Definition erase_mfix Γ (HΓ : ∥wf_local Σ Γ∥) (defs : mfixpoint term) : typing_result (EAst.mfixpoint E.term) :=
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
      monad_map (fun d => H <- _ ;;
                   dbody' <- erase Γ' H d.(dbody);;
                          ret ({| E.dname := d.(dname); E.rarg := d.(rarg);
                                  E.dbody := dbody' |})) defs.
    Next Obligation.
      clear erase.
      
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
      destruct X. econstructor.

      
      sq. eapply wf_local_local_rel.
      eapply wf_local_rel_app_inv. eapply wf_local_rel_local. eauto.
      change fix_context with (fix_context_i #|@nil context_decl|).
      now rewrite app_context_nil_l.
      sq. econstructor 2. exact t.
      Unshelve. (* I believe those go away once infer works on squashed assumptions *)
    Admitted.
      
  End EraseMfix.

  (* Program Fixpoint erase (Γ : context) (HΓ : ∥wf_local Σ Γ∥) (t : term) {struct t} : typing_result E.term := *)
  (*   match is_type_or_proof Σ HΣ Γ HΓ t with *)
  (*   | (Checked true ; H) => ret (E.tBox) *)
  (*   | (TypeError t ; H) => TypeError t *)
  (*   | (Checked false ; H ) => (match t with *)
  (*                             | tRel i => ret (E.tRel i) *)
  (*                             | tVar n =>  ret (E.tVar n) *)
  (*                             | tEvar m l => *)
  (*                               l' <- monad_map (erase Γ HΓ) l;; *)
  (*                                  ret (E.tEvar m l') *)
  (*                             | tSort u =>  ret E.tBox *)
  (*                             | tConst kn u =>  ret (E.tConst kn) *)
  (*                             | tInd kn u =>  ret E.tBox *)
  (*                             | tConstruct kn k u =>  ret (E.tConstruct kn k) *)
  (*                             | tProd na b t =>  ret E.tBox *)
  (*                             | tLambda na b t => *)
  (*                               t' <- erase (vass na b :: Γ) _ t;; *)
  (*                                  ret (E.tLambda na t') *)
  (*                             | tLetIn na b t0 t1 => *)
  (*                               b' <- erase Γ HΓ b;; *)
  (*                                  t1' <- erase (vdef na b t0 :: Γ) _ t1;; *)
  (*                                  ret (E.tLetIn na b' t1') *)
  (*                             | tApp f u => *)
  (*                               f' <- erase Γ HΓ f;; *)
  (*                                  l' <- erase Γ HΓ u;; *)
  (*                                  ret (E.tApp f' l') *)
  (*                             | tCase ip p c brs => *)
  (*                               c' <- erase Γ HΓ c;; *)
  (*                                  brs' <- monad_map (T:=typing_result) (fun x => x' <- erase Γ HΓ (snd x);; ret (fst x, x')) brs;; *)
  (*                                  ret (E.tCase ip c' brs') *)
  (*                             | tProj p c => *)
  (*                               c' <- erase Γ HΓ c;; *)
  (*                                  ret (E.tProj p c') *)
  (*                             | tFix mfix n => *)
  (*                               mfix' <- erase_mfix (erase) Γ HΓ mfix;; *)
  (*                                     ret (E.tFix mfix' n) *)
  (*                             | tCoFix mfix n => *)
  (*                               mfix' <- erase_mfix (erase) Γ HΓ mfix;; *)
  (*                                     ret (E.tCoFix mfix' n) *)
  (*                             end) *)
  (*   end. *)
  (* Next Obligation. *)
  (*   destruct w. sq. econstructor; eauto. cbn. clear Heq_anonymous. *)
        
  (*   eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?). *)
  (*   econstructor; cbn; eauto. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   destruct w. sq. econstructor; eauto. cbn. clear Heq_anonymous. *)
  (*   eapply inversion_LetIn in t as (? & ? & ? & ? & ? & ?). *)
  (*   econstructor; cbn; eauto. *)
  (* Defined. *)

  
  
  Equations(noind) erase (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) : typing_result E.term :=
    erase Γ HΓ t with (is_type_or_proof Σ HΣ Γ HΓ t) :=
    {
      erase Γ HΓ _ (Checked true ; _) := ret (E.tBox);
      erase Γ HΓ _ (TypeError t ; _) := TypeError t ;
      erase Γ HΓ (tRel i) _ := ret (E.tRel i) ;
      erase Γ HΓ (tVar n) _ := ret (E.tVar n) ;
      erase Γ HΓ (tEvar m l) _ := l' <- monad_map (erase Γ HΓ) l;; ret (E.tEvar m l') ;
      erase Γ HΓ (tSort u) _ := ret E.tBox

      ; erase Γ HΓ (tConst kn u) _ := ret (E.tConst kn)
      ; erase Γ HΓ (tInd kn u) _ := ret E.tBox
      ; erase Γ HΓ (tConstruct kn k u) _ := ret (E.tConstruct kn k)
      ; erase Γ HΓ (tProd na b t) _ := ret E.tBox
      ; erase Γ HΓ (tLambda na b t) _ :=
                           t' <- erase (vass na b :: Γ) _ t;;
                              ret (E.tLambda na t')
      ; erase Γ HΓ (tLetIn na b t0 t1) _ :=
                              b' <- erase Γ HΓ b;;
                                 t1' <- erase (vdef na b t0 :: Γ) _ t1;;
                                 ret (E.tLetIn na b' t1')
      ; erase Γ HΓ (tApp f u) _ :=
                     f' <- erase Γ HΓ f;;
                        l' <- erase Γ HΓ u;;
                        ret (E.tApp f' l')
      ; erase Γ HΓ (tCase ip p c brs) _ :=
                             c' <- erase Γ HΓ c;;
                                brs' <- monad_map (T :=typing_result) (fun x => x' <- erase Γ HΓ (snd x);; ret (fst x, x')) brs;;
                                ret (E.tCase ip c' brs')
      ; erase Γ HΓ (tProj p c) _ :=
                      c' <- erase Γ HΓ c;;
                         ret (E.tProj p c')
      ; erase Γ HΓ (tFix mfix n) _ :=
                        mfix' <- erase_mfix (erase) Γ HΓ mfix;;
                              ret (E.tFix mfix' n)
      ; erase Γ HΓ (tCoFix mfix n) _ :=
                          mfix' <- erase_mfix (erase) Γ HΓ mfix;;
                                ret (E.tCoFix mfix' n)
    }.
  Next Obligation.
    destruct w. sq. econstructor; eauto. cbn.
        
    eapply inversion_Lambda in X as (? & ? & ? & ? & ?).
    econstructor; cbn; eauto.
  Qed.
  Next Obligation.
    destruct w. sq. econstructor; eauto. cbn.
    eapply inversion_LetIn in X as (? & ? & ? & ? & ? & ?).
    econstructor; cbn; eauto.
  Qed.
  
  (* Fixpoint erase (Γ : context) (HΓ : ∥wf_local Σ Γ∥) (t : term) {struct t} : typing_result E.term. *)
  (* Proof. *)
  (*   destruct (is_type_or_proof Σ HΣ Γ HΓ t) eqn:E1. *)
  (*   destruct x as [b | ] eqn:E2. *)
  (*   destruct b eqn:E3. *)
  (*   - exact (ret (E.tBox)). *)
  (*   - revert y E1. refine (match t with *)
  (*            | tRel i => fun _ _ => ret (E.tRel i) *)
  (*            | tVar n => fun _ _ =>  ret (E.tVar n) *)
  (*            | tEvar m l => fun _ _ => *)
  (*              l' <- monad_map (erase Γ HΓ) l;; *)
  (*                 ret (E.tEvar m l') *)
  (*            | tSort u => fun _ _ =>  ret E.tBox *)
  (*            | tConst kn u => fun _ _ =>  ret (E.tConst kn) *)
  (*            | tInd kn u => fun _ _ =>  ret E.tBox *)
  (*            | tConstruct kn k u => fun _ _ =>  ret (E.tConstruct kn k) *)
  (*            | tProd na b t => fun _ _ =>  ret E.tBox *)
  (*            | tLambda na b t => fun _ _ => *)
  (*              t' <- erase (vass na b :: Γ) _ t;; *)
  (*                 ret (E.tLambda na t') *)
  (*            | tLetIn na b t0 t1 => fun _ _ => *)
  (*              b' <- erase Γ HΓ b;; *)
  (*                 t1' <- erase (vdef na b t0 :: Γ) _ t1;; *)
  (*                 ret (E.tLetIn na b' t1') *)
  (*            | tApp f u => fun _ _ => *)
  (*              f' <- erase Γ HΓ f;; *)
  (*                 l' <- erase Γ HΓ u;; *)
  (*                 ret (E.tApp f' l') *)
  (*            | tCase ip p c brs => fun _ _ => *)
  (*              c' <- erase Γ HΓ c;; *)
  (*                 brs' <- monad_map (T:=typing_result) (fun x => x' <- erase Γ HΓ (snd x);; ret (fst x, x')) brs;; *)
  (*                 ret (E.tCase ip c' brs') *)
  (*            | tProj p c => fun _ _ => *)
  (*              c' <- erase Γ HΓ c;; *)
  (*                 ret (E.tProj p c') *)
  (*            | tFix mfix n => fun _ _ => *)
  (*                mfix' <- erase_mfix (erase) Γ HΓ mfix;; *)
  (*                ret (E.tFix mfix' n) *)
  (*            | tCoFix mfix n => fun _ _ => *)
  (*                mfix' <- erase_mfix (erase) Γ HΓ mfix;; *)
  (*                ret (E.tCoFix mfix' n) *)
  (*             end). *)
      
  (*     + destruct p as [? []]. sq. clear e. *)
        
  (*       eapply inversion_Lambda in t1 as (? & ? & ? & ? & ?). *)
  (*       econstructor; cbn; eauto. *)
  (*     + destruct p as [? []]. sq. clear e. *)
                
  (*       eapply inversion_LetIn in t2 as (? & ? & ? & ? & ? & ?). *)
  (*       econstructor; cbn; eauto. *)
  (*   - exact (TypeError t0). *)
  (* Defined. *)

End Erase.

Require Import ExtractionCorrectness.

Lemma erases_erase Σ Γ t T (wfΣ : ∥wf Σ∥) (wfΓ : ∥wf_local Σ Γ∥) t' :
  Σ ;;; Γ |- t : T ->
  erase Σ (wfΣ) Γ (wfΓ) t = Checked t' ->                
  erases Σ Γ t t'.
Proof.
  Hint Constructors typing erases.
  intros. sq.
  (* pose proof (typing_wf_local X0). *)

    
  pose (wfΣ' := sq t0).
  pose (wfΓ' := sq a).
  change (erase Σ wfΣ' Γ wfΓ' t = Checked t') in H.

  revert H.
  generalize wfΣ' wfΓ'. clear wfΣ' wfΓ'.
  
  revert Σ t0 Γ a t T X t'.
  eapply (typing_ind_env (fun Σ Γ t T =>   forall (t' : E.term) (wfΣ' : ∥ wf Σ ∥) (wfΓ' : ∥ wf_local Σ Γ ∥),
  erase Σ wfΣ' Γ wfΓ' t = Checked t' -> Σ;;; Γ |- t ⇝ℇ t'
         )); intros.

  all:eauto.
  all: simp erase in *.
  all: unfold erase_clause_1 in *.

  all: cbn in *; repeat (destruct ?;  repeat match goal with
                                          [ H : Checked _ = Checked _ |- _ ] => inv H
                                        | [ H : TypeError _ = Checked _ |- _ ] => inv H
                                        | [ H : _ × PCUICSafeLemmata.welltyped _ _ _ |- _ ] => destruct H as [? []]
                                        end; eauto).
    
  - repeat econstructor; eauto.
  - econstructor. econstructor. clear E.
    eapply inversion_Prod in t0 as (? & ? & ? & ? & ?).
    split. eauto. left. econstructor.
  - econstructor. eauto. econstructor. clear E.
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
    unfold erase_mfix in *.
    pose proof (Prelim.monad_map_All2 _ _ _ mfix a0 E2).
    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.

    intros. destruct X1. cbn in *. repeat destruct ?; inv e. 
    cbn. repeat split; eauto. 
    eapply p. eauto. 
  - econstructor.
    unfold erase_mfix in *.
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

Definition erase_constant_body Σ wfΣ (cb : constant_body) : typing_result E.constant_body :=
  ty <- erase Σ wfΣ [] wf_local_nil cb.(cst_type) ;;
  body <- optM cb.(cst_body) (fun b => erase Σ wfΣ [] wf_local_nil b);;
  ret {| E.cst_body := body; |}.

Definition lift_opt_typing {A} (a : option A) (e : type_error) : typing_result A :=
  match a with
  | Some x => ret x
  | None => raise e
  end.

Definition erase_one_inductive_body Σ wfΣ npars arities Har
           (oib : one_inductive_body) : typing_result E.one_inductive_body :=
  decty <- lift_opt_typing (decompose_prod_n_assum [] npars oib.(ind_type))
        (NotAnInductive oib.(ind_type)) ;;
  let '(params, arity) := decty in
  type <- erase Σ wfΣ [] wf_local_nil oib.(ind_type) ;;
  ctors <- monad_map (fun '(x, y, z) => y' <- erase Σ wfΣ arities Har y;; ret (x, y', z)) oib.(ind_ctors);;
  let projctx := arities ,,, params ,, vass nAnon oib.(ind_type) in
  projs <- monad_map (fun '(x, y) => y' <- erase Σ wfΣ [] wf_local_nil y;; ret (x, y')) oib.(ind_projs);;
  ret {| E.ind_name := oib.(ind_name);
         E.ind_kelim := oib.(ind_kelim);
         E.ind_ctors := ctors;
         E.ind_projs := projs |}.

Program Definition erase_mutual_inductive_body Σ wfΣ
           (mib : mutual_inductive_body) (Hm :   ∥ wf_local Σ (arities_context (ind_bodies mib)) ∥)
: typing_result E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  bodies <- monad_map (erase_one_inductive_body Σ wfΣ mib.(ind_npars) arities _) bds ;;
  ret {| E.ind_npars := mib.(ind_npars);
         E.ind_bodies := bodies; |}.

Program Fixpoint erase_global_decls univs Σ : ∥ wf (Σ, univs) ∥ -> typing_result E.global_declarations := fun wfΣ =>
  match Σ with
  | [] => ret []
  | ConstantDecl kn cb :: Σ => 
    cb' <- erase_constant_body (Σ, univs) _ cb;;
    Σ' <- erase_global_decls univs Σ _;;
    ret (E.ConstantDecl kn cb' :: Σ')
  | InductiveDecl kn mib :: Σ => 
    mib' <- erase_mutual_inductive_body (Σ, univs) _ mib _ ;;
    Σ' <- erase_global_decls univs Σ _;;
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
  sq. eapply wf_extends; eauto. eexists [_]; reflexivity.
Qed.
Next Obligation.
  sq. inv X. cbn in *.
  eapply PCUICSubstitution.wf_arities_context'; eauto.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.

Program Definition erase_global Σ : ∥wf Σ∥ -> _:=
  match Σ with (Σ, univs) => fun wfΣ  =>
  Σ' <- erase_global_decls univs Σ wfΣ ;;
  ret Σ' end.

           
Lemma constructors_typed:
  forall (Σ : list global_decl) (univs : constraints) (k : kername)
    (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term) 
    (i0 : ident) (n0 : nat),
    In (i0, t1, n0) (ind_ctors x) ->
    on_inductive (fun Σ0 : global_context => lift_typing typing Σ0) (Σ, univs) k m ->
    ∑ T, (Σ, univs);;; arities_context (ind_bodies m) |- t1 : T.
Proof.
  intros Σ univs k m x t1 i0 n0 H2 X0.
Admitted.

Lemma proj_typed:
  forall (Σ : list global_decl) (univs : constraints) (k : kername)
    (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term) 
    (i0 : ident) (H2 : In (i0, t1) (ind_projs x))
    (X0 : on_inductive (fun Σ0 : global_context => lift_typing typing Σ0) (Σ, univs) k m),
    ∑ T, (Σ, univs);;; [] |- t1 : T.
Proof.
  
Admitted.

Lemma erase_global_correct Σ (wfΣ : ∥ wf Σ∥) Σ' :
  erase_global Σ wfΣ = Checked Σ' ->
  erases_global Σ Σ'.
Proof.
  destruct Σ as (Σ, univs).
  induction Σ in wfΣ, Σ' |- *; cbn; intros; sq.
  - inv H. econstructor.
  - repeat destruct ?; try congruence.
    + inv H. inv E. inv E1. econstructor.
      * unfold erases_constant_body.
        unfold optM in E4. destruct ?; try congruence.
        -- cbn. cbn in *.
           destruct ( erase (Σ, univs)
           (erase_global_decls_obligation_1 univs (ConstantDecl k c :: Σ) 
              (sq t) k c Σ eq_refl) [] wf_local_nil t0) eqn:E5;
             rewrite E5 in E4; inv E4.
           eapply erases_erase. 2:eauto.
           instantiate (1 := cst_type c).
           clear - t E. inv t.
           cbn in *. unfold on_constant_decl in X0.
           rewrite E in X0. cbn in X0. eassumption.           
        -- cbn. inv E4. econstructor.
      * eapply IHΣ. unfold erase_global. rewrite E2. reflexivity.
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
           eapply All2_impl_In. eassumption.
           intros. destruct x0, p, y, p. cbn in *.
           destruct ?; try congruence.
           inv H4. split; eauto.

           pose (t' := t). inv t'. cbn in *.
           edestruct constructors_typed; eauto.
           eapply erases_erase. 2:eauto. eauto.
        -- eapply All2_Forall.
           eapply All2_impl_In. eassumption.
           intros. cbn in H2. destruct x0, y.
           destruct ?; try congruence;
             inv H4. split; eauto.

           pose (t' := t). inv t'. cbn in *.
           edestruct proj_typed; eauto.
           
           eapply erases_erase.
           2:{ eauto. } eauto.
  * eapply IHΣ. unfold erase_global. rewrite E2. reflexivity.
Qed.
