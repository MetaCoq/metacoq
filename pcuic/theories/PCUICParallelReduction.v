(* Distributed under the terms of the MIT license. *)
Require Import RelationClasses CRelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICUtils PCUICAst PCUICAstUtils PCUICDepth PCUICCases
     PCUICLiftSubst PCUICUnivSubst PCUICReduction PCUICTyping
     PCUICSigmaCalculus PCUICWeakeningEnv PCUICInduction
     PCUICRename PCUICInst PCUICOnFreeVars
     PCUICContextRelation PCUICWeakening PCUICSubstitution.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Local Set Keyed Unification.

Ltac simplify_IH_hyps := 
  repeat match goal with 
      [ H : _ |- _ ] => eqns_specialize_eqs H
  end.

(** All2 lemmas *)

Definition All2_prop_eq Γ Γ' {A B} (f : A -> term) (g : A -> B) (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (on_Trel_eq (rel Γ Γ') f g).

Definition All2_prop Γ (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (rel Γ).

(* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

Lemma All2_All2_prop {P Q : context -> context -> term -> term -> Type} {par par'} {l l' : list term} :
  All2 (P par par') l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2 (Q par par') l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *.
  apply aux; apply r. apply IHAll2.
Defined.

Lemma All2_branch_prop {P Q : context -> context -> branch term -> branch term -> Type} 
  {par par'} {l l' : list (branch term)} :
  All2 (P par par') l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2 (Q par par') l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *.
  apply aux; apply r. apply IHAll2.
Defined.

Lemma All2_All2_prop_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par'}
      {f : A -> term} {g : A -> B} {l l' : list A} :
  All2 (on_Trel_eq (P par par') f g) l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2_prop_eq par par' f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *.
  split. apply aux; apply r. apply r. apply IHAll2.
Defined.

Definition All2_prop2_eq Γ Γ' Γ2 Γ2' {A B} (f g : A -> term) (h : A -> B)
           (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ Γ') f x y * on_Trel_eq (rel Γ2 Γ2') g h x y)%type.

Definition All2_prop2 Γ Γ' {A} (f g : A -> term)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel (rel Γ') g x y)%type.

Lemma All2_All2_prop2_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par' par2 par2'}
      {f g : A -> term} {h : A -> B} {l l' : list A} :
  All2_prop2_eq par par' par2 par2' f g h P l l' ->
  (forall par par' x y, P par par' x y -> Q par par' x y) ->
  All2_prop2_eq par par' par2 par2' f g h Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *. split.
  apply aux. destruct r. apply p. split. apply aux. apply r. apply r. apply IHAll2.
Defined.

(* Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'} *)
(*       {f g : A -> term} {l l' : list A} : *)
(*   All2_prop2 par par' f g P l l' -> *)
(*   (forall par x y, P par x y -> Q par x y) -> *)
(*   All2_prop2 par par' f g Q l l'. *)
(* Proof. *)
(*   intros H aux. *)
(*   induction H; constructor. unfold on_Trel in *. split. *)
(*   apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2. *)
(* Defined. *)

Section All2_fold.

  Definition on_decls_over (P : context -> context -> term -> term -> Type) Γ Γ' :=
    fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ').

  Definition All2_fold_over P Γ Γ' := All2_fold (on_decls (on_decls_over P Γ Γ')).

  (** Do not change this definition as it is used in a raw fixpoint so should preserve 
    the guard condition. *)
  Lemma All2_fold_impl {P Q : context -> context -> term -> term -> Type} {par par'} :
    on_contexts P par par' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    on_contexts Q par par'.
  Proof.
    intros H aux.
    induction H; constructor; tas.
    destruct p; constructor.
    apply aux, p. apply aux, p. apply aux, p0.
  Defined.

  Lemma All2_fold_impl_ind {P Q : context -> context -> term -> term -> Type} {par par'} :
    on_contexts P par par' ->
    (forall par par' x y,
      on_contexts Q par par' ->
      P par par' x y -> Q par par' x y) ->
    on_contexts Q par par'.
  Proof.
    intros H aux.
    induction H; constructor; auto. eapply All_decls_impl; tea. eauto.
  Qed.

  Lemma All2_fold_app :
    forall P (Γ Γ' Γl Γr : context),
      on_contexts P Γ Γl ->
      on_contexts (on_decls_over P Γ Γl) Γ' Γr ->
      on_contexts P (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto. simpl. constructor; auto.
  Qed.

  Lemma All2_fold_length {P l l'} : All2_fold P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto; lia. Qed.

  Global Instance All2_fold_has_length P l l' : 
    HasLen (All2_fold P l l') #|l| #|l'|.
  Proof. red. apply All2_fold_length. Qed.
  Hint Extern 20 (#|?X| = #|?Y|) =>
    match goal with
      [ H : All2_fold _ ?X ?Y |- _ ] => apply (All2_fold_length H)
    | [ H : All2_fold _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
    | [ H : All2_fold_over _ _ _ ?X ?Y |- _ ] => apply (All2_fold_length H)
    | [ H : All2_fold_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
    end : pcuic.

  Ltac pcuic := eauto with pcuic.

  Derive Signature for All2_fold.

  Lemma All2_fold_app':
    forall P (Γ Γ' Γ'' : context),
      on_contexts P (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) /\ #|Γ'| = #|Γr| /\ #|Γ| = #|Γl|.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. eapply (All2_fold_length X).
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,, d'). simpl. intuition eauto. lia.
  Qed.

  Lemma All2_fold_app_ex:
    forall P (Γ Γ' Γ'' : context),
      on_contexts P (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) *
      All2_fold
        (on_decls P)
        Γ Γl * All2_fold (on_decls (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. constructor.
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor; auto.
  Qed.

  Lemma All2_fold_app_inv :
    forall P (Γ Γ' Γl Γr : context),
      on_contexts P (Γ ,,, Γ') (Γl ,,, Γr) ->
      #|Γ| = #|Γl| ->
      on_contexts P Γ Γl *
      on_contexts (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ')) Γ' Γr.
  Proof.
    intros *.
    intros. pose proof X as X'.
    apply All2_fold_app' in X as [Γl' [Γr' ?]].
    destruct a as [? [? ?]].
    apply All2_fold_app_ex in X' as [Γl2' [Γr2' [[? ?] ?]]].
    subst; rename_all_hyps.
    unfold app_context in heq_app_context.
    eapply app_inj_length_r in heq_app_context; try lia. destruct heq_app_context. subst.
    unfold app_context in heq_app_context0.
    eapply app_inj_length_r in heq_app_context0; try lia. intuition subst; auto.
    pose proof (All2_fold_length a). lia.
  Qed.
  
  Lemma nth_error_pred1_ctx {P} {Γ Δ} i body' :
    on_contexts P Γ Δ ->
    option_map decl_body (nth_error Δ i) = Some (Some body') ->
    { body & (option_map decl_body (nth_error Γ i) = Some (Some body)) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body'.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. depelim p => //.
    noconf heq_option_map. exists b. intuition eauto.
    specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma nth_error_pred1_ctx_l {P} {Γ Δ} i body :
    on_contexts P Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    depelim p => //.
    noconf heq_option_map. exists b'. intuition eauto.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma All2_fold_over_app P {Γ0 Δ Γ'' Δ''} :
    on_contexts P Γ0 Δ ->
    All2_fold_over P Γ0 Δ Γ'' Δ'' ->
    on_contexts P (Γ0 ,,, Γ'') (Δ ,,, Δ'').
  Proof.
    intros. induction X0; pcuic; constructor; pcuic.
  Qed.

  Lemma All2_fold_app_inv_left {P Γ Γ' Δ Δ'} :
    on_contexts P (Γ ,,, Δ) (Γ' ,,, Δ') -> #|Γ| = #|Γ'| ->
    on_contexts P Γ Γ'.
  Proof.
    intros. eapply All2_fold_app_inv in X; intuition auto.
  Qed.

  Lemma All2_fold_mapi P Γ Δ f g : 
    All2_fold (on_decls
      (fun Γ Γ' t t' => 
        P (mapi_context f Γ) (mapi_context g Γ')  (f #|Γ| t) (g #|Γ'| t'))) Γ Δ ->
    on_contexts P (mapi_context f Γ) (mapi_context g Δ).
  Proof.
    induction 1; rewrite /=; constructor; auto.
    depelim p; constructor; auto.
  Qed.

  Lemma All2_fold_mapi_inv P Γ Δ f g : 
    on_contexts P (mapi_context f Γ) (mapi_context g Δ) ->
    on_contexts (fun Γ Γ' t t' => 
        P (mapi_context f Γ) (mapi_context g Γ') (f #|Γ| t) (g #|Γ'| t')) Γ Δ.
  Proof.
    induction Γ in Δ |- *; destruct Δ; intros h; depelim h.
    - constructor.
    - constructor; auto.
      destruct a as [na [b|] ty], c as [na' [b'|] ty']; cbn in * => //;
      depelim a0; constructor; auto. 
  Qed.

End All2_fold.

Section ParallelReduction.
  Context (Σ : global_env).

  Definition pred_atom t :=
    match t with
    | tVar _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ 
    | tPrim _ => true
    | _ => false
    end.

  Reserved Notation "'pred1_ctx'" (at level 8).
  Reserved Notation "'pred1_ctx_over' Γ Γ'" (at level 200, Γ, Γ' at level 9).

  Inductive pred1 (Γ Γ' : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t0 t1 b0 b1 a0 a1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> pred1 Γ Γ' a0 a1 ->
      pred1 Γ Γ' (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 Γ Γ' d0 d1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def_unfold i body :
      pred1_ctx Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1 Γ Γ' (tRel i) (lift0 (S i) body)

  | pred_rel_refl i :
      pred1_ctx Γ Γ' ->
      pred1 Γ Γ' (tRel i) (tRel i)

  (** Case *)
  | pred_iota ci c u args0 args1 p0 params' brs0 brs1 br :
      pred1_ctx Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error brs1 c = Some br -> 
      #|skipn (ci_npar ci) args1| = context_assumptions br.(bcontext) ->
      All2 (pred1 Γ Γ') p0.(pparams) params' ->
      All2 (fun br br' => 
        pred1_ctx_over Γ Γ' (inst_case_branch_context p0 br) 
          (inst_case_context params' p0.(puinst) br'.(bcontext)) ×
        on_Trel_eq (pred1 (Γ ,,, inst_case_branch_context p0 br) 
          (Γ' ,,, inst_case_context params' (puinst p0) (bcontext br))) bbody bcontext br br') brs0 brs1 ->
          pred1 Γ Γ' (tCase ci p0 (mkApps (tConstruct ci.(ci_ind) c u) args0) brs0)
            (iota_red ci.(ci_npar) p0 args1 br)

  (** Fix unfolding, with guard *)
  | pred_fix mfix0 mfix1 idx args0 args1 narg fn :
      pred1_ctx Γ Γ' ->
      pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_fix mfix1 idx = Some (narg, fn) ->
      is_constructor narg args0 = true ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ci p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1 :
      pred1_ctx Γ Γ' ->
      pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      All2 (pred1 Γ Γ') p0.(pparams) p1.(pparams) ->
      p0.(puinst) = p1.(puinst) ->
      p0.(pcontext) = p1.(pcontext) ->
      pred1_ctx_over Γ Γ' (PCUICCases.inst_case_predicate_context p0) (PCUICCases.inst_case_predicate_context p1) ->
      pred1 (Γ ,,, PCUICCases.inst_case_predicate_context p0)
        (Γ' ,,, PCUICCases.inst_case_predicate_context p1) p0.(preturn) p1.(preturn) ->
      All2 (fun br br' => 
        pred1_ctx_over Γ Γ' (inst_case_branch_context p0 br) (inst_case_branch_context p1 br') ×
        on_Trel_eq
          (pred1 (Γ ,,, inst_case_branch_context p0 br) (Γ' ,,, inst_case_branch_context p1 br'))
          bbody bcontext br br') brs0 brs1 ->
      pred1 Γ Γ' (tCase ci p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
            (tCase ci p1 (mkApps fn args1) brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix0 mfix1 idx args0 args1 narg fn :
      pred1_ctx Γ Γ' ->
      pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0))
            (tProj p (mkApps fn args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      pred1_ctx Γ Γ' ->
      decl.(cst_body) = Some body ->
      pred1 Γ Γ' (tConst c u) (subst_instance u body)

  | pred_const c u :
      pred1_ctx Γ Γ' ->
      pred1 Γ Γ' (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg u args0 args1 arg1 :
      pred1_ctx Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1 Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ Γ' M M' -> pred1 (Γ ,, vass na M) (Γ' ,, vass na M') N N' ->
                            pred1 Γ Γ' (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ Γ' M0 M1 ->
      pred1 Γ Γ' N0 N1 ->
      pred1 Γ Γ' (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' d0 d1 -> pred1 Γ Γ' t0 t1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ci p0 p1 c0 c1 brs0 brs1 :
      pred1_ctx Γ Γ' ->
      All2 (pred1 Γ Γ') p0.(pparams) p1.(pparams) ->
      p0.(puinst) = p1.(puinst) ->
      p0.(pcontext) = p1.(pcontext) ->
      pred1_ctx_over Γ Γ' (PCUICCases.inst_case_predicate_context p0) (PCUICCases.inst_case_predicate_context p1) ->
      pred1 (Γ ,,, inst_case_context p0.(pparams) p0.(puinst) p0.(pcontext)) 
        (Γ' ,,, inst_case_context p1.(pparams) p1.(puinst) p1.(pcontext)) p0.(preturn) p1.(preturn) ->
      All2 (fun br br' => 
        pred1_ctx_over Γ Γ' (inst_case_branch_context p0 br) (inst_case_branch_context p1 br') ×
        on_Trel_eq
          (pred1 (Γ ,,, inst_case_branch_context p0 br) (Γ' ,,, inst_case_branch_context p1 br'))
          bbody bcontext br br') brs0 brs1 ->
      pred1 Γ Γ' c0 c1 ->
      pred1 Γ Γ' (tCase ci p0 c0 brs0) (tCase ci p1 c1 brs1)

  | pred_proj_congr p c c' :
      pred1 Γ Γ' c c' -> pred1 Γ Γ' (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      pred1_ctx Γ Γ' ->
      pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      pred1_ctx Γ Γ' ->
      pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ Γ' M0 M1 -> pred1 (Γ ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
                               pred1 Γ Γ' (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      pred1_ctx Γ Γ' ->
      All2 (pred1 Γ Γ') l l' -> pred1 Γ Γ' (tEvar ev l) (tEvar ev l')

  | pred_atom_refl t :
      pred1_ctx Γ Γ' ->
      pred_atom t -> pred1 Γ Γ' t t
  where "'pred1_ctx'" := (All2_fold (on_decls pred1))
  and "'pred1_ctx_over' Γ Γ'" := (All2_fold (on_decls (on_decls_over pred1 Γ Γ'))).

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | nat -> bool => fresh "P"
    | nat -> nat => fresh "f"
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Definition extendP {P Q: context -> context -> term -> term -> Type}
             (aux : forall Γ Γ' t t', P Γ Γ' t t' -> Q Γ Γ' t t') :
    (forall Γ Γ' t t', P Γ Γ' t t' -> (P Γ Γ' t t' * Q Γ Γ' t t')).
  Proof.
    intros. split. apply X. apply aux. apply X.
  Defined.

  Definition extend_over {P Q: context -> context -> term -> term -> Type}
             (aux : forall Γ Γ' t t', P Γ Γ' t t' -> Q Γ Γ' t t') Γ Γ' :
    (forall Δ Δ' t t', P (Γ ,,, Δ) (Γ' ,,, Δ') t t' -> Q (Γ ,,, Δ) (Γ' ,,, Δ') t t').
  Proof.
    intros. apply aux. apply X.
  Defined.

  Lemma pred1_ind_all_ctx :
    forall (P : forall (Γ Γ' : context) (t t0 : term), Type)
           (Pctx : forall (Γ Γ' : context), Type)
           (Pctxover : forall (Γ Γ' Δ Δ' : context), Type),
      let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall Γ Γ', pred1_ctx Γ Γ' -> on_contexts P Γ Γ' -> Pctx Γ Γ') ->
      (forall Γ Γ' Δ Δ', pred1_ctx Γ Γ' -> on_contexts P Γ Γ' ->
        Pctx Γ Γ' ->
        pred1_ctx_over Γ Γ' Δ Δ' ->
        All2_fold_over P Γ Γ' Δ Δ' ->
        Pctxover Γ Γ' Δ Δ') ->
      (forall (Γ Γ' : context) (na : aname) (t0 t1 b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : aname) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall Γ Γ' ci c u args0 args1 p0 pparams1 brs0 brs1 br,
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2 (P' Γ Γ') p0.(pparams) pparams1 ->
          All2 (fun br br' =>
            Pctxover Γ Γ' (inst_case_branch_context p0 br) 
              (inst_case_context pparams1 p0.(puinst) br'.(bcontext)) ×
            on_Trel_eq 
              (P' (Γ ,,, inst_case_branch_context p0 br)
                  (Γ' ,,, inst_case_context pparams1 p0.(puinst) br'.(bcontext)))
              bbody bcontext br br') brs0 brs1 ->
          nth_error brs1 c = Some br -> 
          #|skipn (ci_npar ci) args1| = context_assumptions br.(bcontext) ->
          P Γ Γ' (tCase ci p0 (mkApps (tConstruct ci.(ci_ind) c u) args0) brs0)
                (iota_red ci.(ci_npar) p0 args1 br)) ->

      (forall (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          Pctxover Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_fix mfix1 idx = Some (narg, fn) ->
          is_constructor narg args0 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)) ->

      (forall (Γ Γ' : context) ci p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1,
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          Pctxover Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          All2 (P' Γ Γ') p0.(pparams) p1.(pparams) ->
          p0.(puinst) = p1.(puinst) ->
          p0.(pcontext) = p1.(pcontext) ->
          Pctxover Γ Γ' (PCUICCases.inst_case_predicate_context p0) (PCUICCases.inst_case_predicate_context p1) ->
          pred1 (Γ ,,, inst_case_context p0.(pparams) p0.(puinst) p0.(pcontext))
            (Γ' ,,, inst_case_context p1.(pparams) p1.(puinst) p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          P (Γ ,,, inst_case_context p0.(pparams) p0.(puinst) p0.(pcontext)) 
            (Γ' ,,, inst_case_context p1.(pparams) p1.(puinst) p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          All2 (fun br br' => 
            Pctxover Γ Γ' (inst_case_branch_context p0 br) (inst_case_branch_context p1 br') ×
              on_Trel_eq 
                (P' (Γ ,,, inst_case_branch_context p0 br) (Γ' ,,, inst_case_branch_context p1 br'))
                  bbody bcontext br br') brs0 brs1 ->
          P Γ Γ' (tCase ci p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
                (tCase ci p1 (mkApps fn args1) brs1)) ->

      (forall (Γ Γ' : context) (p : projection) (mfix0 mfix1 : mfixpoint term)
         (idx : nat) (args0 args1 : list term)
         (narg : nat) (fn : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          Pctxover Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0)) (tProj p (mkApps fn args1))) ->
      (forall (Γ Γ' : context) c (decl : constant_body) (body : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : Instance.t, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance u body)) ->
      (forall (Γ Γ' : context) c (u : Instance.t),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (u : Instance.t)
              (args0 args1 : list term) (arg1 : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (pred1 Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : aname) (M M' N N' : term),
          pred1 Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 ->
          P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : aname) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1 Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      
      (forall (Γ Γ' : context) ci p0 p1 c0 c1 brs0 brs1,
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') p0.(pparams) p1.(pparams) ->
          p0.(puinst) = p1.(puinst) ->
          p0.(pcontext) = p1.(pcontext) ->
          Pctxover Γ Γ' (PCUICCases.inst_case_predicate_context p0) (PCUICCases.inst_case_predicate_context p1) ->
          pred1 (Γ ,,, inst_case_context p0.(pparams) p0.(puinst) p0.(pcontext)) 
            (Γ' ,,, inst_case_context p1.(pparams) p1.(puinst) p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          P (Γ ,,, inst_case_context p0.(pparams) p0.(puinst) p0.(pcontext)) 
            (Γ' ,,, inst_case_context p1.(pparams) p1.(puinst) p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          All2 (fun br br' => 
            Pctxover Γ Γ' (inst_case_branch_context p0 br) (inst_case_branch_context p1 br') ×
            on_Trel_eq 
              (P' (Γ ,,, inst_case_branch_context p0 br) (Γ' ,,, inst_case_branch_context p1 br'))
                bbody bcontext br br') brs0 brs1 ->
          pred1 Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 ->
          P Γ Γ' (tCase ci p0 c0 brs0) (tCase ci p1 c1 brs1)) ->

      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          Pctxover Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred1_ctx_over Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          Pctxover Γ Γ' (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : aname) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      (forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0) ×
      (forall Γ Γ' Δ Δ', pred1_ctx Γ Γ' -> pred1_ctx_over Γ Γ' Δ Δ' -> Pctxover Γ Γ' Δ Δ').
  Proof using Σ.
    intros P Pctx Pctxover P' Hctx Hctxover. intros.
    assert (forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0).
    intros.
    rename X20 into pr. revert Γ Γ' t t0 pr.
    fix aux 5. intros Γ Γ' t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ _ (tRel _) _ => idtac
                | |- P _ _ (tConst _ _) _ => idtac
                | |- P _ _ (tCase _ _ ?c _) (tCase _ _ ?c _) => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. apply X1; auto.
      clear X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19.
      apply Hctx.
      apply (All2_fold_impl a). intros. eapply X1.
      apply (All2_fold_impl a). intros. eapply (aux _ _ _ _ X1).
    - simpl. apply X2; auto.
      apply Hctx, (All2_fold_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - apply Hctx, (All2_fold_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop a1 (extendP aux Γ Γ')).
    - eapply (All2_branch_prop 
        (P:=fun Γ Γ' br br' =>
        (pred1_ctx_over Γ Γ') (inst_case_branch_context p0 br)
          (inst_case_context params' (puinst p0) (bcontext br')) *
        (pred1 (Γ,,, inst_case_branch_context p0 br)
           (Γ',,, inst_case_context params' (puinst p0) (bcontext br))
           (bbody br) (bbody br') × bcontext br = bcontext br'))
        (Q:=fun Γ Γ' br0 br' => 
        Pctxover Γ Γ' (inst_case_branch_context p0 br0)
     (inst_case_context params' (puinst p0) (bcontext br')) *
   (P' (Γ,,, inst_case_branch_context p0 br0)
      (Γ',,, inst_case_context params' (puinst p0) (bcontext br'))
      (bbody br0) (bbody br') × bcontext br0 = bcontext br')) a2).
      intros x y [? []]. split; [|split]; auto.
      * apply Hctxover => //. 
        apply (All2_fold_impl a aux).
        apply (Hctx _ _ a), (All2_fold_impl a aux).
        apply (All2_fold_impl a3 (extend_over aux Γ Γ')).
      * apply (extendP aux _ _). rewrite -e1. exact p.
    - eapply X4; eauto.
      * apply (Hctx _ _ a), (All2_fold_impl a aux).
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
          (Hctx _ _ a (All2_fold_impl a aux)) a0 (All2_fold_impl a0 (extend_over aux Γ Γ'))).
      * eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      * eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X5; eauto.
      * apply Hctx, (All2_fold_impl a) => //.
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
        (Hctx _ _ a (All2_fold_impl a aux)) a0 (All2_fold_impl a0 (extend_over aux Γ Γ'))).
      * eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      * eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
      * eapply (All2_All2_prop (P:=pred1) (Q:=P') a3 (extendP aux Γ Γ')).
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
        (Hctx _ _ a (All2_fold_impl a aux)) 
        a4 (All2_fold_impl a4 (extend_over aux Γ Γ'))).
      * eapply (All2_branch_prop
          (P:=fun Γ Γ' br br' =>
          (pred1_ctx_over Γ Γ') (inst_case_branch_context p0 br)
            (inst_case_branch_context p1 br') *
          (pred1 (Γ,,, inst_case_branch_context p0 br)
            (Γ',,, inst_case_branch_context p1 br')
            (bbody br) (bbody br') × bcontext br = bcontext br'))
          (Q:=fun Γ Γ' br0 br' => 
          Pctxover Γ Γ' (inst_case_branch_context p0 br0)
          (inst_case_branch_context p1 br') *
        (P' (Γ,,, inst_case_branch_context p0 br0)
            (Γ',,, inst_case_branch_context p1 br')
            (bbody br0) (bbody br') × bcontext br0 = bcontext br')) a5).
        intros x y [? []]. 
        split; auto. 2:split => //.
        + apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
            (Hctx _ _ a (All2_fold_impl a aux)) a6 (All2_fold_impl a6 (extend_over aux Γ Γ'))).
        + apply (extendP aux _ _). exact p.
    - eapply X6; eauto.
      * apply (Hctx _ _ a), (All2_fold_impl a aux).
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
          (Hctx _ _ a (All2_fold_impl a aux)) a0 (All2_fold_impl a0 (extend_over aux Γ Γ'))).
      * eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      * eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X7; eauto.
      apply (Hctx _ _ a), (All2_fold_impl a aux).
    - eapply X8; eauto.
      apply (Hctx _ _ a), (All2_fold_impl a aux).
    - apply (Hctx _ _ a), (All2_fold_impl a aux).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P) a0). intros. apply (aux _ _ _ _ X20).
    - apply (Hctx _ _ a), (All2_fold_impl a aux).
    - apply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux _ _)).
    - apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
        (Hctx _ _ a (All2_fold_impl a aux)) a1 (All2_fold_impl a1 (extend_over aux Γ Γ'))).
    - eapply (All2_branch_prop
        (P:=fun Γ Γ' br br' =>
        (pred1_ctx_over Γ Γ') (inst_case_branch_context p0 br)
          (inst_case_branch_context p1 br') *
        (pred1 (Γ,,, inst_case_branch_context p0 br)
          (Γ',,, inst_case_branch_context p1 br')
          (bbody br) (bbody br') × bcontext br = bcontext br'))
        (Q:=fun Γ Γ' br0 br' => 
        Pctxover Γ Γ' (inst_case_branch_context p0 br0)
        (inst_case_branch_context p1 br') *
      (P' (Γ,,, inst_case_branch_context p0 br0)
          (Γ',,, inst_case_branch_context p1 br')
          (bbody br0) (bbody br') × bcontext br0 = bcontext br')) a2).
      intros x y [? []]. 
      split; auto. 2:split => //.
      + apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
          (Hctx _ _ a (All2_fold_impl a aux)) a3 (All2_fold_impl a3 (extend_over aux Γ Γ'))).
      + apply (extendP aux _ _). exact p.
    - eapply X15 => //.
      * eapply (Hctx _ _ a), (All2_fold_impl a aux).
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
         (Hctx _ _ a (All2_fold_impl a aux)) a0 (All2_fold_impl a0 (extend_over aux Γ Γ'))).
      * eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply X16; tas.
      * eapply (Hctx _ _ a), (All2_fold_impl a aux).
      * apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
        (Hctx _ _ a (All2_fold_impl a aux)) a0 (All2_fold_impl a0 (extend_over aux Γ Γ'))).
      * eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply (Hctx _ _ a), (All2_fold_impl a aux).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (Hctx _ _ a), (All2_fold_impl a aux).
    - split => //.
      intros.
      eapply Hctxover; eauto.
      { eapply (All2_fold_impl X21 X20). }
      eapply Hctx; eauto.
      { eapply (All2_fold_impl X21 X20). }
      eapply (All2_fold_impl X22 (extend_over X20 Γ Γ')).
  Defined.

  Lemma pred1_pred1_ctx {Γ Δ t u} : pred1 Γ Δ t u -> pred1_ctx Γ Δ.
  Proof.
    intros H; revert Γ Δ t u H.
    refine (fst (pred1_ind_all_ctx _ (fun Γ Γ' => pred1_ctx Γ Γ')
      (fun Γ Γ' Δ Δ' => True)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].
  Qed.

  Lemma onctx_rel_pred1_refl Γ Δ : 
    forall Γ', 
    pred1_ctx Γ Γ' ->
    onctx_rel
    (fun (Γ : context) (t : term) =>
      forall Γ' : context, pred1_ctx Γ Γ' -> pred1 Γ Γ' t t) Γ Δ ->
    pred1_ctx_over Γ Γ' Δ Δ.
  Proof.
    intros Γ' pred onc.
    induction onc; simpl; constructor; auto.
    constructor.
    red in t0 |- *. eapply t0.
    apply All2_fold_app => //.
    destruct t1.
    constructor; red; [eapply p|eapply p0];
    apply All2_fold_app => //.
  Qed.

  Lemma onctx_rel_pred1_refl' Γ Δ : 
    forall Γ', 
    pred1_ctx Γ Γ' ->
    onctx_rel
    (fun (Γ : context) (t : term) =>
      forall Γ' : context, pred1_ctx Γ Γ' -> pred1 Γ Γ' t t) Γ Δ ->
    pred1_ctx_over Γ Γ' Δ Δ.
  Proof.
    intros Γ' pred onc.
    induction onc; simpl; constructor; auto.
    constructor.
    red in t0 |- *. eapply t0.
    apply All2_fold_app => //.
    destruct t1.
    constructor; red; [eapply p|eapply p0];
    apply All2_fold_app => //.
  Qed.

  Hint Constructors All_decls : pcuic.

  Lemma pred1_refl_gen Γ Γ' t : pred1_ctx Γ Γ' -> pred1 Γ Γ' t t.
  Proof.
    revert Γ'.
    revert Γ t.
    apply: PCUICDepth.term_forall_ctx_list_ind;
    intros;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [try red in X; constructor; unfold All2_prop2_eq, All2_prop2, on_Trel in *; solve_all];
      intros.
    - constructor; eauto. eapply X0.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply X0.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply X1.
      constructor; try red; eauto with pcuic.
    - red in X, X1; econstructor; solve_all.
      * eapply onctx_rel_pred1_refl => //.
      * eapply b0.
        eapply All2_fold_app => //.
        eapply onctx_rel_pred1_refl => //.
      * eapply All_All2; tea; solve_all.
        + eapply onctx_rel_pred1_refl => //. 
        + eapply b.
          now eapply All2_fold_app => //; eapply onctx_rel_pred1_refl.
    - constructor; auto.
      apply onctx_rel_pred1_refl => //.
      unfold All2_prop_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros. solve_all.
      eapply a; tas.
      eapply b. eapply All2_fold_app; auto.
      now eapply onctx_rel_pred1_refl.
    - constructor; auto.
      apply onctx_rel_pred1_refl => //.
      unfold All2_prop_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros. solve_all.
      eapply a; tas.
      eapply b. eapply All2_fold_app; auto.
      now eapply onctx_rel_pred1_refl.
  Qed.

  Lemma pred1_ctx_refl Γ : pred1_ctx Γ Γ.
  Proof.
    induction Γ. constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic;
    constructor; now apply pred1_refl_gen.
  Qed.
  Hint Resolve pred1_ctx_refl : pcuic.

  Lemma pred1_refl Γ t : pred1 Γ Γ t t.
  Proof. apply pred1_refl_gen, pred1_ctx_refl. Qed.

  Lemma pred1_ctx_over_refl Γ Δ : All2_fold (on_decls (on_decls_over pred1 Γ Γ)) Δ Δ.
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; constructor; auto.
    all:constructor; apply pred1_refl.
  Qed.

End ParallelReduction.

Hint Constructors pred1 : pcuic.
Hint Unfold All2_prop2_eq All2_prop2 on_decls_over on_rel on_Trel snd on_snd : pcuic.
Hint Resolve All2_same: pcuic.
Hint Constructors All2_fold : pcuic.

Hint Resolve pred1_ctx_refl : pcuic.

Ltac pcuic_simplify :=
  simpl || split || rdest || red.

Hint Extern 10 => progress pcuic_simplify : pcuic.

Notation pred1_ctx Σ Γ Γ' := (All2_fold (on_decls (pred1 Σ)) Γ Γ').
Notation pred1_ctx_over Σ Γ Γ' := (All2_fold (on_decls (on_decls_over (pred1 Σ) Γ Γ'))).

Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl_gen : pcuic.
Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl : pcuic.

Hint Extern 20 (#|?X| = #|?Y|) =>
match goal with
  [ H : All2_fold _ ?X ?Y |- _ ] => apply (All2_fold_length H)
| [ H : All2_fold _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
| [ H : All2_fold_over _ _ _ ?X ?Y |- _ ] => apply (All2_fold_length H)
| [ H : All2_fold_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_fold_length H)
end : pcuic.

Hint Extern 4 (pred1_ctx ?Σ ?Γ ?Γ') =>
  match goal with
  | [ H : pred1_ctx Σ (Γ ,,, _) (Γ' ,,, _) |- _ ] => apply (All2_fold_app_inv_left H)
  | [ H : pred1 Σ Γ Γ' _ _ |- _ ] => apply (pred1_pred1_ctx _ H)
  end : pcuic.

Ltac pcuic := try repeat red; cbn in *; try solve [intuition auto; eauto with pcuic || ltac:(try (lia || congruence))].

Ltac my_rename_hyp h th :=
  match th with
  | pred1_ctx _ _ ?G => fresh "pred" G
  | nat -> bool => fresh "P"
  | nat -> nat => fresh "f"
  | urenaming _ _ _ ?f => fresh "u" f
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma All2_fold_over_refl {Σ Γ Δ Γ'} :
  pred1_ctx Σ Γ Δ -> All2_fold_over (pred1 Σ) Γ Δ Γ' Γ'.
Proof.
  intros X0.
  red. induction Γ'. constructor.
  pose proof IHΓ'. apply All2_fold_over_app in IHΓ'; auto.
  constructor; auto.
  destruct a as [na [b|] ty]; constructor; pcuic.
Qed.

Hint Extern 4 (All2_fold_over _ _ _ ?X) =>
  tryif is_evar X then fail 1 else eapply All2_fold_over_refl : pcuic.

Section ParallelWeakening.
  Context {cf : checker_flags}.

  Lemma map_cofix_subst f mfix :
    (forall n, tCoFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f mfix :
    (forall n, tFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tFix mfix n)) ->
    fix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.
  
  Lemma lift_rename' n k : lift n k =1 rename (lift_renaming n k).
  Proof. intros t; apply lift_rename. Qed.

  Lemma lift_iota_red n k pars p args br :
    #|skipn pars args| = context_assumptions br.(bcontext) ->
    test_context_k closedn #|pparams p| (bcontext br) ->
    lift n k (iota_red pars p args br) =
    iota_red pars (map_predicate_k id (lift n) k p) (List.map (lift n k) args) (map_branch_k (lift n) id k br).
  Proof.
    intros hctx hctx'. rewrite !lift_rename'. rewrite rename_iota_red //.
    f_equal; try setoid_rewrite <-lift_rename => //.
    unfold map_branch_k, rename_branch, map_branch_shift.
    f_equal.
    * rewrite /shiftf /rename_predicate /map_predicate_k /= /id.
      f_equal.
      now setoid_rewrite lift_rename'.
      setoid_rewrite shiftn_lift_renaming.
      now rewrite lift_rename'.
    * rewrite /rename_branch /PCUICSigmaCalculus.rename_branch /map_branch_k /= /id.
      f_equal. now rewrite lift_rename' shiftn_lift_renaming.
  Qed.

  Lemma mapi_context_lift n k ctx :
    mapi_context (shiftf (lift n) k) ctx = lift_context n k ctx.
  Proof.
    now rewrite mapi_context_fold.
  Qed.

  Lemma All_decls_map P (f g : term -> term) d d' : 
    All_decls (fun x y => P (f x) (g y)) d d' ->
    All_decls P (map_decl f d) (map_decl g d').
  Proof.
    intros []; constructor; auto.
  Qed.

  Lemma All2_fold_context_k P (f g : nat -> term -> term) ctx ctx' : 
  All2_fold (fun Γ Γ' d d' => P (map_decl (f #|Γ|) d) (map_decl (g #|Γ'|) d')) ctx ctx' ->
  All2 P (fold_context_k f ctx) (fold_context_k g ctx'). 
Proof.
  induction 1. constructor.
  rewrite !fold_context_k_snoc0. now constructor.
Qed.
     
Lemma All2_sym {A B} (P : A -> B -> Type) (ctx : list A) (ctx' : list B) : 
  All2 P ctx ctx' -> 
  All2 (fun x y => P y x) ctx' ctx.
Proof.
  induction 1; constructor; auto.
Qed.

  Lemma on_ctx_free_vars_snoc_ass P Γ na ty : 
    on_ctx_free_vars P Γ ->
    on_free_vars P ty ->
    on_ctx_free_vars (PCUICOnFreeVars.shiftnP 1 P) (Γ ,, vass na ty).
  Proof.
    now rewrite on_ctx_free_vars_snoc => -> /=; rewrite /on_free_vars_decl /test_decl /=.
  Qed.
  
  Lemma on_ctx_free_vars_snoc_def P Γ na def ty : 
    on_ctx_free_vars P Γ ->
    on_free_vars P ty ->
    on_free_vars P def ->
    on_ctx_free_vars (PCUICOnFreeVars.shiftnP 1 P) (Γ ,, vdef na def ty).
  Proof.
    now rewrite on_ctx_free_vars_snoc => -> /=; rewrite /on_free_vars_decl /test_decl /= => -> ->.
  Qed.
  Hint Resolve on_ctx_free_vars_snoc_def on_ctx_free_vars_snoc_ass : pcuic.
  Hint Resolve urenaming_vass urenaming_vdef : pcuic.

  Lemma All2_fold_fold_context_k P (f g : nat -> term -> term) ctx ctx' :
    All2_fold (on_decls (fun Γ Γ' t t' => P (fold_context_k f Γ) (fold_context_k g Γ') 
    (f #|Γ| t) (g #|Γ'| t'))) ctx ctx' ->
    All2_fold (on_decls P) (fold_context_k f ctx) (fold_context_k g ctx').
  Proof.
    intros a. rewrite - !mapi_context_fold.
    eapply All2_fold_mapi.
    eapply (All2_fold_impl_ind a).
    intros par par' x y H.
    now rewrite !mapi_context_fold.
  Qed.
  
  Lemma All2_fold_rename_context Σ Δ Δ' Γ Γ' f :
    All2_fold
      (fun Γ Γ' : context =>
       All_decls
         (fun t t' : term =>
          on_decls_over (pred1 Σ) Δ Δ'
            (fold_context_k (fun i : nat => rename (shiftn i f)) Γ)
            (fold_context_k (fun i : nat => rename (shiftn i f)) Γ')
            (rename (shiftn #|Γ| f) t) (rename (shiftn #|Γ'| f) t'))) Γ Γ' ->
    pred1_ctx_over Σ Δ Δ' (rename_context f Γ) (rename_context f Γ').
  Proof.
    intros q.
    now eapply All2_fold_fold_context_k.
  Qed.

  (* Lemma All2_fold_All_fold_mix_left P Q Γ Γ' :
    All_fold P Γ ->
    All2_fold Q Γ Γ' ->
    All_
  All_fold P Δ ->
  (forall (Δ0 Δ' : context) (x y : context_decl),
   All_fold P Δ0 ->
   All_fold P Δ' -> All2_fold Q Δ0 Δ' -> P Δ0 x -> P Δ' y -> Q Δ0 Δ' x y) ->
  All2_fold Q Γ Δ *)

  Lemma All_decls_on_free_vars_impl P Q R d d' :
    All_decls P d d' ->
    on_free_vars_decl R d ->
    (forall t t', on_free_vars R t -> P t t' -> Q t t') ->
    All_decls Q d d'.
  Proof.
    move=> [] /=; constructor; auto.
    eapply X; eauto with pcuic.
    now move/andP: H => /= [].
    now move/andP: H => /= [].
  Qed.

  Lemma on_ctx_free_vars_snocS P Γ d : 
    on_ctx_free_vars (PCUICOnFreeVars.shiftnP (S #|Γ|) P) (d :: Γ) = 
    on_ctx_free_vars (PCUICOnFreeVars.shiftnP #|Γ| P) Γ && on_free_vars_decl (PCUICOnFreeVars.shiftnP #|Γ| P) d.
  Proof.
    rewrite -(shiftnP_add 1).
    now rewrite on_ctx_free_vars_snoc.
  Qed.

  Ltac inv_on_free_vars ::=
    match goal with
    | [ H : is_true (on_free_vars ?P ?t) |- _ ] => 
      progress (cbn in H || rewrite on_free_vars_mkApps in H);
      (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] || 
        eapply forallb_All in H); intros
    end.

  Hint Resolve on_free_vars_fix_context : fvs.

  (** This not only proves that parallel reduction has renaming, it also
      ensures that it only looks at the variables actually used in the term/context.
      This lemma can later be used to show weakening but also verify that 
      strenghtening is admissible for parallel reduction: i.e. the case of
      a renaming that is only defined on a subset of the variables of 
      the context.
  *)

  Lemma pred1_rename {Σ} {wfΣ : wf Σ} : 
    (forall Γ Γ' u v, pred1 Σ Γ Γ' u v ->
    forall {P f Δ Δ'},
    pred1_ctx Σ Δ Δ' ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars P u ->
    on_ctx_free_vars P Γ ->
    pred1 Σ Δ Δ' (rename f u) (rename f v)) ×
    (forall (Γ Γ' : context) (Δ Δ' : context),
      pred1_ctx Σ Γ Γ' ->
      pred1_ctx_over Σ Γ Γ' Δ Δ' ->
      forall P f Δ0 Δ'0, 
        urenaming P Δ0 Γ f ->
        urenaming P Δ'0 Γ' f ->
        pred1_ctx Σ Δ0 Δ'0 ->
        on_ctx_free_vars P Γ ->
        on_free_vars_ctx P Δ ->
        pred1_ctx_over Σ Δ0 Δ'0 (rename_context f Δ) (rename_context f Δ')).
  Proof using cf.
    set (Pctx := fun (Γ Γ' : context) => pred1_ctx Σ Γ Γ').

    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros; 
      subst Pctx;
    rename_all_hyps; try subst Γ Γ'; 
    lazymatch goal with
    | |- context [tCase _ _ _ _] => idtac
    | |- _ => simplify_IH_hyps
    end; cbn -[iota_red];
    match goal with
    |- context [iota_red _ _ _] => idtac
    | |- _ => autorewrite with lift
    end;
    try specialize (forall_P P f Δ Δ' uf uf0);
    try specialize (forall_P0 P f Δ Δ' uf uf0);
    try specialize (forall_P1 P f Δ Δ' uf uf0);
    try pose proof (All2_fold_length X0);
    try specialize (X0 _ _ eq_refl _ _ eq_refl heq_length _ _ ltac:(eauto));
    simpl; try solve [ econstructor; eauto; try apply All2_map;
                    unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
    unfold All2_prop_eq, All2_prop, on_Trel, id in *.
    all:try inv_on_free_vars.
    all:try solve [econstructor; eauto].
    12:{
      econstructor; eauto.
      eapply forall_P0; eauto with pcuic.
      repeat (econstructor; eauto).
    }
    15:{
      econstructor; eauto.
      rewrite !rename_fix_context. eapply forall_P; tea; eauto with fvs.
      red in X3 |- *.
      eapply All2_All_mix_left in X3; tea.
      eapply All2_map.
      rewrite /= !rename_fix_context /= /on_Trel /=.
      rewrite /on_Trel /= in X3.
      pose proof (All2_length X3).
      eapply (All2_impl X3). intuition auto.
      move/andP: a => [] clty cldef.
      eapply b; tea.
      rewrite -H2.
      eapply b0; tea.
      * eapply All2_fold_app => //. eapply X2; tea; eauto with fvs.
      * relativize #|mfix0|; [eapply urenaming_context|]; tea; now len.
      * len; relativize #|mfix0|; [eapply urenaming_context|]; tea; now len.
      * move/andP: a => []. now len.
      * rewrite on_ctx_free_vars_concat H0 /=.
        rewrite on_free_vars_ctx_on_ctx_free_vars. now eapply on_free_vars_fix_context.
    }

    1:{ exact predΓ'. }
        
    - rename uf0 into uf'.
      rename H into onΓ; rename H0 into onΔ.
      eapply All2_fold_fold_context_k.
      induction X3.
      * constructor; auto.
      * move: onΔ.
        rewrite -on_free_vars_ctx_on_ctx_free_vars on_ctx_free_vars_snocS => /andP[] onΓ0 ond.
        rewrite on_free_vars_ctx_on_ctx_free_vars in onΓ0.
        depelim X2.
        do 2 forward IHX3 by auto.
        constructor; auto.
        eapply All_decls_on_free_vars_impl; tea.
        intros t t' ont. unfold on_decls_over => IH.
        rewrite -(All2_fold_length IHX3).
        rewrite - !/(rename_context _ _).
        eapply IH; tea; auto with pcuic.
        + eapply All2_fold_app => //.
          eapply All2_fold_fold_context_k => //.
        + now eapply urenaming_context.
        + rewrite (All2_fold_length IHX3). now eapply urenaming_context.
        + now rewrite on_ctx_free_vars_concat onΓ on_free_vars_ctx_on_ctx_free_vars onΓ0.

    - (* Beta *)
      move/andP: a => [] onty onbody.
      rewrite rename_subst10.
      econstructor; eauto.
      eapply (forall_P (PCUICOnFreeVars.shiftnP 1 P) (shiftn 1 f)); auto with pcuic.
      repeat (constructor; eauto).

    - (* Let *) 
      rewrite rename_subst10.
      econstructor; eauto.
      eapply (forall_P1 (PCUICOnFreeVars.shiftnP 1 P) (shiftn 1 f)); eauto with pcuic.
      repeat (constructor; eauto).
    
    - (* Rel *)
      rewrite lift0_rename /rshiftk.
      cbn in H0.
      epose proof (nth_error_pred1_ctx _ _ predΓ' heq_option_map) as [bod [hbod predbod]].
      destruct (nth_error Γ i) eqn:hnth => //. noconf hbod.
      destruct (nth_error Γ' i) eqn:hnth' => //.
      simpl in X0.
      unfold urenaming in uf, uf0.
      specialize uf0 with (1 := H0) (2 := hnth') as [decl' [nthΔ' [eqba [reneq onb]]]].
      specialize uf with (1 := H0) (2 := hnth) as [decl'' [nthΔ'' [eqba' [reneq' onb']]]].
      cbn in heq_option_map. noconf heq_option_map.
      rewrite H in onb. rewrite H3 in onb'; cbn in *.
      destruct decl' as [? [?|] ?]; noconf onb; cbn in *.
      destruct decl'' as [? [?|] ?]; noconf onb'; cbn in *.
      rewrite rename_compose H4.
      replace (rename (fun m => S (f i + m)) t) with (lift0 (S (f i)) t).
      2:{ rewrite lift0_rename //. }
      econstructor; eauto.
      rewrite nthΔ' /= //.

    - (* Iota reduction *)
      rewrite rename_mkApps. simpl.
      eapply forallb_All in p4.
      eapply All2_All_mix_left in X3; tea.
      rewrite rename_iota_red //.
      * eapply All2_nth_error_Some_right in X3 as [br' [nthbr [? []]]]; tea.
        move/andP: i => [] clbctx onfvs.
        destruct p5.
        rewrite -e.
        rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
        now rewrite closedn_ctx_on_free_vars.      
      * move: p3; rewrite on_free_vars_mkApps /= => /forallb_All Hargs.
        eapply All2_All_mix_left in X1; tea.
        econstructor; tea; try solve [solve_all].
        + erewrite nth_error_map, heq_nth_error => //.
        + simpl. now len.
        + simpl. eapply All2_map; solve_all.
        + eapply All2_map, (All2_impl X3).
          move=> x y [] /andP [] onctx onb [] IHctx [] [] Hbod IHbod eqc; cbn.
          simpl.
          rewrite -eqc.
          rewrite {2}/id.
          rewrite /PCUICSigmaCalculus.rename_branch /inst_case_branch_context /= /id.
          rewrite -rename_inst_case_context_wf //.
          rewrite -rename_inst_case_context_wf //.
          { now rewrite -(All2_length X2). }
          split.
          { rewrite -eqc in IHctx. eapply IHctx; tea.
            eapply on_free_vars_ctx_inst_case_context; tea => //. }
          split => //. eapply IHbod; tea.
          { eapply All2_fold_app => //. rewrite -eqc in IHctx. eapply IHctx; tea.
            eapply on_free_vars_ctx_inst_case_context; tea. reflexivity. }
          { relativize #|bcontext x|; [apply: urenaming_context|] => //.
            now rewrite inst_case_context_length. }
          { rewrite -eqc. relativize #|bcontext x|; [apply: urenaming_context|] => //.
            now rewrite inst_case_context_length. }
          { relativize #|bcontext x|; [erewrite on_ctx_free_vars_concat, H2|].
            2:{ now rewrite inst_case_context_length. }
            rewrite /=.
            rewrite on_free_vars_ctx_on_ctx_free_vars.
            eapply on_free_vars_ctx_inst_case_context; trea. }

    - (* Fixpoint unfolding *) 
      rewrite 2!rename_mkApps. simpl. inv_on_free_vars.
      econstructor; tas.
      3:eapply rename_unfold_fix; tea.
      3:eapply is_constructor_rename; tea.
      + rewrite !rename_fix_context.
        eapply forall_P; tea.
        eapply on_free_vars_fix_context; solve_all.
      + red in X3 |- *. pose proof (All2_length X3).
        eapply All2_All_mix_left in X3; tea.
        eapply All2_map => /=; rewrite /on_Trel /=.
        rewrite !rename_fix_context.
        eapply (All2_impl X3); solve_all.
        unfold on_Trel in *; cbn; solve_all.
        eapply b1; tea. now move/andP: a.
        rewrite -H0; eapply b0; tea.
        * eapply All2_fold_app => //. eapply X2; tea.
          eapply on_free_vars_fix_context. solve_all.
        * relativize #|mfix0|; [eapply urenaming_context|]; tea; now len.
        * len. relativize #|mfix0|; [eapply urenaming_context|]; tea; now len.
        * len. now move/andP: a.
        * rewrite on_ctx_free_vars_concat on_free_vars_ctx_on_ctx_free_vars H2.
          eapply on_free_vars_fix_context; solve_all.
      + solve_all.

    - rewrite 2!rename_mkApps. simpl. repeat inv_on_free_vars.
      eapply pred_cofix_case; tea.
      3:eapply rename_unfold_cofix; tea.
      all:try rewrite !rename_fix_context.
      + eapply forall_P; tea.
        eapply on_free_vars_fix_context; solve_all.
      + eapply All2_All_mix_left in X3; tea.
        eapply All2_map, (All2_impl X3); unfold on_Trel; cbn.
        move=> x y [] /andP[] onty onbod [] [] pty IHbty [] [] pbody IHpbody [=] eqna eqrarg.
        solve_all.
        rewrite -(All2_length X3).
        rewrite -(fix_context_length mfix0) in onbod *.
        eapply IHpbody; tea.
        * eapply All2_fold_app => //. eapply X6; eauto.
          eapply on_free_vars_fix_context; solve_all.
        * now eapply urenaming_context.
        * relativize #|fix_context mfix0|; [eapply urenaming_context|]; len; trea.
          now rewrite (All2_length X3).
        * rewrite on_ctx_free_vars_concat H3 /= on_free_vars_ctx_on_ctx_free_vars.
          eapply on_free_vars_fix_context; solve_all.
      + solve_all.
      + cbn. solve_all.
      + cbn. rewrite /map_predicate_shift /PCUICCases.inst_case_predicate_context /=.
        rewrite - !rename_inst_case_context_wf //.
        { now rewrite -(All2_length X5). }
        eapply forall_P0; tea.
        now eapply on_free_vars_ctx_inst_case_context.
      + cbn.
        rewrite /map_predicate_shift /PCUICCases.inst_case_predicate_context /=.
        rewrite - !rename_inst_case_context_wf //.
        { now rewrite -(All2_length X5). }
        rewrite -heq_pcontext.
        eapply forall_P1; trea.
        * eapply All2_fold_app => //.
          rewrite {2}heq_pcontext. eapply forall_P0; tea.
          now eapply on_free_vars_ctx_inst_case_context.
        * relativize #|pcontext p0|; [eapply urenaming_context|]; len; trea.
        * rewrite heq_pcontext. 
          relativize #|pcontext p1|; [eapply urenaming_context|]; len; trea.
        * relativize #|pcontext p0|. erewrite on_ctx_free_vars_extend, H3. cbn. 
          now eapply on_free_vars_ctx_inst_case_context. now len.
      + eapply All2_map. 
        eapply forallb_All in p5. eapply All2_All_mix_left in X9; tea.
        eapply (All2_impl X9).
        move=> x y [] /andP[] onpars onbod [] IHbctx [] [] hbod IHbod eq. unfold on_Trel.
        rewrite /map_predicate_shift /= /inst_case_branch_context /=.
        rewrite - !rename_inst_case_context_wf //.
        { now rewrite -(All2_length X5). }
        split; [|split] => //.
        * eapply IHbctx; tea.
          now eapply on_free_vars_ctx_inst_case_context.
        * rewrite -eq; eapply IHbod; tea.
          { rewrite {2}eq.
            eapply All2_fold_app => //.
            eapply IHbctx; tea.
            now eapply on_free_vars_ctx_inst_case_context. }
          { relativize #|bcontext x|; [eapply urenaming_context|]; len; trea. }
          { rewrite eq; relativize #|bcontext y|;[eapply urenaming_context|]; len; trea. }
          { relativize #|bcontext x|. erewrite on_ctx_free_vars_concat, H3.
            rewrite on_free_vars_ctx_on_ctx_free_vars.
            eapply on_free_vars_ctx_inst_case_context; solve_all. now len. }
      
    - rewrite 2!rename_mkApps. simpl. cbn in H0. repeat inv_on_free_vars.
      econstructor; tea.
      3:eapply rename_unfold_cofix; tea.
      all:try rewrite !rename_fix_context.
      + eapply forall_P; tea.
        now eapply on_free_vars_fix_context.
      + eapply All2_All_mix_left in X3; tea.
        eapply All2_map, (All2_impl X3).
        move=> x y [] /andP[] hty hbody. rewrite /on_Trel.
        move=> [] [] Hty IHty [] [] Hbod IHbod /= [=] hna hrarg.
        repeat split; auto. 3:congruence.
        eapply IHty; tea.
        rewrite -(All2_length X3).
        eapply IHbod; tea.
        { eapply All2_fold_app => //. eapply forall_P; tea.
          now eapply on_free_vars_fix_context. }
        { relativize #|mfix0|; [eapply urenaming_context|]; len; trea. }
        { relativize #|mfix0|; [eapply urenaming_context|]; len; trea.
          now rewrite (All2_length X3). }
        { rewrite -(fix_context_length mfix0). rewrite on_ctx_free_vars_concat H1 /=.
          rewrite on_free_vars_ctx_on_ctx_free_vars. now apply on_free_vars_fix_context. }
      + solve_all.

    - rewrite rename_subst_instance.
      econstructor; tea.
      rewrite rename_closed. 2: assumption.
      eapply (PCUICClosed.declared_constant_closed_body). all: eauto.
    - rewrite rename_mkApps. simpl. cbn in H0; inv_on_free_vars.
      econstructor; tea. 2:erewrite nth_error_map, heq_nth_error; reflexivity.
      solve_all.
    - constructor; eauto.
      eapply forall_P1; tea.
      { constructor; eauto with pcuic. constructor; eauto. }
      { eapply urenaming_vdef; eauto. }
      { eapply urenaming_vdef; eauto. }
      eapply on_ctx_free_vars_snoc_def; eauto.
    - rewrite /map_predicate_shift /=.
      constructor; cbn; eauto.
      all:rewrite /PCUICCases.inst_case_predicate_context /inst_case_branch_context /=.
      all:try rewrite - !rename_inst_case_context_wf //.
      2,4:now rewrite -heq_pcontext - ?(All2_length X1).
      solve_all.
      { eapply forall_P; tea.
        now eapply on_free_vars_ctx_inst_case_context. }
      { relativize #|pcontext p1|. eapply forall_P0; tea.
        + eapply All2_fold_app => //. eapply forall_P; tea.
          now eapply on_free_vars_ctx_inst_case_context.
        + relativize #|pcontext p0|; [eapply urenaming_context|]; len; trea.
        + relativize #|pcontext p0|; [eapply urenaming_context|]; len; trea.
          now rewrite heq_pcontext.
        + relativize #|pcontext p0|; [erewrite on_ctx_free_vars_concat, H2|]; len; trea.
          relativize #|pcontext p0|; [erewrite on_free_vars_ctx_on_ctx_free_vars|]; len; trea.
          now eapply on_free_vars_ctx_inst_case_context.
        + now rewrite heq_pcontext.
      }
      eapply All2_map; cbn. solve_all.
      all:rewrite - !rename_inst_case_context_wf //.
      1,3:rewrite - ?b -(All2_length X1) //.
      { eapply a0; tea.
        eapply on_free_vars_ctx_inst_case_context; trea. solve_all. }
      { relativize #|bcontext y|; [eapply b0|]; len; trea.
        { eapply All2_fold_app => //. eapply a0; tea.
          eapply on_free_vars_ctx_inst_case_context; trea. solve_all. }
        { relativize #|bcontext x|; [eapply urenaming_context|]; len; trea. }
        { rewrite /inst_case_branch_context. 
          relativize #|bcontext x|; [eapply urenaming_context|]; len; trea.
          now rewrite b. }
        { relativize #|bcontext x|; [erewrite on_ctx_free_vars_concat, H2|]; len; trea.
          rewrite /inst_case_branch_context.
          relativize #|bcontext x|; [erewrite on_free_vars_ctx_on_ctx_free_vars|]; len; trea.
          eapply on_free_vars_ctx_inst_case_context; len; trea.
          solve_all. }
        now rewrite b. }

    - econstructor; tea.
      rewrite !rename_fix_context. eapply forall_P; tea; eauto with fvs.
      rewrite /All2_prop2_eq in X3 *.
      eapply All2_All_mix_left in X3; tea.
      eapply All2_map, (All2_impl X3).
      move=> x y [] /andP [] onty onbody. rewrite /on_Trel /=.
      move=> [] [] Hty IHty [] [] Hbod IHbod [=] hna hrarg.
      repeat split; try congruence. eauto with fvs.
      rewrite !rename_fix_context.
      relativize #|mfix1|. eapply IHbod; tea.
      { eapply All2_fold_app => //. eapply forall_P; tea; eauto with fvs. }
      { rewrite -(fix_context_length mfix0). now eapply urenaming_context. }
      { rewrite (All2_length X3) -(fix_context_length mfix1).
        now eapply urenaming_context. }
      { rewrite -(fix_context_length mfix0).
        rewrite on_ctx_free_vars_extend H0 on_free_vars_fix_context //. }
      now rewrite (All2_length X3).
    - econstructor; tea; eauto with fvs.
      eapply forall_P0; tea; eauto with fvs.
      repeat (constructor; eauto).
      1-2:now eapply urenaming_vass.
      now eapply on_ctx_free_vars_snoc_ass.
    - econstructor; tea. solve_all.
    - destruct t => //; constructor; auto.
  Qed.

  Lemma weakening_pred1 {Σ} {wfΣ : wf Σ} {P Γ Γ' Γ'' Δ Δ' Δ'' M N} :
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') M N ->
    on_ctx_free_vars (PCUICOnFreeVars.shiftnP #|Γ'| P) (Γ ,,, Γ') ->    
    on_free_vars (PCUICOnFreeVars.shiftnP #|Γ'| P) M ->
    #|Γ| = #|Δ| ->
    All2_fold_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
          (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
          (lift #|Γ''| #|Γ'| M) (lift #|Δ''| #|Δ'| N).
  Proof.
    intros H onΓ onM hlen predo.
    rewrite !lift_rename.
    pose proof (All2_fold_length predo).
    rewrite -H0.
    pose proof (pred1_pred1_ctx _ H).
    eapply All2_fold_length in X. len in X.
    assert (#|Δ'| = #|Γ'|)  by lia. rewrite -H1.
    eapply (fst pred1_rename _ _ _ _ ). tea.
    { pose proof (pred1_pred1_ctx _ H).
      eapply All2_fold_app_inv in X0 as [] => //.
      eapply All2_fold_app.
      eapply All2_fold_app => //.
      rewrite - !rename_context_lift_context.
      eapply (snd pred1_rename).
      5:{ eapply All2_fold_app in predo => //. } exact a.
      2:tea. assumption.
      eapply (weakening_renaming _ Γ []).
      rewrite H0.
      eapply (weakening_renaming _ _ []).
      rewrite on_ctx_free_vars_concat in onΓ.
      move/andP: onΓ=> []; eauto.
      rewrite on_ctx_free_vars_concat in onΓ.
      move/andP: onΓ => [] _.
      now rewrite on_free_vars_ctx_on_ctx_free_vars. }
    rewrite H1. eapply weakening_renaming.
    rewrite H0. apply weakening_renaming.
    2:tea. tea.
  Qed.

  Lemma weakening_pred1_pred1 {Σ} {wfΣ : wf Σ} {P Γ Δ Γ' Δ' M N} :
    pred1_ctx_over Σ Γ Δ Γ' Δ' ->
    on_ctx_free_vars P Γ -> 
    on_free_vars P M ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 #|Γ'| M) (lift0 #|Δ'| N).
  Proof.
    intros; eapply (weakening_pred1 (Γ' := []) (Δ' := [])); eauto.
    now rewrite shiftnP0.
    now rewrite shiftnP0.
    pose proof (pred1_pred1_ctx _ X0).
    now rewrite (All2_fold_length X1).
  Qed.

  Lemma weakening_pred1_0 {Σ} {wfΣ : wf Σ} {P Γ Δ Γ' M N} :
    pred1 Σ Γ Δ M N ->
    on_ctx_free_vars P Γ -> 
    on_free_vars P M ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof.
    intros p onΓ onM.
    eapply weakening_pred1_pred1; tea.
    apply All2_fold_over_refl; pcuic.
  Qed.

  Lemma All2_fold_over_pred1_ctx Σ Γ Γ' Δ Δ' :
    #|Δ| = #|Δ'| ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    All2_fold
      (on_decls (on_decls_over (pred1 Σ) Γ Γ')) Δ Δ'.
  Proof.
    intros. pose proof (All2_fold_length X).
    apply All2_fold_app_inv in X.
    intuition. auto. rewrite !app_context_length in H0. pcuic.
  Qed.
  Hint Resolve All2_fold_over_pred1_ctx : pcuic.

  Lemma nth_error_pred1_ctx_all_defs {P} {Γ Δ} :
    on_contexts P Γ Δ ->
    forall i body body', option_map decl_body (nth_error Γ i) = Some (Some body) ->
              option_map decl_body (nth_error Δ i) = Some (Some body') ->
              P (skipn (S i) Γ) (skipn (S i) Δ) body body'.
  Proof.
    induction 1; destruct i; simpl; try discriminate; depelim p => //;
    intros; noconf H; noconf H0; auto.
  Qed.

  Lemma All2_fold_over_firstn_skipn:
    forall (Σ : global_env) (i : nat) (Δ' R : context),
      pred1_ctx Σ Δ' R ->
      All2_fold_over (pred1 Σ) (skipn i Δ') (skipn i R) (firstn i Δ') (firstn i R).
  Proof.
    intros Σ i Δ' R redr.
    induction redr in i |- *; simpl.
    * destruct i; constructor; pcuic.
    * destruct i; simpl; constructor; pcuic. apply IHredr.
      depelim p; constructor; auto; repeat red; now rewrite /app_context !firstn_skipn.
  Qed.

End ParallelWeakening.

Hint Resolve pred1_pred1_ctx : pcuic.

Section ParallelSubstitution.
  Context {cf : checker_flags}.

  Inductive psubst Σ (Γ Γ' : context) : list term -> list term -> context -> context -> Type :=
  | psubst_empty : psubst Σ Γ Γ' [] [] [] []
  | psubst_vass Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' t t' ->
      psubst Σ Γ Γ' (t :: s) (t' :: s') (Δ ,, vass na T) (Δ' ,, vass na' T')
  | psubst_vdef Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ Γ' (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T) (Δ' ,, vdef na' t' T').

  Lemma psubst_length {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' ->
                                           #|s| = #|Γ'| /\ #|s'| = #|Δ'| /\ #|s| = #|s'|.
  Proof.
    induction 1; simpl; intuition lia.
  Qed.

  Lemma psubst_length' {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; lia.
  Qed.

  Lemma psubst_nth_error Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ decl decl' t',
      (nth_error Γ' n = Some decl) *
      (nth_error Δ' n = Some decl') *
      (nth_error s' n = Some t') *
    match decl_body decl, decl_body decl' with
    | Some d, Some d' =>
        let s2 := (skipn (S n) s) in
        let s2' := (skipn (S n) s') in
      let b := subst0 s2 d in
      let b' := subst0 s2' d' in
      psubst Σ Γ Δ s2 s2' (skipn (S n) Γ') (skipn (S n) Δ') *
      (t = b) * (t' = b') * pred1 Σ Γ Δ t t'
    | None, None => pred1 Σ Γ Δ t t'
    | _, _ => False
    end.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), (vass na' T'), t'. intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (vdef na t0 T), (vdef na' t' T'), (subst0 s' t'). intuition auto.
      simpl. intuition simpl; auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error' Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ t',
      (nth_error s' n = Some t') *
      pred1 Σ Γ Δ t t'.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists t'; intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (subst0 s' t'). intuition auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error_None Σ Γ Δ Γ' Δ' s s' n :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = None ->
    (nth_error Γ' n = None) * (nth_error Δ' n = None)* (nth_error s' n = None).
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; intros; intuition try congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
  Qed.

  Lemma subst_skipn' n s k t : k < n -> (n - k) <= #|s| ->
    lift0 k (subst0 (skipn (n - k) s) t) = subst s k (lift0 n t).
  Proof.
    intros Hk Hn.
    assert (#|firstn (n - k) s| = n - k) by (rewrite firstn_length_le; lia).
    assert (k + (n - k) = n) by lia.
    assert (n - k + k = n) by lia.
    rewrite <- (firstn_skipn (n - k) s) at 2.
    rewrite subst_app_simpl. rewrite H H0.
    rewrite <- (commut_lift_subst_rec t _ n 0 0); try lia.
    generalize (subst0 (skipn (n - k) s) t). intros.
    erewrite <- (simpl_subst_rec _ (firstn (n - k) s) _ k); try lia.
    now rewrite H H1.
  Qed.

  Lemma split_app3 {A} (l l' l'' : list A) (l1 l1' l1'' : list A) :
    #|l| = #|l1| -> #|l'| = #|l1'| ->
        l ++ l' ++ l'' = l1 ++ l1' ++ l1'' ->
        l = l1 /\ l' = l1' /\ l'' = l1''.
  Proof.
    intros.
    eapply app_inj_length_l in H1 as [Hl Hr]; auto.
    eapply app_inj_length_l in Hr as [Hl' Hr]; auto.
  Qed.

  Lemma All2_fold_subst_ctx :
    forall (Σ : global_env) c c0 (Γ0 Δ : context)
    (Γ'0 : list context_decl) (Γ1 Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
      psubst Σ Γ0 Γ1 s s' Δ Δ1 ->
      #|Γ'0| = #|Γ'1| ->
      #|Γ0| = #|Γ1| ->
      All2_fold_over (pred1 Σ) Γ0 Γ1 Δ Δ1 ->
     All2_fold
      (on_decls
       (on_decls_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall (Γ2 Δ0 : context) (Γ'2 : list context_decl),
           Γ = Γ2 ,,, Δ0 ,,, Γ'2 ->
           forall (Γ3 Δ2 : context) (Γ'3 : list context_decl) (s0 s'0 : list term),
           psubst Σ Γ2 Γ3 s0 s'0 Δ0 Δ2 ->
           Γ' = Γ3 ,,, Δ2 ,,, Γ'3 ->
           #|Γ2| = #|Γ3| ->
           #|Γ'2| = #|Γ'3| ->
           All2_fold_over (pred1 Σ) Γ2 Γ3 Δ0 Δ2 ->
           pred1 Σ (Γ2 ,,, subst_context s0 0 Γ'2) (Γ3 ,,, subst_context s'0 0 Γ'3) (subst s0 #|Γ'2| t)
             (subst s'0 #|Γ'3| t0)) (Γ0 ,,, Δ ,,, Γ'0) (Γ1 ,,, Δ1 ,,, Γ'1))) c c0 ->
  All2_fold (on_decls (on_decls_over (pred1 Σ) (Γ0 ,,, subst_context s 0 Γ'0) (Γ1 ,,, subst_context s' 0 Γ'1)))
    (subst_context s #|Γ'0| c) (subst_context s' #|Γ'1| c0).
  Proof.
    intros.
    pose proof (All2_fold_length X1).
    induction X1; simpl; rewrite ?subst_context_snoc; constructor; auto; rename_all_hyps.
    eapply All_decls_map, All_decls_impl; tea => /=.
    unfold on_decls_over. intros; rename_all_hyps.
    simpl in heq_length1.
    specialize (forall_Γ2 _ _ (Γ'0 ,,, Γ)
                ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                ltac:(now rewrite app_context_assoc) heq_length0
                ltac:(now rewrite !app_context_length; len; lia) X0).
    simpl in *.
    rewrite !subst_context_app !app_context_length !app_context_assoc !Nat.add_0_r in forall_Γ2.
    simpl. congruence.
  Qed.

  Lemma mapi_context_subst s k ctx :
    mapi_context (shiftf (subst s) k) ctx = subst_context s k ctx.
  Proof.
    now rewrite mapi_context_fold.
  Qed.

  Context {Σ : global_env_ext}.

  Definition pred1_subst (P : nat -> bool) (Γ Γ' Δ Δ' : context) (σ τ : nat -> term) :=
    forall x,
      on_free_vars P (σ x) ×
      pred1 Σ Δ Δ' (σ x) (τ x) ×
      match option_map decl_body (nth_error Γ x) return Type with
      | Some (Some b) =>
        (∑ b', 
          (* The Γ' context necessarily has a let-in for i and [σ i] must reduce to it in Δ *)
          option_map decl_body (nth_error Γ' x) = Some (Some b') ×
          (pred1 Σ Δ Δ' (σ x) (b'.[↑^(S x) ∘s τ])))
      | _ => True
    end.

  Lemma pred1_subst_pred1_ctx {P Γ Γ' Δ Δ' σ τ} :
    pred1_subst P Γ Γ' Δ Δ' σ τ ->
    pred1_ctx Σ Δ Δ'.
  Proof. intros Hrel. destruct (Hrel 0). pcuic. Qed.

  Hint Extern 4 (pred1_ctx ?Σ ?Δ ?Δ') =>
  match goal with
    H : pred1_subst _ _ Δ Δ' _ _ |- _ =>
    apply (pred1_subst_pred1_ctx H)
  end : pcuic.

  Lemma simpl_pred Γ Γ' t t' u u' : t = t' -> u = u' -> pred1 Σ Γ Γ' t' u' -> pred1 Σ Γ Γ' t u.
  Proof. now intros -> ->. Qed.

  Lemma pred1_subst_ext P P' Γ Γ' Δ Δ' σ σ' τ τ' : 
    P =1 P' ->
    σ =1 σ' ->
    τ =1 τ' ->
    pred1_subst P Γ Γ' Δ Δ' σ τ <~> pred1_subst P' Γ Γ' Δ Δ' σ' τ'.
  Proof.
    intros HP Hσ Hτ.
    rewrite /pred1_subst. split; intros H x; specialize (H x) as [? ?].
    split. now rewrite -HP. rewrite -(Hσ x) -(Hτ x).
    destruct p. split => //. destruct option_map => //.
    destruct o => //. destruct y as [b' []]. exists b'; split => //.
    eapply simpl_pred. 2:rewrite -Hτ; trea. reflexivity. assumption.
    split. now rewrite HP.
    destruct p; split => //. now rewrite (Hσ x) (Hτ x).
    destruct option_map as [[]|] => //.
    destruct y as [b' []]; exists b'; split => //.
    eapply simpl_pred. now rewrite Hσ. now rewrite Hτ.
    assumption.
  Qed.

  Lemma pred1_subst_Up {wfΣ : wf Σ} P (Γ Γ' : context) (na : aname) (t0 t1 : term) (Δ Δ' : context) (σ τ : nat -> term) :
      on_ctx_free_vars P Δ ->
      pred1 Σ Δ Δ' t0.[σ] t1.[τ] ->
      pred1_subst P Γ Γ' Δ Δ' σ τ ->
      pred1_subst (PCUICOnFreeVars.shiftnP 1 P) (Γ,, vass na t0) (Γ' ,, vass na t1) (Δ,, vass na t0.[σ]) (Δ',, vass na t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros onΔ X2 Hrel.
    intros x. destruct x; simpl. split; auto. split; auto.
    eapply pred1_refl_gen. constructor; eauto with pcuic. now constructor.
    unfold subst_compose.
    split.
    rewrite - !(lift0_inst 1).
    eapply on_free_vars_lift0. rewrite addnP_shiftnP. apply Hrel.
    rewrite - !(lift0_inst 1).
    split. eapply (weakening_pred1_pred1 (Γ' := [_]) (Δ' := [_])); auto.
    repeat (constructor; auto). tea. eapply Hrel. apply Hrel.
    destruct (Hrel x) as [? []]. destruct option_map as [[o|]|] => //.
    destruct y as [b' []]; exists b'. split => //.
    eapply simpl_pred. reflexivity.
    
    rewrite -shiftnP_add.
  Qed.

  Lemma pred1_subst_vdef_Up {wfΣ : wf Σ} P (Γ : context) (na : aname) (b0 b1 t0 t1 : term) (Δ Δ' : context) 
    (σ τ : nat -> term) :
    on_ctx_free_vars P Δ ->
    pred1 Σ Δ Δ' t0.[σ] t1.[τ] ->
      pred1 Σ Δ Δ' b0.[σ] b1.[τ] ->
      pred1_subst P Γ Δ Δ' σ τ ->
      pred1_subst (shiftnP 1 P) (Γ,, vdef na b0 t0) (Δ,, vdef na b0.[σ] t0.[σ]) (Δ',, vdef na b1.[τ] t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros onΔ Xt Xb Hrel.
    intros x. destruct x; simpl. split; auto. eapply pred1_refl_gen.
    constructor; eauto with pcuic; constructor; auto.
    unfold subst_compose. rewrite - !(lift0_inst 1).
    split.
    - eapply on_free_vars_lift0; rewrite addnP_shiftnP. apply Hrel.
    - eapply (weakening_pred1_pred1 (Γ' := [_]) (Δ' := [_])); eauto.
      repeat (constructor; auto). apply Hrel. apply Hrel.
    (* destruct (Hrel x). destruct option_map as [[o|]|]; now rewrite ?y. *)
  Qed.

  Lemma leb_S x y : S x <= y -> x <? y.
  Proof. intros. apply Nat.leb_le. lia. Qed.

  Lemma pred1_subst_Upn {wfΣ : wf Σ} {P} {Γ Δ Δ' σ τ Γ' Δ0 Δ1 n} :
    #|Γ'| = #|Δ0| -> #|Δ0| = #|Δ1| -> n = #|Δ0| ->
    on_ctx_free_vars P Δ ->
    pred1_subst P Γ Δ Δ' σ τ ->
    pred1_ctx_over Σ Δ Δ' Δ0 Δ1 ->
    pred1_subst (shiftnP #|Γ'| P) (Γ ,,, Γ') (Δ ,,, Δ0) (Δ' ,,, Δ1) (⇑^n σ) (⇑^n τ).
  Proof.
    intros * len0 len1 -> onΔ Hrel.
    red. intros H x.
    destruct (leb_spec_Set (S x) #|idsn #|Δ0| |).
    unfold Upn.
    specialize (subst_consn_lt_spec l).
    intros [tx [Hdecl Heq]].
    rewrite !Heq. split.
    apply nth_error_idsn_eq_Some in Hdecl. subst. simpl.
    len in l. unfold shiftnP. now rewrite len0 (leb_S _ _ l).
    eapply pred1_refl_gen. auto.
    eapply All2_fold_over_app; auto. destruct (Hrel 0). pcuic.
    split. rewrite len0.
    unfold Upn.
    rewrite subst_consn_ge. lia. len.
    unfold subst_compose. rewrite - !(lift0_inst _).
    eapply on_free_vars_lift0. rewrite addnP_shiftnP.
    eapply Hrel.
    unfold Upn.
    rewrite !subst_consn_ge. lia. lia.
    rewrite idsn_length. specialize (Hrel (x - #|Δ0|)).
    destruct Hrel.
    unfold subst_compose. rewrite - !(lift0_inst _).
    rewrite {3}len1.
    eapply weakening_pred1_pred1; eauto.

    (* rewrite nth_error_app_ge. rewrite idsn_length in l. lia.
    rewrite len0.
    destruct option_map as [[o|]|]; auto.
    unfold subst_compose. simpl. rewrite y. reflexivity. *)
  Qed.

  Lemma pred1_subst_up {wfΣ : wf Σ} {P} {Γ Δ Δ'} (σ τ : nat -> term) (Γ' Δ0 Δ1 : context) n :
    #|Γ'| = #|Δ0| -> n = #|Δ0| ->
    pred1_subst P Γ Δ Δ' σ τ ->
    on_ctx_free_vars P Δ ->
    All2_fold_over (pred1 Σ) Δ Δ' Δ0 Δ1 ->
    pred1_subst (shiftnP #|Γ'| P) (Γ ,,, Γ') (Δ ,,, Δ0) (Δ' ,,, Δ1) (up n σ) (up n τ).
  Proof.
    intros len' -> ps onΔ a.
    eapply pred1_subst_ext; tea. reflexivity.
    1-2:rewrite up_Upn //.
    eapply pred1_subst_Upn => //.
    apply (length_of a).
  Qed.
  Hint Resolve pred1_subst_up : pcuic.
  
  Ltac simpl_pred :=
    eapply simpl_pred;
    rewrite ?up_Upn;
    unfold Upn, Up, idsn;
    [autorewrite with sigma; reflexivity|
      autorewrite with sigma; reflexivity|].
  
  Lemma strong_substitutivity :
    let Pover (Γ Γ' : context) (Δ Δ' : context) :=
    pred1_ctx Σ Γ Γ' ->
    pred1_ctx_over Σ Γ Γ' Δ Δ' ->
    forall P Δ0 Δ'0 σ τ,
      on_ctx_free_vars P Δ0 ->
      pred1_subst P Γ Δ0 Δ'0 σ τ ->
      pred1_ctx_over Σ Δ0 Δ'0 (inst_context σ Δ) (inst_context τ Δ')
    in
    (forall Γ Γ' s t,
      pred1 Σ Γ Γ' s t ->
      forall P Δ Δ' σ τ,
      on_ctx_free_vars P Δ ->
      on_free_vars P s ->
      pred1_subst P Γ Δ Δ' σ τ ->
      pred1 Σ Δ Δ' s.[σ] t.[τ]) ×
    (forall Γ Γ' Δ Δ', Pover Γ Γ' Δ Δ').
  Proof.
    intros Pover.
    refine (pred1_ind_all_ctx Σ _ (fun Γ Γ' => pred1_ctx Σ Γ Γ')
       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); subst Pover;
      try (intros until Δ; intros Δ' σ τ onΔ ont Hrel); trivial; try inv_on_free_vars.

    (* induction redst using ; sigma; intros Δ Δ' σ τ Hσ Hτ Hrel. *)
    all:eauto 2 with pcuic.

    1:{ simpl.
        intros P ctx ctx' σ' τ' onctx ps.
        rewrite /inst_context.
        eapply All2_fold_fold_context_k, All2_fold_impl_ind; tea => /=.
        clear Hrel.
        intros.
        unfold on_decls_over in *.
        rewrite - !/(inst_context _ _).
        eapply X0; revgoals.
        (* + eapply Upn_ctxmap => //. eapply pres_bodies_inst_context.
        + eapply Upn_ctxmap => //. eapply pres_bodies_inst_context. *)
        + rewrite -(length_of X). eapply pred1_subst_Upn; len => //; tea.
          { apply (length_of X). }
          now eapply All2_fold_fold_context_k.
        + admit.
        + rewrite on_ctx_free_vars_app; len. rewrite addnP_shiftnP onctx.
          relativize #|par|; [erewrite on_free_vars_ctx_on_ctx_free_vars|]; len; trea.
          admit.
        }

    (** Beta case *)
    1:{ eapply simpl_pred; simpl; rewrite ?up_Upn; sigma; try reflexivity.
        move/andP: a => [] ont0 onb0.
        specialize (X2 P _ _ _ _ onΔ ont0 Hrel).
        specialize (X0 (shiftnP 1 P) (Δ ,, vass na t0.[σ]) (Δ' ,, vass na t1.[τ]) (⇑ σ) (⇑ τ)).
        forward X0. eapply on_ctx_free_vars_snoc_ass => //. admit.
        forward X0 by tas.
        forward X0. eapply pred1_subst_Up; auto.
        specialize (X4 P _ _ _ _ onΔ b Hrel).
        eapply (pred_beta _ _ _ _ _ _ _ _ _ _ X2 X0 X4). }

    (** Let-in delta case *)
    2:{ rewrite lift_rename rename_inst.
        simpl. rewrite lift_renaming_0. clear X0.
        destruct (nth_error_pred1_ctx _ _ X H) as [bodyΓ [? ?]]; eauto.
        move e after H.
        pose proof (pred1_pred1_ctx _ (snd (Hrel i))).
        destruct (nth_error Γ' i) eqn:HΓ'i; noconf H. hnf in H.
        destruct (nth_error Γ i) eqn:HΓi; noconf e. hnf in H.
        simpl_pred.
        
        
        pose proof (Hσ _ _ HΓi) as Hc. rewrite H in Hc.
        destruct Hc as [σi [b' [eqi' [Hnth Hb']]]].
        pose proof (Hτ _ _ HΓ'i) as Hc'. rewrite H0 in Hc'.
        destruct Hc' as [τi [b'' [eqi'' [Hnth' Hb'']]]].
        destruct (nth_error_pred1_ctx _ _ X0 Hnth') as [bodyΔ [? ?]].
        destruct (Hrel i) as [_ Hi]. rewrite HΓi in Hi. simpl in Hi. rewrite H in Hi.
        rewrite Hi in eqi'. rewrite eqi' in eqi''. noconf eqi''.
        simpl_pred.
        eapply refine_pred.
        now rewrite -ren_shiftk -Hb''.
        rewrite Hi eqi'. rewrite -lift0_inst. constructor. auto. auto. }

    (** Zeta *)
    1:{ sigma.
        econstructor; eauto.
        eapply X4; try apply Up_ctxmap; auto.
        apply pred1_subst_vdef_Up; auto. }

    - simpl. eapply Hrel.

    - simpl. rewrite inst_iota_red //.
      sigma. econstructor; eauto.
      + now eapply pred1_subst_pred1_ctx.
      + solve_all.
      + erewrite nth_error_map, H => //.
      + now len.
      + solve_all; red. red in b0.
        simpl. rewrite !mapi_context_inst.
        eapply b0 => //.
        rewrite !mapi_context_inst.
        red in b. cbn.
        eapply b; eauto with pcuic.
        eapply pred1_subst_ext.
        3:eapply pred1_subst_Upn; tea; len => //.
        1-3: sigma => //; now rewrite -(length_of a0).
        apply b0 => //.

    - sigma.
      unfold unfold_fix in *.
      destruct nth_error eqn:Heq; noconf H.
      assert (All2_fold (on_decls (on_decls_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { exact (X2 _ _ _ _ Hσ Hτ Hrel). }
      econstructor; eauto with pcuic.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_fix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_fix_subst. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?fix_subst_length //.
      + solve_all.

    - (* CoFix Case *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_fold (on_decls (on_decls_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { exact (X2 _ _ _ _ Hσ Hτ Hrel). }
      econstructor. eapply pred1_subst_pred1_ctx; eauto.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X11 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?cofix_subst_length //.
      + solve_all. (* args *)
      + simpl. solve_all.
      + eauto.
      + red in X7. red. simpl.
        rewrite !mapi_context_inst. eauto.
      + simpl. rewrite !mapi_context_inst.
        eapply X9; eauto with pcuic.
        eapply pred1_subst_ext.
        1-2:rewrite !up_Upn //.
        pose proof (length_of X6). rewrite H.
        eapply pred1_subst_Upn; len => //.
        eapply X7 => //.
      + solve_all; red; simpl; eauto; rewrite !mapi_context_inst; eauto.
        eapply b => //; eauto with pcuic.
        eapply pred1_subst_ext.
        1-2:rewrite !up_Upn //.
        pose proof (length_of a0). rewrite H.
        eapply pred1_subst_Upn; len => //.
        eapply b0 => //.

    - (* Proj Cofix *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_fold (on_decls (on_decls_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { exact (X2 _ _ _ _ Hσ Hτ Hrel). }
      econstructor. eapply pred1_subst_pred1_ctx; eauto.
      instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
      rewrite !inst_fix_context; auto.
      rewrite !inst_fix_context; auto.
      + clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b. rewrite -(fix_context_length mfix0); auto with pcuic.
        rewrite -(fix_context_length mfix1); auto with pcuic.
        rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'. simpl. intros. f_equal. apply map_ext. intros.
        apply map_def_eq_spec; auto. now sigma.
        rewrite Upn_comp ?map_length ?cofix_subst_length //.
      + solve_all. (* args *)

    - simpl. rewrite inst_closed0.
      rewrite closedn_subst_instance; auto.
      eapply declared_decl_closed in H; auto. hnf in H. rewrite H0 in H.
      rtoProp; auto.
      econstructor; eauto with pcuic.

    - (* Proj-Construct *)
      simpl. sigma. econstructor. pcuic. eapply All2_map. solve_all.
      rewrite nth_error_map. now rewrite H.

    - (* Lambda congruence *)
      sigma. econstructor. pcuic. eapply X2. eapply Up_ctxmap; pcuic.
      eapply Up_ctxmap; pcuic. now eapply pred1_subst_Up.

    - (* App congruence *)
      sigma; auto with pcuic.

    - (* Let congruence *)
      sigma. econstructor; eauto. eapply X4; try apply Up_ctxmap; auto.
      eapply pred1_subst_vdef_Up; eauto.

    - (* Case congruence *)
      simpl. econstructor; eauto with pcuic; unfold on_Trel; simpl; solve_all;
        rewrite !mapi_context_inst; eauto with pcuic.
      + eapply X5; eauto with pcuic.
        have len := length_of X2. rewrite len.
        eapply pred1_subst_up; len => //.
        eapply X3 => //.
      + eapply b; eauto with pcuic.
        have len := length_of a0. rewrite len.
        eapply pred1_subst_up; len => //.
        eapply b0 => //.

    - (* Proj congruence *)
      sigma; pcuic.

    - (* Fix congruence *)
      sigma.
      assert (All2_fold (on_decls (on_decls_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { exact (X2 _ _ _ _ Hσ Hτ Hrel). }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length X3).
      solve_all.
      unfold on_Trel in *. simpl. intuition auto.
      unfold on_Trel in *. simpl. intuition auto.
      eapply b; auto with pcuic.
      rewrite -{1}(fix_context_length mfix0). auto with pcuic.
      rewrite -{1}(fix_context_length mfix1). auto with pcuic.
      rewrite -H. apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* CoFix congruence *)
      sigma.
      assert (All2_fold (on_decls (on_decls_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { exact (X2 _ _ _ _ Hσ Hτ Hrel). }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length X3).
      solve_all.
      unfold on_Trel in *. simpl. intuition auto.
      unfold on_Trel in *. simpl. intuition auto.
      eapply b; auto with pcuic.
      rewrite -{1}(fix_context_length mfix0). auto with pcuic.
      rewrite -{1}(fix_context_length mfix1). auto with pcuic.
      rewrite -H. apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* Prod Congruence *)
      sigma. constructor; auto with pcuic;
      eapply X2; auto with pcuic; try eapply Up_ctxmap; auto with pcuic.
      apply pred1_subst_Up; auto.

    - sigma. simpl. constructor; auto with pcuic. solve_all.

    - rewrite !pred_atom_inst; auto. eapply pred1_refl_gen; auto with pcuic.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' Γ1 Δ1 Γ'1 s s' M N : wf Σ ->
    psubst Σ Γ Γ1 s s' Δ Δ1 ->
    #|Γ| = #|Γ1| -> #|Γ'| = #|Γ'1| ->
    All2_fold_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') (Γ1 ,,, Δ1 ,,, Γ'1) M N ->
    pred1 Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1) (subst s #|Γ'| M) (subst s' #|Γ'1| N).
  Proof.
    intros wfΣ Hs.
    remember (Γ ,,, Δ ,,, Γ') as Γl.
    remember (Γ1 ,,, Δ1 ,,, Γ'1) as Γr.
    intros Hlen Hlen' HΔ HΓ.
    revert HeqΓl Γ1 Δ1 Γ'1 s s' Hs HeqΓr Hlen Hlen' HΔ.
    revert Γ Δ Γ'.
    revert Γl Γr M N HΓ.
    set(P' :=
      fun (Γl Γr : context) =>
        forall (Γ Δ : context) (Γ' : list context_decl),
          Γl = Γ ,,, Δ ,,, Γ' ->
          forall (Γ1 : list context_decl) (Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
            psubst Σ Γ Γ1 s s' Δ Δ1 ->
            Γr = Γ1 ,,, Δ1 ,,, Γ'1 ->
            #|Γ| = #|Γ1| ->
            All2_fold_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
            pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)).
    set(Pover :=
    fun (Γl Γr : context) (Δl Δr : context) =>
      forall (Γ Δ : context) (Γ' : list context_decl),
        Γl = Γ ,,, Δ ,,, Γ' ->
        forall (Γ1 : list context_decl) (Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
          psubst Σ Γ Γ1 s s' Δ Δ1 ->
          Γr = Γ1 ,,, Δ1 ,,, Γ'1 ->
          #|Γ| = #|Γ1| ->
          All2_fold_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
          pred1_ctx_over Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)
            (subst_context s #|Γ'| Δl)
            (subst_context s' #|Γ'1| Δr)).

    refine (pred1_ind_all_ctx Σ _ P' Pover _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros;
      try subst Γ Γ'; 
      lazymatch goal with
      | |- context [tCase _ _ _ _] => idtac
      | |- _ => simplify_IH_hyps
      end; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try 
      
      specialize (forall_Γ _ _ _ eq_refl _ _ _
                               _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                              _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ1 _ _ _ eq_refl _ _ _
                           _ _ Hs eq_refl heq_length heq_length0 HΔ);
      try pose proof (All2_fold_length X0);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      red. intros. subst.
      pose proof (All2_fold_length X1).
      rewrite !app_context_length in H |- *.
      assert (#|Γ'0| = #|Γ'1|) by lia.
      eapply All2_fold_over_app. eapply All2_fold_app_inv in predΓ'.
      subst P'. intuition auto. typeclasses eauto with pcuic.
      now rewrite !app_context_length.
      eapply All2_fold_app_inv in X0 as [Xl Xr].
      2:{ rewrite !app_context_length. lia. }
      induction Xr; rewrite ?subst_context_snoc; constructor; pcuic. apply IHXr.
      + depelim predΓ'. all: hnf in H, H0. all: noconf H. noconf H0. auto.
      + depelim predΓ'. all: hnf in H, H0. all: noconf H. noconf H0. auto.
      + simpl in *. lia.
      + simpl in *.
        repeat red. rewrite !Nat.add_0_r.
        eapply All_decls_map, All_decls_impl; tea => /=.
        rewrite /on_decls_over. intros.
        eapply X0; eauto.

    - (* Reduction over *)
      subst Pover; simpl; intros.
      pose proof (length_of X4).
      assert (#|Γ'0| = #|Γ'1|) by (subst; len in H; lia).
      clear X0 X1 X2.
      rewrite - !mapi_context_subst.
      eapply All2_fold_mapi, All2_fold_impl_ind; tea.
      unfold on_decls_over; simpl. intros.
      pose proof (length_of X0).
      rewrite !mapi_context_subst /shiftf.
      subst Γ Γ'. rewrite - app_context_assoc in X1.
      specialize (X1 _ _ _ eq_refl).
      rewrite - app_context_assoc in X1.
      specialize (X1 _ _ _ _ _ X eq_refl H2).
      rewrite !subst_context_app !app_context_assoc in X1.
      len in X1; eapply X1. len in H. lia. exact X4.

    - (* Beta *)
      specialize (forall_Γ _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite distr_subst. simpl.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ _  (_ ,, _) eq_refl _ _ (_ ,, _)
                            _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      simpl. rewrite distr_subst.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ1.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      elim (leb_spec_Set); intros Hn.
      red in X0. specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
      destruct (nth_error s) eqn:Heq.
      ++ (* Let-bound variable in the substitution *)
         pose proof (nth_error_Some_length Heq).
         pose proof predΓ' as X.
         eapply psubst_nth_error in Heq as [decl [decl' [t' ?]]]; eauto.
         intuition; rename_all_hyps.
         destruct decl as [? [?|] ?]; destruct decl' as [? [?|] ?]; simpl in b; try contradiction.
         intuition subst.
         revert heq_option_map.
         rewrite -> nth_error_app_context_ge by lia.
         pose proof (nth_error_Some_length heq_nth_error1).
         rewrite -> nth_error_app_context_lt by lia.
         rewrite - heq_length0 heq_nth_error1 => [= <-].
         eapply weakening_pred1_pred1 in b0. 2:eauto. 2:eapply All2_fold_app_inv. 2:eapply X0.
         rewrite !subst_context_length in b0.
         rewrite <- subst_skipn'; try lia.
         now replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia. lia.
         revert heq_option_map.
         rewrite -> nth_error_app_context_ge by lia.
         pose proof (nth_error_Some_length heq_nth_error1).
         rewrite -> nth_error_app_context_lt by lia.
         rewrite - heq_length0 heq_nth_error1. simpl. congruence.

      ++ pose proof (psubst_length Hs).
         assert (#|Δ1| = #|s|).
         eapply psubst_nth_error_None in Hs; eauto. lia.
         eapply nth_error_None in Heq.
         subst P'.
         intuition; rename_all_hyps.
         (* Rel is a let-bound variable in Γ0, only weakening needed *)
         assert(eq:S i = #|s| + (S (i - #|s|))) by (lia). rewrite eq.
         rewrite simpl_subst'; try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_ge !subst_context_length /=; try lia.
         rewrite <- heq_option_map. f_equal.
         rewrite nth_error_app_context_ge /=; try lia.
         rewrite nth_error_app_context_ge /=; try lia.
         f_equal. lia.

      ++ (* Local variable from Γ'0 *)
         assert(eq: #|Γ'1| = #|Γ'1| - S i + S i) by lia. rewrite eq.
         rewrite <- (commut_lift_subst_rec body s' (S i) (#|Γ'1| - S i) 0); try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_lt /= in heq_option_map. autorewrite with wf; lia.
         rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
         rewrite nth_error_subst_context. rewrite option_map_decl_body_map_decl heq_option_map.
         simpl. do 3 f_equal. lia.

    - specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
      rewrite {1}heq_length0. elim (leb_spec_Set); intros Hn.
      + subst P'. intuition; subst; rename_all_hyps.
        pose proof (psubst_length Hs).
        destruct nth_error eqn:Heq.
        ++ eapply psubst_nth_error' in Heq as [t' [? ?]]; eauto.
           rewrite - heq_length0 e.
           rewrite - {1}(subst_context_length s 0 Γ'0).
           rewrite {1}heq_length0 -(subst_context_length s' 0 Γ'1).
           eapply weakening_pred1_pred1; auto. eapply All2_fold_over_pred1_ctx.
           now rewrite !subst_context_length. auto.
        ++ eapply psubst_nth_error_None in Heq; eauto.
           intuition; rename_all_hyps.
           rewrite - heq_length0 heq_nth_error.
           eapply psubst_length' in Hs.
           assert(#|s| = #|s'|) as -> by lia.
           eauto with pcuic.
      + constructor. auto.

    - rewrite subst_iota_red //.
      autorewrite with subst.
      econstructor; eauto.
      * apply All2_map. solve_all.
      * now erewrite nth_error_map, heq_nth_error.
      * now len.
      * solve_all; red; cbn.
        { now rewrite !mapi_context_subst. }
        specialize (b1 Γ0 Δ (Γ'0 ,,, bcontext x) ltac:(rewrite app_context_assoc //)).
        specialize (b1 Γ1 Δ1 (Γ'1 ,,, bcontext y) _ _ Hs ltac:(rewrite app_context_assoc //)
          heq_length0).
        forward b1. { now len; rewrite (length_of a0). }
        len in b1. rewrite !mapi_context_subst.
        now rewrite !subst_context_app in b1; len in b1; rewrite !app_context_assoc in b1.

    - autorewrite with subst. simpl.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix.
      econstructor; auto with pcuic.
      * eapply X0; eauto with pcuic.
      * rewrite !subst_fix_context.
        erewrite subst_fix_context.
        now eapply X2.
      * apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                              ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length
          in forall_Γ0. pose proof (All2_fold_length X1).
        forward forall_Γ0. lia. specialize (forall_Γ0 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
            !Nat.add_0_r !app_context_assoc in forall_Γ0.
      * unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite (map_fix_subst (fun k => subst s' (k + #|Γ'1|))).
        intros. reflexivity. simpl.
        now rewrite (distr_subst_rec _ _ _ _ 0) fix_subst_length.
      * apply subst_is_constructor; auto.
      * eapply All2_map. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix.
      econstructor; eauto.
      * rewrite !subst_fix_context.
        erewrite subst_fix_context.
        now eapply X2.
      * apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ1 _ _ (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ1 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                              ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length in forall_Γ1.
        pose proof (All2_fold_length X1).
        forward forall_Γ1. lia. specialize (forall_Γ1 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
            !Nat.add_0_r !app_context_assoc in forall_Γ1.
      * unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
        intros. reflexivity. simpl.
        now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.

      * eapply All2_map. solve_all.
      * eapply All2_map. solve_all.
      * red; cbn. rewrite !mapi_context_subst.
        now eapply X7.
      * cbn. rewrite !mapi_context_subst.
        have lenpctx := length_of X6.
        have len' := length_of predΓ'. len in len'.
        clear -heq_length lenpctx len' forall_Γ Hs HΔ.
        specialize (forall_Γ _ _ (Γ'0 ,,, pcontext p0)
            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ _ _ (Γ'1 ,,, pcontext p1) _ _ Hs
            ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !subst_context_app !app_context_assoc in forall_Γ; len in forall_Γ.
        eapply forall_Γ.
        { move: (length_of HΔ). lia. }
        exact HΔ.

      * solve_all; red; cbn; rewrite !mapi_context_subst.
        + now eapply b0.
        + rename_all_hyps.
          have lenbctx := length_of a0.
          have len' := length_of predΓ'. len in len'.
          clear -heq_length lenbctx len' forall_Γ0 Hs HΔ.
          specialize (forall_Γ0 _ _ (Γ'0 ,,, bcontext x)
            ltac:(now rewrite app_context_assoc)).
          specialize (forall_Γ0 _ _ (Γ'1 ,,, bcontext y) _ _ Hs
            ltac:(now rewrite app_context_assoc) heq_length).
          rewrite !subst_context_app !app_context_assoc in forall_Γ0; len in forall_Γ0.
          eapply forall_Γ0.
          { move: (length_of HΔ). lia. }
          exact HΔ.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor.
      * red in X0. eauto 1 with pcuic. unshelve eapply X0. 1-2:shelve.
        all:eauto.
      * rewrite !subst_fix_context.
        erewrite subst_fix_context.
        now eapply X2.
      * apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                              ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length in forall_Γ0. pose proof (All2_fold_length X1).
        forward forall_Γ0. lia. specialize (forall_Γ0 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
            !Nat.add_0_r !app_context_assoc in forall_Γ0.
      * unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
        intros. reflexivity. simpl.
        now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.
      * eapply All2_map. solve_all.

    - pose proof (subst_declared_constant (empty_ext Σ) _ _ s' #|Γ'0| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite heq_length0 in H0. rewrite H0.
      econstructor; eauto.

    - autorewrite with subst. simpl.
      econstructor; eauto.
      eapply All2_map. solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor; eauto.
      * eapply All2_map; solve_all.
      * red; cbn; rewrite !mapi_context_subst.
        now eapply X3.
      * cbn; rewrite !mapi_context_subst.
        have lenpctx := length_of X2.
        have len' := length_of predΓ'. len in len'.
        clear -heq_length lenpctx len' forall_Γ Hs HΔ.
        specialize (forall_Γ _ _ (Γ'0 ,,, pcontext p0)
            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ _ _ (Γ'1 ,,, pcontext p1) _ _ Hs
            ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !subst_context_app !app_context_assoc in forall_Γ; len in forall_Γ.
        eapply forall_Γ.
        { move: (length_of HΔ). lia. }
        exact HΔ.
      * eapply All2_map; solve_all; red; cbn; rewrite !mapi_context_subst.
        + now eapply b0.
        + have lenbctx := length_of a0.
          have len' := length_of predΓ'. len in len'.
          clear -heq_length lenbctx len' b1 Hs HΔ.
          specialize (b1 _ _ (Γ'0 ,,, bcontext x)
              ltac:(now rewrite app_context_assoc)
              _ _ (Γ'1 ,,, bcontext y) _ _ Hs
            ltac:(now rewrite app_context_assoc) heq_length).
          rewrite !subst_context_app !app_context_assoc in b1; len in b1.
          eapply b1. { move: (length_of HΔ); lia. }
          exact HΔ.
    - econstructor; eauto.
      { rewrite !subst_fix_context. now eapply X2. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - econstructor; eauto.
      { rewrite !subst_fix_context. now eapply X2. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                              _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_env} {Γ Δ M M' na na' A A' N N'} :
    wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vass na A) (Δ ,, vass na' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] Δ [vass na' A'] [] [M] [M'] N N' wfΣ) as H.
    forward H.
    - constructor; auto with pcuic.
      forward H by pcuic.
      + constructor; pcuic. apply pred1_pred1_ctx in redN.
        depelim redN. pcuic. now depelim a.
      + simpl in H |- *. apply pred1_pred1_ctx in redN; pcuic.
        depelim redN; pcuic. now depelim a.
    - pose proof (pred1_pred1_ctx _ redN). depelim X.
      apply H; pcuic.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ Δ na na' M M' A A' N N'} : wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vdef na M A) (Δ ,, vdef na' M' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] Δ [vdef na' M' A'] [] [M] [M'] N N' wfΣ) as H.
    pose proof (pred1_pred1_ctx _ redN). depelim X. depelim a.
    forward H.
    - pose proof (psubst_vdef Σ Γ Δ [] [] [] [] na na M M' A A').
      rewrite !subst_empty in X0. apply X0; pcuic.
    - apply H; pcuic.
      econstructor; auto with pcuic. constructor; auto.
  Qed.

End ParallelSubstitution.
