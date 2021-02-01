(* Distributed under the terms of the MIT license. *)
Require Import RelationClasses CRelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICUtils PCUICAst PCUICAstUtils PCUICSize PCUICCases
     PCUICLiftSubst PCUICUnivSubst PCUICReduction PCUICTyping
     PCUICSigmaCalculus PCUICWeakeningEnv PCUICInduction
     PCUICRename PCUICInst
     PCUICWeakening PCUICSubstitution.

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
  | pred_iota ci c u args0 args1 p0 brs0 brs1 br :
      pred1_ctx Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error brs1 c = Some br -> 
      #|skipn (ci_npar ci) args1| = context_assumptions br.(bcontext) ->
      All2 (fun br br' => 
        on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
        on_Trel (pred1 (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
         bbody br br') brs0 brs1 ->
      pred1 Γ Γ' (tCase ci p0 (mkApps (tConstruct ci.(ci_ind) c u) args0) brs0)
            (iota_red ci.(ci_npar) args1 br)

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
      on_Trel (pred1_ctx_over Γ Γ') pcontext p0 p1 ->
      pred1 (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
      All2 (fun br br' => 
        on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
        on_Trel (pred1 (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
         bbody br br') brs0 brs1 ->
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
      on_Trel (pred1_ctx_over Γ Γ') pcontext p0 p1 ->
      pred1 (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
      All2 (fun br br' => 
        on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
        on_Trel (pred1 (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
           bbody br br') brs0 brs1 ->
      pred1 Γ Γ' c0 c1 ->
      pred1 Γ Γ' (tCase ci p0 c0 brs0) (tCase ci p1 c1 brs1)

  (* | pred_case_refl ci p c brs :
    (** We add a specific trivial reflexivity rule for tCase to ensure the relation 
        is reflexive on *any* term (even ill-formed ones), to simplify the
        development. Otherwise we would have to reason on the shapes of the
        case_predicate_context/case_branch_context everywhere. *)
    pred1_ctx Γ Γ' ->
    pred1 Γ Γ' (tCase ci p c brs) (tCase ci p c brs) *)

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
      (forall Γ Γ' ci c u args0 args1 p0 brs0 brs1 br,
          pred1_ctx Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2 (fun br br' => 
            (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
             on_Trel (Pctxover Γ Γ') bcontext br br') × 
            on_Trel (P' (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
                bbody br br') brs0 brs1 ->
          nth_error brs1 c = Some br -> 
          #|skipn (ci_npar ci) args1| = context_assumptions br.(bcontext) ->
          P Γ Γ' (tCase ci p0 (mkApps (tConstruct ci.(ci_ind) c u) args0) brs0)
                (iota_red ci.(ci_npar) args1 br)) ->

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
          on_Trel (pred1_ctx_over Γ Γ') pcontext p0 p1 ->
          on_Trel (Pctxover Γ Γ') pcontext p0 p1 -> 
          pred1 (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          P (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          All2 (fun br br' => 
            (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
             on_Trel (Pctxover Γ Γ') bcontext br br') × 
            on_Trel (P' (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
                bbody br br') brs0 brs1 ->
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
          on_Trel (pred1_ctx_over Γ Γ') pcontext p0 p1 ->
          on_Trel (Pctxover Γ Γ') pcontext p0 p1 -> 
          pred1 (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          P (Γ ,,, p0.(pcontext)) (Γ' ,,, p1.(pcontext)) p0.(preturn) p1.(preturn) ->
          All2 (fun br br' => 
            (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' ×
             on_Trel (Pctxover Γ Γ') bcontext br br') × 
              on_Trel (P' (Γ ,,, br.(bcontext)) (Γ' ,,, br'.(bcontext)))
                bbody br br') brs0 brs1 ->
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
      forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof using Σ.
    intros P Pctx Pctxover P' Hctx Hctxover. intros. 
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
    - eapply (All2_branch_prop
        (P:=fun Γ Γ' br br' =>
        on_Trel (pred1_ctx_over Γ Γ') bcontext br br' *
        on_Trel (pred1 (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
        (Q:=fun Γ Γ' br br' => 
          (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' × 
            on_Trel (Pctxover Γ Γ') bcontext br br') *
          on_Trel (P' (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
         a1).
      intros x y []. split; auto. split => //.
      * apply Hctxover => //. 
        apply (All2_fold_impl a aux).
        apply (Hctx _ _ a), (All2_fold_impl a aux).
        apply (All2_fold_impl o (extend_over aux Γ Γ')).
      * apply (extendP aux _ _). exact o0.
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
        o (All2_fold_impl o (extend_over aux Γ Γ'))).
      * eapply (All2_branch_prop
          (P:=fun Γ Γ' br br' =>
          on_Trel (pred1_ctx_over Γ Γ') bcontext br br' *
          on_Trel (pred1 (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
          (Q:=fun Γ Γ' br br' => 
            (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' × 
              on_Trel (Pctxover Γ Γ') bcontext br br') *
            on_Trel (P' (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
          a4).        
        intros x y []. 
        split; auto. split => //.
        + apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
            (Hctx _ _ a (All2_fold_impl a aux)) o0 (All2_fold_impl o0 (extend_over aux Γ Γ'))).
        + apply (extendP aux _ _). exact o1.
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
        (Hctx _ _ a (All2_fold_impl a aux)) o (All2_fold_impl o (extend_over aux Γ Γ'))).
    - eapply (All2_branch_prop
          (P:=fun Γ Γ' br br' =>
          on_Trel (pred1_ctx_over Γ Γ') bcontext br br' *
          on_Trel (pred1 (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
          (Q:=fun Γ Γ' br br' => 
            (on_Trel (pred1_ctx_over Γ Γ') bcontext br br' × 
              on_Trel (Pctxover Γ Γ') bcontext br br') *
            on_Trel (P' (Γ,,, bcontext br) (Γ',,, bcontext br')) bbody br br')
          a1).        
        intros x y []. 
        split; auto. split => //.
        + apply (Hctxover _ _ _ _ a (All2_fold_impl a aux)
            (Hctx _ _ a (All2_fold_impl a aux)) o0 (All2_fold_impl o0 (extend_over aux Γ Γ'))).
        + apply (extendP aux _ _). exact o1.
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
  Defined.

  Lemma pred1_pred1_ctx {Γ Δ t u} : pred1 Γ Δ t u -> pred1_ctx Γ Δ.
  Proof.
    intros H; revert Γ Δ t u H.
    refine (pred1_ind_all_ctx _ (fun Γ Γ' => pred1_ctx Γ Γ')
      (fun Γ Γ' Δ Δ' => True)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
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

  Hint Constructors All_decls : pcuic.

  Lemma pred1_refl_gen Γ Γ' t : pred1_ctx Γ Γ' -> pred1 Γ Γ' t t.
  Proof.
    revert Γ'.
    revert Γ t.
    apply: term_forall_ctx_list_ind;
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
      * apply onctx_rel_pred1_refl => //.
      * eapply b0.
        eapply All2_fold_app => //.
        eapply onctx_rel_pred1_refl => //.
      * eapply All_All2; tea; solve_all.
        + apply onctx_rel_pred1_refl => //.
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

  Lemma lift_iota_red n k pars args br :
    #|skipn pars args| = context_assumptions br.(bcontext) ->
    lift n k (iota_red pars args br) =
    iota_red pars (List.map (lift n k) args) (map_branch_k (lift n) k br).
  Proof.
    intros hctx. rewrite !lift_rename'. rewrite rename_iota_red //.
    f_equal; try setoid_rewrite <-lift_rename => //.
    unfold map_branch_k, rename_branch, map_branch_shift.
    f_equal.
    * rewrite /shiftf. setoid_rewrite lift_rename'.
      now setoid_rewrite shiftn_lift_renaming.
    * simpl. now rewrite lift_rename' shiftn_lift_renaming.
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

  Lemma weakening_pred1 Σ Γ Γ' Γ'' Δ Δ' Δ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') M N ->
    #|Γ| = #|Δ| ->
    All2_fold_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
          (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
          (lift #|Γ''| #|Γ'| M) (lift #|Δ''| #|Δ'| N).
  Proof.
    intros wfΣ H.

    remember (Γ ,,, Γ') as Γ0.
    remember (Δ ,,, Δ') as Δ0.
    intros HΓ.
    revert Γ Γ' HeqΓ0 Δ Δ' HeqΔ0 HΓ Γ'' Δ''.
    revert Γ0 Δ0 M N H.

    set (Pctx :=
           fun (Γ0 Δ0 : context) =>
             forall Γ Γ' : context,
               Γ0 = Γ ,,, Γ' ->
               forall Δ Δ' : context,
                 Δ0 = Δ ,,, Δ' ->
                 #|Γ| = #|Δ| ->
           forall Γ'' Δ'' : context,
             All2_fold_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
             pred1_ctx Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')).

    set (Pctxover :=
      fun (Γ0 Δ0 : context) (ctx ctx' : context) =>
        forall Γ Γ' : context,
          Γ0 = Γ ,,, Γ'  ->
          forall Δ Δ' : context,
            Δ0 = Δ ,,, Δ' ->
            #|Γ| = #|Δ| ->
      forall Γ'' Δ'' : context,
      All2_fold_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
      pred1_ctx_over Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') 
                  (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
                  (lift_context #|Γ''| #|Γ'| ctx) 
                  (lift_context #|Δ''| #|Δ'| ctx')).
  
      refine (pred1_ind_all_ctx Σ _ Pctx Pctxover _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros; subst Pctx
        Pctxover;
        rename_all_hyps; try subst Γ Γ'; 
        lazymatch goal with
        | |- context [tCase _ _ _ _] => idtac
        | |- _ => simplify_IH_hyps
        end; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try pose proof (All2_fold_length X0);
      try specialize (X0 _ _ eq_refl _ _ eq_refl heq_length _ _ ltac:(eauto));
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      intros. subst.
      eapply All2_fold_over_app.
      + eapply All2_fold_over_app; pcuic.
      + eapply All2_fold_app_inv in X0; auto.
        destruct X0.
        induction a0; rewrite ?lift_context_snoc0; cbn; constructor; pcuic.
        * apply IHa0.
          -- depelim predΓ'.
             ++ assumption.
          -- unfold ",,,". lia.
        * rewrite !Nat.add_0_r.
          eapply All_decls_map, All_decls_impl; tea.
          intuition auto. unfold on_decls_over.
          eapply X0 => //.

    - intros.
      rewrite - !mapi_context_lift.
      apply All2_fold_mapi. simpl. clear X0 X1 X2.
      eapply All2_fold_impl; tea.
      intros. red in X0.
      rewrite !mapi_context_lift /shiftf.
      subst Γ Γ'.
      rewrite - !app_context_assoc in X0.
      specialize (X0 _ _ eq_refl _ _ eq_refl H2 _ _ X).
      red.
      now rewrite !lift_context_app in X0; len in X0; rewrite !app_context_assoc in X0.

    - (* Beta *)
      specialize (forall_Γ _ (Γ'0,, vass na t0) eq_refl _ (Δ' ,, vass na t1) eq_refl heq_length _ _ X5).
      specialize (forall_Γ1 heq_length _ _ X5).
      econstructor; now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ (Γ'0,, vdef na d0 t0) eq_refl _ (Δ',, vdef na d1 t1)
                            eq_refl heq_length _ _ X5).
      simpl. econstructor; eauto.
      now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.

    - (* Rel unfold *)
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      elim (leb_spec_Set); intros Hn.
      + destruct nth_error eqn:Heq; noconf heq_option_map.
        pose proof (nth_error_Some_length Heq).
        rewrite !app_context_length in H1.
        assert (#|Γ'0| = #|Δ'|). pcuic. eapply All2_fold_app_inv in predΓ' as [? ?].
        now eapply All2_fold_length in a0. auto.
        rewrite simpl_lift; try lia.
        rewrite - {2}H0.
        assert (#|Γ''| + S i = S (#|Γ''| + i)) as -> by lia.
        econstructor; auto.
        rewrite H0. rewrite <- weaken_nth_error_ge; auto. rewrite Heq.
        simpl in H. simpl. f_equal. auto.
        lia.

      + (* Local variable *)
        pose proof (All2_fold_length predΓ'). rewrite !app_context_length in H0.
        rewrite <- lift_simpl; pcuic.
        econstructor; auto.
        rewrite (weaken_nth_error_lt); try lia.
        now rewrite option_map_decl_body_map_decl heq_option_map.

    - (* Rel refl *)
      pose proof (All2_fold_length predΓ').
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      rewrite !app_context_length in H.
      assert (#|Γ'0| = #|Δ'|) by lia. rewrite H1.
      elim (leb_spec_Set); intros Hn. rewrite H0. econstructor.
      rewrite -{1}H0.
      eapply X0; eauto.
      now constructor.

    - (* iota reduction *) 
      assert(#|Γ''| = #|Δ''|). pcuic.
      simplify_IH_hyps.
      pose proof (All2_fold_length predΓ').
      specialize (X0 heq_length0).
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      rewrite lift_mkApps /=.
      rewrite lift_iota_red //.
      specialize (X0 _ _ X3).
      eapply (pred_iota _ _ _ _ _ _ _ _ _ _
        (map_branches_k (lift #|Δ''|) #|Δ'| brs1)); solve_all.
      * now rewrite nth_error_map heq_nth_error.
      * now len.
      * red. simpl.
        specialize (b0 _ _ eq_refl _ _ eq_refl heq_length0 _ _ X3).
        now rewrite !mapi_context_lift. 
      * specialize (b1 Γ0 (Γ'0 ,,, bcontext x) ltac:(rewrite app_context_assoc //)).
        specialize (b1 Δ (Δ' ,,, bcontext y) ltac:(rewrite app_context_assoc //) heq_length0 _ _ X3).
        len in b1. red. simpl. rewrite !mapi_context_lift.
        now rewrite !lift_context_app in b1; len in b1; rewrite !app_context_assoc in b1.
      
    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_fold_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix. simpl.
      econstructor; pcuic.
      rewrite !lift_fix_context.
      erewrite lift_fix_context.
      eapply X2 => //.
      apply All2_map. clear X4. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.
      unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite distr_lift_subst. rewrite fix_subst_length. f_equal.
      now rewrite (map_fix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      eapply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_fold_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix.
      simpl.
      econstructor. all:try solve [pcuic].
      * simplify_IH_hyps. simpl in *.
        rewrite !lift_fix_context.
        erewrite lift_fix_context.
        now eapply X2.
      * apply All2_map. clear X2 X6 X5 X4. simpl. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ2 Γ0 (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ2 Δ (Δ' ,,, fix_context mfix1)
                              ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
                !app_context_assoc in forall_Γ2.
        now rewrite !lift_fix_context.
      * unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
        now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      * eapply All2_map. solve_all.
      * eapply All2_map. solve_all.
      * red. simpl. rewrite !mapi_context_lift /shiftf.
        now eapply X7.
      * simpl.
        rewrite !mapi_context_lift.
        specialize (forall_Γ Γ0 
          (Γ'0 ,,, pcontext p0)
          ltac:(now rewrite app_context_assoc) 
          Δ (Δ' ,,, pcontext p1)
          ltac:(now rewrite app_context_assoc) heq_length _ _ X11).
        rewrite !lift_context_app Nat.add_0_r !app_context_assoc in forall_Γ.
        now len in forall_Γ.
      * solve_all; red; cbn.
        + rewrite !mapi_context_lift.
          now eapply b0.
        + rewrite !mapi_context_lift.
           specialize (b1 Γ0
          (Γ'0 ,,, bcontext x)
          ltac:(now rewrite app_context_assoc) 
          Δ (Δ' ,,, bcontext y)
          ltac:(now rewrite app_context_assoc) heq_length _ _ X11).
          rewrite !lift_context_app Nat.add_0_r !app_context_assoc in b1.
          now len in b1.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_fold_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      rewrite !lift_fix_context.
      erewrite lift_fix_context.
      now eapply X2.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.
      unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
      now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      eapply All2_map. solve_all.

    - assert(Hlen:#|Γ''| = #|Δ''|). eapply All2_fold_length in X1; pcuic.
      pose proof (lift_declared_constant _ _ _ #|Δ''| #|Δ'| wfΣ H).
      rewrite -subst_instance_lift. 
      econstructor; eauto.
      rewrite H0.
      now rewrite - !map_cst_body heq_cst_body.

    - simpl. eapply pred_proj with (map (lift #|Δ''| #|Δ'|) args1). auto.
      eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X5).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - assert(Hlen:#|Γ''| = #|Δ''|). eapply All2_fold_length in X9; pcuic.
      assert(Hlen':#|Γ'0| = #|Δ'|).
      { eapply All2_fold_length in predΓ'; pcuic.
        len in predΓ'; pcuic. }
      econstructor; pcuic.
      * eapply All2_map; solve_all.
      * simpl. now rewrite !mapi_context_lift.
      * specialize (forall_Γ Γ0 (Γ'0 ,,, pcontext p0) ltac:(rewrite app_context_assoc //)).
        specialize (forall_Γ Δ (Δ' ,,, pcontext p1) ltac:(rewrite app_context_assoc //)
          heq_length _ _ X9).
        rewrite !lift_context_app !Nat.add_0_r !app_context_assoc in forall_Γ.
        rewrite !mapi_context_lift.
        simpl. now len in forall_Γ.
      * solve_all.
        + red; simpl. rewrite !mapi_context_lift.
          now eapply b0.
        + rewrite !mapi_context_lift.
          specialize (b1 Γ0 (Γ'0 ,,, bcontext x) ltac:(rewrite app_context_assoc //)).
          specialize (b1 Δ (Δ' ,,, bcontext y) ltac:(rewrite app_context_assoc //)
            heq_length _ _ X9).
          rewrite !lift_context_app !Nat.add_0_r !app_context_assoc in b1.
          now len in b1.

    - assert(Hlen:#|Γ''| = #|Δ''|). eapply All2_fold_length in X4; pcuic.
      constructor; eauto.
      * rewrite !lift_fix_context. now eapply X2.
      * apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                              ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
                !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.
    
    - econstructor; pcuic.
      * rewrite !lift_fix_context. now eapply X2.
      * apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                              ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                              ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
                !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.

    - specialize (forall_Γ0 Γ0 (Γ'0 ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Lemma weakening_pred1_pred1 Σ Γ Δ Γ' Δ' M N : wf Σ ->
    All2_fold_over (pred1 Σ) Γ Δ Γ' Δ' ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 #|Γ'| M) (lift0 #|Δ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Δ' M N); eauto.
    eapply pred1_pred1_ctx in X1. pcuic.
  Qed.

  Lemma weakening_pred1_0 Σ Γ Δ Γ' M N : wf Σ ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Γ' M N); eauto.
    eapply pred1_pred1_ctx in X0. pcuic.
    eapply pred1_pred1_ctx in X0.
    apply All2_fold_over_refl; auto.
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
