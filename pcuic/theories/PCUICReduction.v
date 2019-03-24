(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed.
Require Import ssreflect ssrbool.
Require Import String.
Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  induction 2. econstructor; auto. constructor. apply X.
  econstructor 2; eauto.
Qed.

Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Lemma red_alt@{i j +} Σ Γ t u : red Σ Γ t u <~> clos_refl_trans@{i j} (red1 Σ Γ) t u.
Proof.
  split. intros H. apply clos_rt_rtn1_iff.
  induction H; econstructor; eauto.
  intros H. apply clos_rt_rtn1_iff in H.
  induction H; econstructor; eauto.
Qed.

(** Atoms do not reduce *)

Definition atom t :=
  match t with
  | tVar _
  | tMeta _
  | tSort _
  | tInd _ _
  | tConstruct _ _ _ => true
  | _ => false
  end.

Section ParallelReduction.
  Context (Σ : global_declarations).

  Inductive pred1 (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t b0 b1 a0 a1 :
      pred1 Γ b0 b1 -> pred1 Γ a0 a1 ->
      pred1 Γ (tApp (tLambda na t b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t b0 b1 :
      pred1 Γ d0 d1 -> pred1 Γ b0 b1 ->
      pred1 Γ (tLetIn na d0 t b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def i body body' :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      pred1 Γ (lift0 (S i) body) body' ->
      pred1 Γ (tRel i) body'

  | pred_rel_assum i :
      option_map decl_body (nth_error Γ i) = Some None ->
      pred1 Γ (tRel i) (tRel i)

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2 (pred1 Γ) args0 args1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix idx args0 args1 narg fn0 fn1 :
      unfold_fix mfix idx = Some (narg, fn0) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix idx args0 args1 narg fn0 fn1 brs0 brs1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ p0 p1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0)
            (tCase ip (mkApps fn1 args1) p1 brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix idx args0 args1 narg fn0 fn1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (tProj p (mkApps (tCoFix mfix idx) args0))
            (tProj p (mkApps fn1 args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      pred1 Γ (tConst c u) (subst_instance_constr u body)

  | pred_axiom c decl (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = None ->
      pred1 Γ (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg args k u args0 args1 arg1 :
      All2 (pred1 Γ) args0 args1 ->
      nth_error args (pars + narg) = Some arg1 ->
      pred1 Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ M M' -> pred1 (Γ ,, vass na M) N N' ->
                            pred1 Γ (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ M0 M1 ->
      pred1 Γ N0 N1 ->
      pred1 Γ (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)
  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ d0 d1 -> pred1 Γ t0 t1 -> pred1 (Γ ,, vdef na d0 t0) b0 b1 ->
      pred1 Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ p0 p1 ->
      pred1 Γ c0 c1 ->
      All2 (on_Trel (pred1 Γ) snd) brs0 brs1 ->
      pred1 Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' : pred1 Γ c c' -> pred1 Γ (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (pred1 Γ (dtype d0) (dtype d1)) *
                         (pred1 (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      pred1 Γ (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2 (fun d0 d1 => (pred1 Γ (dtype d0) (dtype d1)) *
                            (pred1 (Γ ,,, fix_context mfix0) (dbody d0) (dbody d1)))%type mfix0 mfix1 ->
      pred1 Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ M0 M1 -> pred1 (Γ ,, vass na M0) N0 N1 ->
                               pred1 Γ (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' : All2 (pred1 Γ) l l' -> pred1 Γ (tEvar ev l) (tEvar ev l')

  | pred_atom t : atom t -> pred1 Γ t t.

  Lemma pred1_refl Γ t : pred1 Γ t t.
  Proof.
    induction t in Γ |- * using term_forall_list_ind;
      try solve [(apply pred_atom; reflexivity) || constructor; auto].
    constructor. solve_all; eapply All_Forall2; eauto. simpl. auto.
    econstructor; auto. solve_all. eapply All_Forall2; eauto. simpl; auto.
    constructor; eauto. red in H. solve_all. eapply All_Forall2; eauto. simpl; intuition auto.
    red. auto.
    constructor; eauto. red in H. solve_all. eapply All_Forall2; eauto. simpl; intuition auto.
    constructor; eauto. red in H. solve_all. eapply All_Forall2; eauto. simpl; intuition auto.
  Qed.

  Hint Constructors pred1 : pred.
  Hint Resolve pred1_refl : pred.

  Lemma Forall2_same {A} (P : A -> A -> Prop) l : (forall x, P x x) -> Forall2 P l l.
  Proof. induction l; constructor; auto. Qed.

  Hint Resolve Forall2_same : pred.
  Hint Unfold on_rel snd on_snd : pred.

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Γ M N.
    induction 1 using red1_ind_all; intros; eauto with pred.

    constructor; auto with pred.
    induction H. intuition. constructor; auto with pred.
    admit.

    constructor. auto with pred.
    induction H. constructor; intuition auto with pred.
    constructor; auto with pred.
    constructor; auto with pred.

    induction H; constructor; intuition auto with pred.

    constructor.
    generalize (fix_context mfix0).
    induction H; constructor; intuition auto with pred.
    rewrite H1; auto with pred.

    constructor.
    revert H.
    generalize (fix_context mfix0).
    induction 1; constructor; intuition auto with pred.
    rewrite H1; auto with pred.

    constructor.
    generalize (fix_context mfix0).
    induction H; constructor; intuition auto with pred.
    rewrite H1; auto with pred.

    constructor.
    revert H.
    generalize (fix_context mfix0).
    induction 1; constructor; intuition auto with pred.
    rewrite H1; auto with pred.
  Admitted.

  Lemma pred1_red Γ : forall M N, pred1 Γ M N -> red Σ Γ M N.
  Proof.
    induction 1; try constructor; auto with pred.
  Admitted.

End ParallelReduction.

Lemma substitution_pred1 `{cf:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ -> All Ast.wf s -> subs Σ Γ s Γ' -> wf_local Σ Γ -> Ast.wf M ->
  wf_local Σ (Γ ,,, Γ' ,,, Γ'') ->
  pred1 (fst Σ) (Γ ,,, Γ' ,,, Γ'') M N ->
  pred1 (fst Σ) (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  intros.
  induction H1. constructor.
  econstructor 2; eauto.
  eapply substitution_red1; eauto.
  eapply wf_red_wf. 4:eauto. all:eauto.
Qed.
