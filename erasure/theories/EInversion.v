(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR PCUICValidity.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ETyping EWcbvEval Extract Prelim.

From Equations Require Import Equations.

Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance default_checker_flags.

(** ** Inversion on eval *)

Lemma type_Case_inv (Σ : global_env_ext) (hΣ : wf Σ.1) Γ ind npar p c brs T :
  Σ;;; Γ |- PCUICAst.tCase (ind, npar) p c brs : T ->
  { '(u, args, mdecl, idecl, pty, indctx, pctx, ps, btys) : _ &
         (PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl) *
         (PCUICAst.ind_npars mdecl = npar) *
         let pars := firstn npar args in
         (Σ;;; Γ |- p : pty) *
         (types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys)) *
         (check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx) *
         (existsb (leb_sort_family (universe_family ps)) (PCUICAst.ind_kelim idecl)) *
         (Σ;;; Γ |- c : PCUICAst.mkApps (tInd ind u) args) *
         (All2 (fun x y : nat * PCUICAst.term => ((fst x = fst y) * (Σ;;; Γ |- snd x : snd y)) * (Σ ;;; Γ |- snd y : tSort ps)) brs btys) *
         (Σ ;;; Γ |- PCUICAst.mkApps p (skipn npar args ++ [c])  <= T)}%type.
Proof.
  intros. dependent induction X.
  - unshelve eexists.
    + repeat refine (_,_). all:shelve.
    + cbn. subst pars. intuition eauto.
  - edestruct (IHX hΣ _ _ _ _ _ eq_refl) as [ [[[[[[[[]]]]]]]] ].
    repeat match goal with [ H : _ * _ |- _ ] => destruct H end.
    unshelve eexists.
    + repeat refine (_, _). all:shelve.
    + cbn. intuition eauto.
      all: eapply PCUICConversion.cumul_trans; eauto.
Qed.

Notation type_Construct_inv := PCUICInversion.inversion_Construct.
Notation type_tFix_inv := PCUICInversion.inversion_Fix.

Derive Signature for Forall2.
Lemma eval_box_apps:
  forall (Σ' : list E.global_decl) (e : E.term) (x x' : list E.term),
    Forall2 (eval Σ') x x' ->
    eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2. revert e H2; induction x using rev_ind; cbn; intros; eauto using eval.
  eapply Forall2_app_inv_l in H as [l1' [l2' [H [H' eq]]]]. subst H2.
  depelim H'.
  specialize (IHx e _ H H0). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
