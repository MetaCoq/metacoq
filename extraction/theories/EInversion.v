(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR PCUICValidity.

From Equations Require Import Equations.
Require Import String.
Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.


Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

(** ** Inversion on eval *)

Lemma type_Case_inv Σ Γ ind npar p c brs T :
  Σ;;; Γ |- PCUICAst.tCase (ind, npar) p c brs : T ->
  { '(u, args, mdecl, idecl, pty, indctx, pctx, ps, btys) : _ &                                                 
         (PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl) *
         (PCUICAst.ind_npars mdecl = npar) *
         let pars := firstn npar args in
         (Σ;;; Γ |- p : pty) *
         (types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys)) *
         (check_correct_arity (snd Σ) idecl ind u indctx pars pctx) *
         (Exists (fun sf : sort_family => universe_family ps = sf) (PCUICAst.ind_kelim idecl)) *
         (Σ;;; Γ |- c : PCUICAst.mkApps (tInd ind u) args) *
         (All2 (fun x y : nat * PCUICAst.term => ((fst x = fst y) * (Σ;;; Γ |- snd x : snd y))) brs btys) *
         (Σ ;;; Γ |- PCUICAst.mkApps p (skipn npar args ++ [c])  <= T)}%type.
Proof.
  intros. dependent induction X.
  - unshelve eexists.
    + repeat refine (_,_). all:shelve.
    + cbn. subst pars. intuition eauto.
  - edestruct (IHX _ _ _ _ _ eq_refl) as [ [[[[[[[[]]]]]]]] ].
    repeat match goal with [ H : _ * _ |- _ ] => destruct H end.
    unshelve eexists.
    + repeat refine (_, _). all:shelve.
    + cbn. intuition eauto.
      all: eapply cumul_trans; eauto.
Qed.

Lemma type_Construct_inv Σ Γ ind i u T :
  Σ;;; Γ |- PCUICAst.tConstruct ind i u : T ->
  { '(mdecl, idecl, cdecl) : _ & 
        (wf_local Σ Γ) *
        (PCUICTyping.declared_constructor (fst Σ) mdecl idecl (ind, i) cdecl) *
        (consistent_universe_context_instance (snd Σ) (ind_universes mdecl) u) *
        (Σ ;;; Γ |- type_of_constructor mdecl cdecl (ind, i) u <= T)}%type.
Proof.
  intros. dependent induction X.
  - eexists (_, _, _). cbn. intuition eauto.
  - edestruct IHX. reflexivity. destruct x as []. destruct p.
    exists (m, o, p0). intuition eauto.
    all: eapply cumul_trans; eauto.
Qed.

Lemma type_tFix_inv Σ Γ mfix n T : wf Σ ->
  Σ ;;; Γ |- tFix mfix n : T ->
  ∑ decl, let types := PCUICLiftSubst.fix_context mfix in
               (nth_error mfix n = Some decl) *
               (wf_local Σ (Γ ,,, types)) *
               (All
                 (fun d : BasicAst.def PCUICAst.term =>
                  Σ;;; Γ ,,, types |- BasicAst.dbody d : PCUICLiftSubst.lift #|types| 0 (dtype d)
                  × PCUICAst.isLambda (BasicAst.dbody d) = true) mfix) *
               (Σ;;; Γ |- dtype decl <= T).
Proof.
  intros. dependent induction X0.
  - eexists.  intuition eauto.
  - edestruct (IHX0 _ _ X eq_refl) as []. destruct p as [[[]]].
    (* repeat match goal with [ H : _ * _ |- _ ] => destruct H end. *)
    eexists.
    cbn. intuition eauto.
    all: eapply cumul_trans; eauto.
Qed.
  
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim.

Lemma eval_tBox_inv Σ' x2 :
  eval Σ' E.tBox x2 -> x2 = tBox.
Proof.
  intros. dependent induction H.
  - induction args using rev_ind. inv x. rewrite emkApps_snoc in x. inv x.
  - induction l using rev_ind. cbn in x. invs H0. cbn. eapply IHeval. eauto.
    rewrite emkApps_snoc in x. inv x.
  - reflexivity.
Qed.

Lemma eval_box_apps:
  forall (Σ' : list E.global_decl) (e : E.term) (x : list E.term), eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2. revert e H2; induction x; cbn; intros; eauto using eval.
Qed.
