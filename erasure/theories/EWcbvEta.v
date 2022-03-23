(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.
     

From MetaCoq.Template Require Import config utils BasicAst Universes.
From MetaCoq.Erasure Require Import EAst ETyping EAstUtils.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalInd EEtaExpanded ECSubst.

Local Hint Resolve isEtaExp_eval : core.
Local Hint Constructors eval : core.

Section Wcbv.
  Context {wfl : WcbvFlags}.
  Context (Σ : global_declarations).

  Let expanded_ := isEtaExp Σ.

  Let expanded := expanded_ [].

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  | eval_box a t t' :
      eval a tBox ->
      eval t t' ->
      eval (tApp a t) tBox

  (* (** Beta, with guarded fixpoint before *) *)
  (* | eval_beta_guarded_fix mfix idx na b a a' res fn args1 fa args2 args2' : *)
  (*     Forall expanded args1 -> expanded fa -> Forall expanded args2 -> expanded a -> *)
  (*     Forall expanded args2' -> expanded a' -> expanded res -> *)
  (*     expanded_ [0] b -> *)
  (*     expanded (mkApps (tFix mfix idx) (args1 ++ [fa])) -> *)
  (*     expanded (csubst a' 0 b) -> *)
  (*     expanded fn -> *)
  (*     cunfold_fix mfix idx = Some (#|args1|, fn) -> *)
  (*     All2 eval args2 args2' -> *)
  (*     eval (mkApps fn (args1 ++ [fa] ++ args2')) (tLambda na b) -> *)
  (*     eval a a' -> *)
  (*     eval (csubst a' 0 b) res -> *)
  (*     eval (mkApps (tFix mfix idx) (args1 ++ [fa] ++ args2 ++ [a])) res *)

  (** Beta, with unguarded fixpoint before *)
  | eval_beta_unguarded_fix mfix idx na b a a' res args argsv fa arg fn :
      expanded fa -> Forall expanded args -> expanded a ->
      Forall expanded args -> expanded a' -> expanded res ->
      expanded_ [0] b ->
      expanded (csubst a' 0 b) ->
      expanded fn ->

      All2 (fun a a' => (a = a') + eval a a')%type args argsv ->
      cunfold_fix mfix idx = Some (arg,fn) ->
      eval (mkApps (tApp fn fa) argsv) (tLambda na b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (mkApps (tFix mfix idx) (fa :: args ++ [a])) res

  (** Beta, with no fixpoint before *)
  | eval_beta f na b a a' res :
    expanded f -> 
    expanded a -> expanded a' ->
    expanded (csubst a' 0 b) -> expanded res ->
    isEtaExp Σ [0] b ->
    with_guarded_fix || negb (isFixApp f)  ->
    eval f (tLambda na b) ->
    eval a a' ->
    eval (csubst a' 0 b) res ->
    eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 b1) res

  (** Case *)
  | eval_iota ind pars discr c args brs br res :
      eval discr (mkApps (tConstruct ind c) args) ->
      inductive_isprop_and_pars Σ ind = Some (false, pars) ->
      nth_error brs c = Some br ->
      #|skipn pars args| = #|br.1| ->
      eval (iota_red pars args br) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Singleton case on a proof *)
  | eval_iota_sing ind pars discr brs n f res :
      with_prop_case ->
      eval discr tBox ->
      inductive_isprop_and_pars Σ ind = Some (true, pars) ->
      brs = [ (n,f) ] ->
      eval (substl (repeat tBox #|n|) f) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av fn res :
      forall guarded : with_guarded_fix,
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (#|argsv|, fn) ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      forall guarded : with_guarded_fix,
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| < narg) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

  (** Fix unfolding, without guard *)
  | eval_fix' f mfix idx a fn res narg :
    forall unguarded : with_guarded_fix = false,
    eval f (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    eval (tApp fn a) res ->
    eval (tApp f a) res

  (** CoFix-case unfolding *)
  | eval_cofix_case ip mfix idx args discr narg fn brs res :
      eval discr (mkApps (tCoFix mfix idx) args) ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip (mkApps fn args) brs) res ->
      eval (tCase ip discr brs) res

  (** CoFix-proj unfolding *)
  | eval_cofix_proj p mfix idx args discr narg fn res :
      eval discr (mkApps (tCoFix mfix idx) args) ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p discr) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
      decl.(cst_body) = Some body ->
      eval body res ->
      eval (tConst c) res

  (** Proj *)
  | eval_proj i pars arg discr args res :
      eval discr (mkApps (tConstruct i 0) args) ->
      inductive_isprop_and_pars Σ i = Some (false, pars) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (** Proj *)
  | eval_proj_prop i pars arg discr :
      with_prop_case ->
      eval discr tBox ->
      inductive_isprop_and_pars Σ i = Some (true, pars) ->
      eval (tProj (i, pars, arg) discr) tBox

  (** Atoms (non redex-producing heads) applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~ (isLambda f' || (if with_guarded_fix then isFixApp f' else isFix f') || isBox f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors) *)
  | eval_atom t : atom t -> eval t t.

End Wcbv.

Module Ee := EWcbvEval.

Require Import ssreflect ssrbool.

Lemma eval_app_cong_tApp {wfl : WcbvFlags} Σ t v args res :
  Ee.eval Σ t v ->  
  Ee.eval Σ (tApp v args) res ->
  Ee.eval Σ (tApp t args) res.
Proof.
  intros. depind H0.
  - econstructor; eauto. eapply eval_trans; eauto.
  - econstructor; eauto. eapply eval_trans; eauto.
  - eapply Ee.eval_fix; eauto. eapply eval_trans; eauto.
  - eapply Ee.eval_fix_value; eauto. eapply eval_trans; eauto.
  - eapply Ee.eval_fix'; eauto. eapply eval_trans; eauto.
  - eapply Ee.eval_app_cong; eauto. eapply eval_trans; eauto.
  - cbn in i. easy.
Qed.

Lemma eval_app_cong_tApp2 {wfl : WcbvFlags} Σ t v args res :
  Ee.eval Σ args v ->  
  Ee.eval Σ (tApp t v) res ->
  Ee.eval Σ (tApp t args) res.
Proof.
  intros. depind H0.
  - econstructor; eauto. 
  - econstructor. eauto. eapply eval_trans; eauto. eauto.
  - eapply Ee.eval_fix. eauto. eauto. eapply eval_trans; eauto. eauto. eauto.
  - eapply Ee.eval_fix_value. eauto. eauto. eapply eval_trans; eauto. eauto. eauto.
  - eapply Ee.eval_fix'; eauto.
  - eapply Ee.eval_app_cong. eauto. eauto. eapply eval_trans; eauto.
  - cbn in i. easy.
Qed.

Lemma eval_mkApps_tFix_inv_size {wfl : WcbvFlags} Σ mfix idx args v :
with_guarded_fix ->
  forall Heval : Ee.eval Σ (mkApps (tFix mfix idx) args) v,
 (exists args', Forall2 (fun a a' => exists H : Ee.eval Σ a a', eval_depth H < eval_depth Heval) args args' /\ v = mkApps (tFix mfix idx) (args')) \/
   (exists fn args1 a args2 argsv2 (av : term), args = args1 ++ [a] ++ args2 /\
            cunfold_fix mfix idx = Some (#|args1|, fn) /\
            (exists H : Ee.eval Σ a av, eval_depth H < eval_depth Heval) /\
            Forall2 (fun a a' => exists H : Ee.eval Σ a a', eval_depth H < eval_depth Heval) args2 argsv2 /\
            exists H : Ee.eval Σ (mkApps fn (args1 ++ [a] ++ argsv2)) v, eval_depth H <= eval_depth Heval).
Proof.
 revert v.
 induction args using List.rev_ind; intros v wg ev.
 + left. exists []. split. repeat econstructor. now depelim ev.
 + rewrite mkApps_app in ev |- *.
   cbn in *.
   depelim ev.
   all: try(specialize (IHargs) with (Heval := ev1); destruct IHargs as [(args' & ? & Heq) | (fn_ & args1 & a & args2 & argsv2 & av_ & -> & Hunf & [Ha_ Ha] & Heval & Hev & Hsz)];eauto; rewrite ?Heq; try solve_discr; try congruence;
     len; rewrite ?Heq; try rewrite Nat.add_comm; eauto 9).
   * right. do 6 eexists; repeat eapply conj; cbn.
     1: rewrite <- app_assoc;cbn; reflexivity. all: eauto.
     unshelve eexists; eauto ; lia.
     eapply Forall2_app. solve_all. destruct H. exists x1. lia.
     econstructor. 2:econstructor. unshelve eexists. eauto. lia.
     replace ((args1 ++ a :: argsv2 ++ [t'])) with ((args1 ++ a :: argsv2) ++ [t']) by now rewrite <- app_assoc. 
     rewrite mkApps_app. cbn. unshelve eexists.
     econstructor. eauto. eapply size_final. eauto.
     cbn. destruct size_final. lia. 
   * right. do 6 eexists; repeat eapply conj; cbn.
     1: rewrite <- app_assoc;cbn; reflexivity. all: eauto.
     unshelve eexists; eauto ; lia.
     eapply Forall2_app. solve_all. destruct H. exists x1. lia.
     econstructor. 2:econstructor. unshelve eexists. eauto. lia.
     replace ((args1 ++ a :: argsv2 ++ [a'])) with ((args1 ++ a :: argsv2) ++ [a']) by now rewrite <- app_assoc. 
     rewrite mkApps_app. cbn. unshelve eexists.
     econstructor. eauto. eapply size_final. eauto. eauto.
     cbn. destruct size_final. lia. 
   * invs H0. right. do 6 eexists; repeat eapply conj; cbn.
     1: reflexivity. all: eauto. eapply Forall2_length in H as ->. eauto.
     unshelve eexists; eauto; lia.
     rewrite mkApps_app. cbn.

     unshelve eexists.
     eapply eval_app_cong_tApp2; eauto.
     eapply eval_app_cong_tApp; eauto.
     todo "ok". todo "ok".
Admitted.

Theorem use {wfl : WcbvFlags} Σ t v :
  Ee.eval Σ t v -> isEtaExp Σ [] t -> eval Σ t v.
Proof.
  induction 1 as [ | ? ? ? ? ? ? ? ? IHs | | | | ? ? ? ? ? ? ? ? ? ? ? IHs | ? ? ? ? ? ? ? ? ? ? ? IHs | ? ? ? ? ? ? ? ? ? ? IHs | | | | | | |   ] using eval_mkApps_rect.
  - admit.
  - pose proof (H' := H). move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct expanded_head_viewc.
    + clear IHs. move=> [] hl [] hf [] ha /andP[] hl' etal.
      move: H H0. rewrite hf => H H0.
      eapply eval_construct in H as [? []];solve_discr.
    + solve_all. rtoProp. solve_all. subst.
      destruct with_guarded_fix eqn:Ewf.
      * specialize eval_mkApps_tFix_inv_size with (Heval := H); intros [(args' & ? & Heq) | (fn_ & args1 & a_ & args2 & argsv2 & av_ & Heq & Hunf & [Ha_ Ha] & Heval & Hev & Hsz)]; eauto.
        -- solve_discr.
        -- econstructor. 
           ++ rewrite Heq isEtaExp_mkApps => //. Opaque isEtaExp. cbn. rtoProp.
              repeat split.
              ** unfold cunfold_fix, isEtaExp_fixapp in *. destruct nth_error; invs Hunf. len. rewrite H5.
                 eapply Nat.ltb_lt. lia.
              ** solve_all.
              ** eapply All_remove_last in H7. rewrite Heq in H7. solve_all.
           ++ eapply All_Forall, Forall_last in H7. rewrite H3. eassumption. eauto.
           ++ shelve.
           ++ shelve.
           ++ shelve.
           ++ shelve.
           ++ eapply All_remove_last in H7. rewrite Heq in H7. eapply All_app in H7 as []. invs a1.
              eapply IHeval1. todo "gotit".
           ++ eapply IHeval2. todo "gotit".
           ++ eapply IHeval3. eapply etaExp_csubst. eapply isEtaExp_eval. eauto. todo "gotit".
              admit.
      * admit.
    + solve_all. rewrite nth_error_nil in H5; easy.
    + move/and4P => [] etat etal etaf etaa.
      eapply eval_beta; try assumption.
      1-4: shelve.
      eapply IHeval1; eauto. eauto. eapply IHeval3. eapply etaExp_csubst. eauto.
      eapply isEtaExp_eval in H'.
      simp_eta in H'. eassumption. eauto.
  - simp_eta; solve_all; econstructor; try eassumption; eauto using etaExp_csubst.
  - simp_eta. solve_all. econstructor; try eassumption. eapply IHeval2.
    unfold iota_red. eapply isEtaExp_substl.
    2:{ apply isEtaExp_eval in H. 2: eauto. rewrite isEtaExp_mkApps in H => //.
  -
