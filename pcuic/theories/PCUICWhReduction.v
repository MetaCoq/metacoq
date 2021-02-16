(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICContextRelation
     PCUICContextReduction PCUICEquality PCUICLiftSubst PCUICTyping PCUICWeakeningEnv
     PCUICInduction PCUICRedTypeIrrelevance PCUICNormal PCUICReduction.
Require Import ssreflect.
Set Asymmetric Patterns.
From Equations Require Import Equations.

Inductive wh_red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| wh_red_beta na t b a :
    wh_red1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| wh_red_zeta na b t b' :
    wh_red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| wh_red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    wh_red1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| wh_red_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    wh_red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args br)

(** Fix unfolding, with guard *)
| wh_red_fix mfix idx args a fn :
    unfold_fix mfix idx = Some (#|args|, fn) ->
    isConstruct_app a -> 
    wh_red1 Σ Γ (tApp (mkApps (tFix mfix idx) args) a) (tApp (mkApps fn args) a)

(** CoFix-case unfolding *)
| wh_red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    wh_red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| wh_red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    wh_red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| wh_red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    wh_red1 Σ Γ (tConst c u) (subst_instance u body)

(** Proj *)
| wh_red_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    wh_red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg
    
| case_red_discr ci p c c' brs :
  wh_red1 Σ Γ c c' -> 
  wh_red1 Σ Γ (tCase ci p c brs) (tCase ci p c' brs)

| proj_red p c c' : wh_red1 Σ Γ c c' -> wh_red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : wh_red1 Σ Γ M1 N1 -> wh_red1 Σ Γ (tApp M1 M2) (tApp N1 M2)

(** Reduction of a fixpoint's principal/recursive argument *)
| wh_red_fix_arg mfix idx args fn arg arg' :
    unfold_fix mfix idx = Some (#|args|, fn) ->
    wh_red1 Σ Γ arg arg' ->
    wh_red1 Σ Γ (tApp (mkApps (tFix mfix idx) args) arg)
        (tApp (mkApps (tFix mfix idx) args) arg').

Derive Signature NoConfusion for wh_red1.



From Coq Require Import ssrbool.

Ltac invwh := simpl in *; try congruence || match goal with 
    | [ H : whne _ _ _ (mkApps _ _) |- _ ] => 
    eapply whne_mkApps_inv in H => //; solve_discr;
    destruct H as [|[? [? [? [? [? [eq [? [? ?]]]]]]]]]; solve_discr
  | [ H : whne _ _ _ (?f ?x) |- _ ] => depelim H; solve_discr; simpl in *; try congruence
  end.

Lemma nisConstruct_app_whne {Σ Γ a} :
  whne RedFlags.default Σ Γ a -> isConstruct_app a -> False.
Proof.
  rewrite /isConstruct_app.
  destruct decompose_app eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_inv in da. subst.
  intros wh. simpl.
  destruct t => //. intros _.
  repeat invwh.
Qed.


Set Equations With UIP.

Lemma uip_pr1 {A B} {HA : UIP A} (x : A) (y y' : B x) :
  y = y' ->
  {| pr1 := x; pr2 := y |} =
  {| pr1 := x; pr2 := y' |}.
Proof.
  intros ->.
  f_equal.
Qed.

Lemma uip_K {A} {HA : UIP A} {x : A} (e : x = x) : e = eq_refl.
Proof.
  apply uip.
Qed.

Lemma mkApps_tApp_inj fn args t u : 
  ~~ isApp fn -> 
  mkApps fn args = tApp t u ->
  args <> [] /\ t = mkApps fn (removelast args) /\ nth_error args #|removelast args| = Some u.
Proof.
  intros napp eqapp.
  destruct args using rev_case => //.
  simpl in eqapp. subst fn => //.
  rewrite -mkApps_nested in eqapp. noconf eqapp.
  rewrite removelast_app // /= app_nil_r nth_error_app_ge // Nat.sub_diag /=.
  repeat split; auto. now destruct args.
Qed.

Ltac simpl_tApp_eq :=
  match goal with
  | [ H : tApp _ _ = mkApps _ _ |- _ ] =>
    symmetry in H; simpl_tApp_eq
  | [ H : mkApps _ _ = tApp _ _ |- _ ] =>
    let H' := fresh in let H'' := fresh in 
    let argsnil := fresh in
    apply mkApps_tApp_inj in H as [argsnil [H' H'']] => //;
    try rewrite -> H in *; try rewrite -> H' in *
  end.

Ltac simpl_mkApps := 
  match goal with 
  [ H : mkApps ?f _ = mkApps _ _ |- _ ] =>
    let H' := fresh in 
    let H'' := fresh in 
    pose proof (mkApps_eq_inj H eq_refl eq_refl) as [H' H'']; 
    noconf H'; noconf H''
  end.

Ltac simpl_mkApps_in eqH := 
  match goal with 
  [ H : mkApps ?f _ = mkApps _ _ |- _ ] =>
    let H' := fresh in 
    let H'' := fresh in 
    pose proof (mkApps_eq_inj H eq_refl eq_refl) as [H' H'']; 
    noconf H'; noconf H''; try rewrite (uip_K H) in eqH; cbn in eqH; try noconf eqH
  end.

Lemma removelast_app_tip {A} (l : list A) (a : A) : 
  removelast (l ++ [a]) = l.
Proof.
  now rewrite removelast_app // /= app_nil_r.
Qed.

Lemma nth_error_app_removelast {A} (l : list A) (a : A) :
  nth_error l #|removelast l| = Some a ->
  removelast l ++ [a] = l.
Proof.
  induction l using rev_case.
  * rewrite nth_error_nil => //.
  * rewrite removelast_app_tip.
    intros hnth.
    rewrite nth_error_app_ge // Nat.sub_diag /= in hnth.
    now noconf hnth.
Qed.

Lemma firstn_removelast_length {A} (l : list A) : 
  firstn #|removelast l| l = removelast l.
Proof.
  induction l using rev_ind => /= //.
  now rewrite removelast_app_tip (firstn_app_left _ 0) // /= app_nil_r.
Qed.

Lemma skipn_removelast_length {A} (l : list A) : 
  skipn (S #|removelast l|) l = [].
Proof.
  induction l using rev_ind => /= //.
  rewrite removelast_app_tip -Nat.add_1_r skipn_all2 // app_length /= //.
Qed.

Lemma wh_red1_fix {Σ Γ mfix idx t args} : 
  wh_red1 Σ Γ (mkApps (tFix mfix idx) args) t ->
  (∑ rarg body arg,
    unfold_fix mfix idx = Some (rarg, body) ×
    (nth_error args rarg = Some arg) × 
    ((isConstruct_app arg × t = mkApps body args) +
    ∑ arg', (wh_red1 Σ Γ arg arg' × t = mkApps (tFix mfix idx) (firstn rarg args ++ (arg' :: skipn (S rarg) args))))).
Proof.
  intros h; depind h; solve_discr.
  - simpl_tApp_eq. simpl_mkApps.
    eexists _, _, _; repeat split; eauto.
    left. rewrite -mkApps_snoc nth_error_app_removelast //.
  - simpl_tApp_eq.
    specialize (IHh _ _ _ _ eq_refl) as [rarg [body [arg [unffix [hnth whne]]]]].
    eexists _, _, _; repeat split; tea.
    now apply nth_error_removelast in hnth.
    destruct whne; [left|right]; intuition auto.
    * rewrite b. rewrite -mkApps_snoc. f_equal.
      rewrite nth_error_app_removelast //.
    * destruct s as [arg' [wharg ->]].
      exists arg'; split => //.
      rewrite -mkApps_snoc. f_equal.
      pose proof (nth_error_removelast hnth).
      eapply nth_error_Some_length in H.
      rewrite firstn_removelast // - !app_assoc /=. f_equal. f_equal.
      destruct args using rev_case => //.
      rewrite removelast_app_tip.
      rewrite skipn_app. f_equal.
      eapply nth_error_Some_length in hnth.
      rewrite app_length /= in H.
      rewrite removelast_app_tip in hnth.
      assert (S rarg - #|args| = 0) as -> by lia.
      rewrite skipn_0.
      rewrite removelast_app_tip in H1.
      rewrite nth_error_app_ge // Nat.sub_diag /= in H1. now noconf H1.
  - simpl_tApp_eq; simpl_mkApps.
    exists #|removelast args0|, fn, arg; repeat split; tea.
    right. exists arg'; repeat split; auto.
    rewrite -mkApps_snoc. f_equal.
    now rewrite firstn_removelast_length skipn_removelast_length.
Qed.

Lemma whne_fix Σ Γ mfix idx args : 
  whne RedFlags.default Σ Γ (mkApps (tFix mfix idx) args) ->
  (∑ rarg body arg,
    unfold_fix mfix idx = Some (rarg, body) ×
    (nth_error args rarg = Some arg) × 
    whne RedFlags.default Σ Γ arg).
Proof.
  intros h; depind h; solve_discr.
  - apply PCUICAstUtils.mkApps_tApp_inj in H as [-> ->] => //.
    specialize (IHh _ _ _ eq_refl) as [rarg [body [arg [unffix [hnth whne]]]]].
    eexists _, _, _; repeat split; tea.
    now apply nth_error_removelast in hnth.
  - exists rarg, body, arg; repeat split; tea.
  - simpl in e; congruence.
Qed.

From MetaCoq.PCUIC Require Import PCUICSize.

Lemma eqs_trans {A} {x y z : A} (e : x = y) (e' : x = z) : y = z.
Proof. rewrite -e. exact e'. Defined.

Ltac inj_eqs := 
  match goal with
  | [ H : ?x = ?y, H' : ?x = ?z |- _] =>
    let H'' := fresh in 
    pose proof (eqs_trans H H') as H''; progress noconf H''
  end.

Lemma whne_wh_red1 Σ Γ t u :
  wh_red1 Σ Γ t u -> whne RedFlags.default Σ Γ t -> False.
Proof.
  intros r h.
  induction t in r, h, u |- * using term_ind_size_app.
  all:depelim h.
  all:try solve [depelim r; solve_discr; simpl in *; try congruence].
  all:try solve [eapply mkApps_discr in H1; auto].
  - depelim r.
    * depelim h; solve_discr; simpl in *; try congruence.
    * eapply whne_fix in h as [rarg [body [arg [unf [nth whne]]]]].
      rewrite unf in e; noconf e.
      eapply nth_error_Some_length in nth. lia.
    * eauto.
    * eapply whne_fix in h as [rarg' [body' [arg'' [unf' [nth' whne']]]]].
      rewrite unf' in e; noconf e.
      eapply nth_error_Some_length in nth'. lia.
  - rewrite H0 in r.
    depelim r; solve_discr.
    * repeat simpl_tApp_eq. simpl_mkApps.
      subst t1. inj_eqs.
      rewrite e in e1. noconf e1. rewrite e0 in H3; noconf H3.
      eapply nisConstruct_app_whne in h; eauto.
    * simpl_tApp_eq.
      eapply wh_red1_fix in r as (?&?&?&?&?&?).
      rewrite e1 in e; noconf e.
      rewrite (nth_error_removelast e2) in e0; noconf e0.
      simpl_tApp_eq. inj_eqs.
      destruct s.
      + destruct p. eapply nisConstruct_app_whne in h; eauto.
      + destruct s as [arg' [wh _]].
        eapply H; tea.
        eapply (nth_error_size size) in e2.
        now rewrite /= size_mkApps.
    * simpl_tApp_eq. simpl_mkApps. repeat inj_eqs.
      eapply H; tea. rewrite -H0.
      eapply (nth_error_size size) in e0.
      now rewrite mkApps_size.
  - depelim r; solve_discr.
    * eapply whne_mkApps_inv in h as [|]; auto.
      invwh.
      destruct s as (? & ? & ? & ? & ? & ?). intuition discriminate.
    * eapply whne_mkApps_inv in h as [|]; auto.
      invwh.
      destruct s as (? & ? & ? & ? & ? & ?). intuition discriminate.
    * eauto.
  - depelim r; solve_discr.
    * eapply whne_mkApps_inv in h as [|]; auto.
      invwh.
      destruct s0 as (? & ? & ? & ? & ? & ?). intuition discriminate.
    * eapply whne_mkApps_inv in h as [|]; auto.
      invwh.
      destruct s as (? & ? & ? & ? & ? & ?). intuition discriminate.
    * eauto.
Qed.

Lemma wh_red1_abs {Σ Γ na ty b t} : 
  wh_red1 Σ Γ (tLambda na ty b) t -> False.
Proof.
  intros r; depind r; solve_discr.
Qed.

Lemma wh_red1_constr {Σ Γ i n u args t} : 
  wh_red1 Σ Γ (mkApps (tConstruct i n u) args) t -> False.
Proof.
  intros r; depind r; try simpl_tApp_eq; solve_discr; eauto.
Qed.

Lemma wh_red1_inductive {Σ Γ i u args t} : 
  wh_red1 Σ Γ (mkApps (tInd i u) args) t -> False.
Proof.
  intros r; depind r; try simpl_tApp_eq; solve_discr; eauto.
Qed.

Lemma wh_red1_cofix {Σ Γ mfix idx args t} : 
  wh_red1 Σ Γ (mkApps (tCoFix mfix idx) args) t -> False.
Proof.
  intros r; depind r; try simpl_tApp_eq; solve_discr; eauto.
Qed.

Lemma whnf_wh_red1 Σ Γ t u :
  wh_red1 Σ Γ t u -> whnf RedFlags.default Σ Γ t -> False.
Proof.
  induction 2.
  1:eauto using whne_wh_red1.
  all:depelim X; try simpl_tApp_eq; try simpl_mkApps; solve_discr.
  - now eapply wh_red1_constr in X.
  - now apply wh_red1_inductive in X.
  - rewrite e in y. congruence.
  - eapply wh_red1_fix in X as (?&?&?&?&?&?).
    rewrite e in y.
    now rewrite (nth_error_removelast e0) in y.
  - rewrite e in y. congruence.
  - now eapply wh_red1_cofix in X.
Qed.

Lemma isConstruct_app_tApp t u : isConstruct_app (tApp t u) -> isConstruct_app t.
Proof.
  rewrite /isConstruct_app /decompose_app /=.
  now rewrite fst_decompose_app_rec.
Qed.

Lemma isConstruct_app_spec t : 
  isConstruct_app t ->
  ∑ ind n u args, t = mkApps (tConstruct ind n u) args.
Proof.
  induction t => // /=.
  - intros isc. apply isConstruct_app_tApp in isc.
    destruct (IHt1 isc) as [ind [n [u [args ->]]]].
    exists ind, n, u, (args ++ [t2]).
    now rewrite -mkApps_snoc.
  - intros _.
    now exists ind, n, ui, [].
Qed. 
  
Lemma wh_red1_isConstruct_app Σ Γ arg arg' :
  wh_red1 Σ Γ arg arg' -> 
  isConstruct_app arg -> False.
Proof.
  intros w isc.
  eapply isConstruct_app_spec in isc as [ind [n [u [args' ->]]]].
  now eapply wh_red1_constr in w.
Qed.

Lemma is_constructor_args narg args : is_constructor narg args -> args <> [].
Proof.
  rewrite /is_constructor.
  destruct args => //. now rewrite nth_error_nil.
Qed.

Lemma is_constructor_removelast_args narg (args : list term) arg : 
  nth_error (removelast args) narg = Some arg -> args <> [].
Proof.
  destruct args => //. now rewrite nth_error_nil.
Qed.

Ltac invert_wh_red1 := 
  match goal with
  | [ H : wh_red1 _ _ (mkApps (tConstruct _ _ _) _) _ |- _] => 
    now apply wh_red1_constr in H
  | [ H : wh_red1 _ _ (mkApps (tCoFix _ _) _) _ |- _] => 
    now apply wh_red1_cofix in H
  | [ H : wh_red1 _ _ (tLambda _ _ _) _ |- _] => 
    now apply wh_red1_abs in H
  | [ H : wh_red1 _ _ (mkApps (tInd _ _) _) _ |- _] => 
    now apply wh_red1_inductive in H
  end.

Lemma uip_pr2 {A B} {HB : UIP B} (P Q : A -> B) (x x' : A) (y : P x = Q x) (y' : P x' = Q x') :
  x = x' ->
  {| pr1 := x; pr2 := y |} =
  {| pr1 := x'; pr2 := y' |} :> sigma (fun x => P x = Q x).
Proof.
  intros ->.
  now rewrite (uip y y').
Qed.

Instance branch_UIP : UIP (branch term).
Proof.
  eapply EqDec.eqdec_uip; tc.
Qed.

Instance option_UIP {A} (u : EqDec A) : UIP (option A).
Proof.
  eapply EqDec.eqdec_uip; tc.
  eqdec_proof.
Qed.

Ltac clear_uip := 
  match goal with
  | [ H : ?x = ?y, H' : ?x = ?y |- _] =>
    rewrite -> (uip H H') in *; try clear H
  end.

Lemma isConstruct_app_whnf {Σ Γ t} : 
  isConstruct_app t -> whnf RedFlags.default Σ Γ t.
Proof.
  move/isConstruct_app_spec => [ind [c [u [args ->]]]].
  eapply whnf_cstrapp.
Qed.

Lemma wh_red1_unique_sig {Σ Γ t u u'} (r0 : wh_red1 Σ Γ t u) (r1 : wh_red1 Σ Γ t u') : 
  {| pr1 := {| pr1 := t; pr2 := u |}; pr2 := r0 |} = 
  {| pr1 := {| pr1 := t; pr2 := u' |}; pr2 := r1 |} :> sigma (fun x : sigma (fun _ : term => term) => wh_red1 Σ Γ (pr1 x) (pr2 x)).
Proof.
  eapply noConfusion_wh_red1_obligation_1.
  induction r0 in u', r1 |- *; depelim r1 => //.
  all:try solve [
    let H' := fresh in
    pose proof (f_equal (@pr1 _ _) H) as H'; simpl in H'; noconf H';
    solve_discr].
  all:try solve [try clear H; try clear IHr0; solve_discr].
  all:try solve [elimtype False; invert_wh_red1].
  all:try (simpl_mkApps_in H); try simpl_mkApps; repeat (inj_eqs; clear_uip); try reflexivity.
  all:try (simpl; clear IHr0; invert_wh_red1).
  - now rewrite (uip i i0).
  - simpl. eapply wh_red1_fix in r1 as [rarg [body [arg [unf [hnth s]]]]].
    rewrite e in unf. noconf unf.
    now apply nth_error_Some_length in hnth.
  - simpl. apply (whnf_wh_red1 _ _ _ _ r1).
    now eapply isConstruct_app_whnf.
  - pose proof (declared_constant_inj _ _ isdecl isdecl0).
    destruct H. inj_eqs.
    repeat clear_uip.
    now rewrite (uip isdecl isdecl0).
  - simpl. specialize (IHr0 _ r1).
    eapply noConfusion_wh_red1_obligation_1 in IHr0. now noconf IHr0.
  - simpl. specialize (IHr0 _ r1).
    eapply noConfusion_wh_red1_obligation_1 in IHr0. now noconf IHr0.
  - simpl. clear IHr0. eapply wh_red1_fix in r0 as [rarg [body [arg [unf [hnth s]]]]].
    inj_eqs. now apply nth_error_Some_length in hnth.
  - simpl. specialize (IHr0 _ r1).
    eapply noConfusion_wh_red1_obligation_1 in IHr0. now noconf IHr0.
  - simpl. clear IHr0.
    eapply wh_red1_fix in r0 as [rarg [body [arg [unf [hnth s]]]]].
    inj_eqs. now apply nth_error_Some_length in hnth.
  - simpl. clear IHr0.
    eapply (whnf_wh_red1 _ _ _ _ r0).
    now apply isConstruct_app_whnf.
  - simpl; clear IHr0.
    eapply wh_red1_fix in r1 as [rarg [body [arg'' [unf [hnth s]]]]].
    inj_eqs.
    now apply nth_error_Some_length in hnth.
  - specialize (IHr0 _ r1).
    eapply noConfusion_wh_red1_obligation_1 in IHr0. now noconf IHr0.
Qed.

(* Not only the relation is deterministic on end values, 
  we also show that it is also proof-irrelevant: there is actually a single
  weak-head reduction path between two terms. *)

Lemma wh_red1_unique {Σ Γ t u u'} : 
  wh_red1 Σ Γ t u -> wh_red1 Σ Γ t u' -> u = u'.
Proof.
  intros r0 r1.
  pose proof (wh_red1_unique_sig r0 r1).
  noconf H. reflexivity.
Qed.

Lemma wh_red1_irrelevant {Σ Γ t u} (r0 r1 : wh_red1 Σ Γ t u) : r0 = r1.
Proof.
  pose proof (wh_red1_unique_sig r0 r1).
  noconf H. simpl. reflexivity.
Qed.

Lemma wh_red1_red1 {Σ Γ t u} : wh_red1 Σ Γ t u -> red1 Σ Γ t u.
Proof.
  induction 1; try solve [econstructor; eauto].
  rewrite - !mkApps_snoc.
  eapply red_fix. tea.
  now rewrite /is_constructor nth_error_app_ge // Nat.sub_diag /=.
Qed.
From MetaCoq.PCUIC Require Import PCUICSubstitution.

Lemma unfold_fix_args {mfix idx args narg fn} : 
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args ->
  ∑ arg, args = firstn narg args ++ (arg :: skipn (S narg) args) × 
    narg = #|firstn narg args| ×
    isConstruct_app arg.
Proof.
  intros unf isc.
  rewrite /is_constructor in isc.
  move: isc.
  case: nth_error_spec => [x hnth hlt|hle] => // isc.
  exists x. split => //. 
  now eapply nth_error_firstn_skipn in hnth.
  split => //. rewrite List.firstn_length. lia.
Qed.

(** Even if the weak-head-reduction is carefully crafted to have unique derivations,
    we still get the general reduction rules of fixpoints, where the principal argument
    might be anywhere in the [args] spine. *)
Lemma wh_red_fix_red {Σ Γ mfix idx args narg fn} : 
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args ->
  wh_red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args).
Proof.
  intros unf isc.
  destruct (unfold_fix_args unf isc) as [arg [hargs [hnth isc']]].
  clear isc.
  rewrite hnth in unf.
  rewrite hargs.
  revert unf isc'.
  clear hnth hargs.
  generalize (firstn narg args).
  induction (skipn (S narg) args) using rev_ind.
  - intros. rewrite - !mkApps_nested. constructor; auto.
  - intros nargs unf isc.
    specialize (IHl _ unf isc).
    rewrite (app_assoc _ [arg]) app_assoc.
    rewrite - !(mkApps_nested _ _ [x]).
    eapply app_red_l.
    rewrite -app_assoc. apply IHl.
Qed.

From Equations.Type Require Import Relation Relation_Properties.

Definition wh_red Σ Γ := clos_refl_trans (wh_red1 Σ Γ).

(** Sanity check: if there is a one-step reduction to a product, then there is also a weak-head-reduction 
  to the product. This is still far from a standardization theorem. *)
Lemma red1_tProd_wh_red {cf : checker_flags} {Σ : global_env_ext} {Γ t na A B} : red1 Σ Γ t (tProd na A B) -> 
  ∑ A' B', wh_red Σ Γ t (tProd na A' B') × red Σ Γ A' A × red Σ (Γ ,, vass na A) B' B.
Proof.
  remember (tProd na A B) as t'.
  intros red; revert na A B Heqt'.
  induction red using red1_ind_all; intros.
  all:try solve [
    eexists _, _; split; [constructor; erewrite <- Heqt'; econstructor; tea|
    split; reflexivity] ].
  all:try congruence.
  - eexists _, _; split. erewrite <- Heqt'.
    constructor.
    eapply wh_red_fix_red; tea. split; reflexivity.
  - noconf Heqt'.
    exists M1, M2. split. reflexivity.
    split; try reflexivity.
    now eapply red1_red.
  - noconf Heqt'.
    eexists _, _. split.
    reflexivity.
    split; try reflexivity.
    now apply red1_red.
Qed.

(** TODO: define a notion of internal reductions, following Takahashi's "Parallel reductions in lambda-calculus".
  Internal reductions are exactly the congruence rules of reduction not in the weak-head reduction, e.g. 
  including reduction on the right of an application, or congruence for beta-redexes.

  This should allow to show that:
  1) head reduction is standardizing (his proof is for "strong" head reduction though, not sure if this
    adapts smoothly to weak head reductions). We could also consider a strong form 
    of head reduction here, which would still produce unique (strong) head normal forms.
    As long as we have at least on standardizing reduction allowing to uncover products/inductives etc.
    we should be fine
  2) His paper also shows how one can adapt the confluence proof to η-reduction using η-postponment.
    The main difference here seems to be that we have type annotations in the domain of lambdas, 
    but if we adapt eq-term to not compare those it should "just work".

*)
(** If there is a one-step reduction then it is either a weak head reduction or an internal reduction *)
(* Lemma red1_wh_red1 {cf : checker_flags} {Σ : global_env_ext} {Γ t u} : 
  red1 Σ Γ u v -> wh_red1 Σ Γ t v + int_red1 Σ Γ t v. *)
