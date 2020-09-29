(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInduction.
Require Import String.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(* Require Import Equations.Type.DepElim. *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.

End RedFlags.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive whnf (Γ : context) : term -> Prop :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fixapp mfix idx v :
    match unfold_fix mfix idx with
    | Some (rarg, body) => nth_error v rarg = None
    | None => True
    end ->
    whnf Γ (mkApps (tFix mfix idx) v)
  | whnf_cofixapp mfix idx v : whnf Γ (mkApps (tCoFix mfix idx) v)

  with whne (Γ : context) : term -> Prop :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)

  | whne_rel_nozeta i :
      RedFlags.zeta flags = false ->
      whne Γ (tRel i)

  | whne_var v :
      whne Γ (tVar v)

  | whne_evar n l :
      whne Γ (tEvar n l)

  | whne_sort s : whne Γ (tSort s)

  | whne_prod na A B : whne Γ (tProd na A B)

  | whne_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t)

  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      whne Γ (tConst c u)

  | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u)

  | whne_app f v :
      whne Γ f ->
      whne Γ (tApp f v)

  (* Stuck fixpoints are neutrals *)
  | whne_fixapp mfix idx args rarg arg body :
     unfold_fix mfix idx = Some (rarg, body) ->
     nth_error args rarg = Some arg -> 
     whne Γ arg ->
     whne Γ (mkApps (tFix mfix idx) args)
  
  | whne_case i p c brs :
      whne Γ c ->
      whne Γ (tCase i p c brs)

  | whne_case_noiota i p c brs :
      RedFlags.iota flags = false ->
      whne Γ (tCase i p c brs)

  | whne_proj p c :
      whne Γ c ->
      whne Γ (tProj p c)

  | whne_proj_noiota p c :
      RedFlags.iota flags = false ->
      whne Γ (tProj p c).

  Lemma whne_mkApps :
    forall Γ t args,
      whne Γ t ->
      whne Γ (mkApps t args).
  Proof.
    intros Γ t args h.
    induction args in t, h |- *.
    - assumption.
    - simpl. eapply IHargs. econstructor. assumption.
  Qed.

  Lemma whnf_mkApps :
    forall Γ t args,
      whne Γ t ->
      whnf Γ (mkApps t args).
  Proof.
    intros. econstructor. now eapply whne_mkApps.
  Qed.
  
  Lemma whne_mkApps_inv :
    forall Γ t l,
      negb (isApp t) ->
      whne Γ (mkApps t l) ->
      whne Γ t \/ exists mfix idx narg body a, t = tFix mfix idx /\ unfold_fix mfix idx = Some (narg, body) /\ nth_error l narg = Some a /\ whne Γ a.
  Proof.
    intros Γ t l Ha h. revert t Ha h.
    induction l using rev_ind; intros.
    - eauto.
    - rewrite mkApps_snoc in h.
      depelim h.
      + edestruct IHl as [ | (? & ? & ? & ? & ? & ? & ? & ? & ?)]; eauto. subst.
        right. exists x0, x1, x2, x3, x4. repeat split; eauto. now eapply nth_error_app_left.
      + rewrite <- mkApps_snoc in x.
        eapply (f_equal decompose_app) in x;
          rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
        inversion x. subst. 
        right. exists mfix, idx, rarg, body, arg. repeat split; eauto.
  Qed.
  
End Normal.

Derive Signature for whnf.
Derive Signature for whne.
Derive Signature for All.
Hint Constructors whnf whne : core.

Local Ltac inv H := inversion H; subst; clear H.

Ltac help' := try repeat match goal with
| [ H0 : _ = mkApps _ _ |- _ ] => 
  eapply (f_equal decompose_app) in H0;
    rewrite !decompose_app_mkApps in H0; cbn in *; firstorder congruence
| [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
  destruct args using rev_ind; cbn in *; [ inv H1 |
                                           rewrite <- mkApps_nested in H1; cbn in *; inv H1
                                  ]
        end.
Ltac help := help'; try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; help'.

Hint Resolve All_Forall : core.

Notation decision P := ({P} + {~P}).

Lemma dec_All X (L : list X) P : All (fun x => decision (P x)) L ->
                                 All P L + (All P L -> False).
Proof.
  intros. induction X0.
  - left. econstructor.
  - destruct p.
    + destruct IHX0. left; econstructor; eauto. right. inversion 1. subst. eauto.
    + right. inversion 1; subst; eauto.
Defined.

Lemma negb_is_true b :
 ~ is_true b -> is_true (negb b).
Proof.
  destruct b; firstorder.
Qed.
Hint Resolve negb_is_true : core.

Lemma whnf_mkApps_inv flags :
  forall Σ Γ t l,
    ~ isApp t ->
    whnf flags Σ Γ (mkApps t l) ->
    whnf flags Σ Γ t.
Proof.
  intros Σ Γ t l Hr h.
  induction l using rev_ind.
  - assumption.
  - rewrite <- mkApps_nested in h. cbn in h. depelim h. depelim H. eauto.
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. eauto. inv x.
      eapply whnf_fixapp with (v := []); eauto. rewrite H. now destruct rarg.    
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_cstrapp with (v := []).
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
        rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_indapp with (v := []).
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_fixapp with (v := []).
      destruct unfold_fix as [[rarg arg] | ]; eauto. now destruct rarg.
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eauto.
Qed.

Lemma whnf_fixapp' {flags} Σ Γ mfix idx narg body v :
unfold_fix mfix idx = Some (narg, body) ->
nth_error v narg = None ->
whnf flags Σ Γ (mkApps (tFix mfix idx) v).
Proof.
 intros E1 H. eapply whnf_fixapp. rewrite E1. eauto.
Qed. 
Hint Resolve whnf_fixapp' : core.

Definition whnf_whne_dec flags Σ Γ t : ({whnf flags Σ Γ t} + {~ (whnf flags Σ  Γ t)}) * ({whne flags Σ Γ t} + {~ (whne flags Σ Γ t)}).
Proof.
  induction t using term_forall_mkApps_ind in Γ |- *; split; eauto.
  all: try now (right; intros H; depelim H;help).
  - destruct (RedFlags.zeta flags) eqn:Er.
    + destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help. 
      * eauto.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help. 
    + eauto.
  - destruct (RedFlags.zeta flags) eqn:Er.
    + destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
      * right. intros H. depelim H. congruence. congruence. help.
      * eauto.
      * right. intros H. depelim H. congruence. congruence. help.
    + eauto.
  - destruct (RedFlags.zeta flags) eqn:Er; eauto.
    right. intros ?. depelim H. depelim H. all:help. congruence.
  - destruct (RedFlags.zeta flags) eqn:Er; eauto.
    right. intros ?. depelim H. congruence. help.
  - destruct (IHt Γ) as [[] _].
    + destruct t. all:try now (left; eauto using whnf_mkApps, All_Forall).
      all: try now left; eapply whnf_mkApps; depelim w; eauto; help.
      * destruct v as [ | ? v].
        -- eauto.
        -- right. intros ?. depelim H0. depelim H0. all:help. clear IHl.
           eapply whne_mkApps_inv in H0 as []; eauto.
           ++ depelim H0. help.
           ++ firstorder congruence.
      * destruct (unfold_fix mfix idx) as [(narg, body) |] eqn:E1.
        -- destruct (nth_error v narg) as [a  | ] eqn:E2.
           ++ destruct (nth_error_all E2 X Γ) as [_ []].
              ** left. eauto.
              ** right. intros ?. depelim H0. depelim H0. all:help. clear IHv. 
                 eapply whne_mkApps_inv in H0 as []; eauto.
                 --- depelim H0. help. 
                     eapply (f_equal decompose_app) in x; 
                     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. 
                     inv x. destruct rarg; inv H1. 
                 --- destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ?). inv H0.
                     rewrite E1 in H1. inv H1.
                     eapply (nth_error_app_left v [x0]) in H2.
                     rewrite E2 in H2. inv H2. eauto.
                 --- help. eapply (f_equal decompose_app) in x; 
                     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
                     inv x. rewrite E1 in H0. congruence. 
           ++ left. eauto.
        -- left. eapply whnf_fixapp. rewrite E1. eauto.
    + right. intros ?. eapply n. now eapply whnf_mkApps_inv. 
  - destruct (IHt Γ) as [_ []].
    + left. now eapply whne_mkApps.
    + destruct t.
      all: try now (right; intros [ | (mfix & idx & narg & body & a & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto).
      * destruct (unfold_fix mfix idx) as [(narg, body) |] eqn:E1.
      -- destruct (nth_error v narg) as [a  | ] eqn:E2.
         ++ destruct (nth_error_all E2 X Γ) as [_ []].
            ** left. eauto.
            ** right. intros ?. depelim H0. depelim H0. all:help. clear IHv. 
               eapply whne_mkApps_inv in H0 as []; eauto.
               destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ?). inv H0.
               rewrite E1 in H1. inv H1.
               eapply (nth_error_app_left v [x0]) in H2.
               rewrite E2 in H2. inv H2. eauto.
         ++ right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
            congruence.
      -- right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
         congruence.
      * right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
  - destruct (RedFlags.delta flags) eqn:Er; eauto.
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help.
      * eauto. 
    +   right. intros H. depelim H. depelim H. congruence. congruence. all:help.
    +   right. intros H. depelim H. depelim H. congruence. congruence. all:help.
  - destruct (RedFlags.delta flags) eqn:Er; eauto.
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. congruence. congruence. help.
      * eauto.
    +   right. intros H. depelim H. congruence. congruence. help.
    +   right. intros H. depelim H. congruence. congruence. help.
  - left. eapply whnf_indapp with (v := []). 
  - left. eapply whnf_cstrapp with (v := []). 
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt2 Γ) as [_ []].
    + eauto. 
    + right. intros ?. depelim H. depelim H. all:help. eauto. congruence.
  -  destruct (RedFlags.iota flags) eqn:Eq; eauto.
     destruct (IHt2 Γ) as [_ []].
    + eauto. 
    + right. intros ?. depelim H. all:help. eauto. congruence.
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. depelim H. all:eauto. all:help.
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. all:help. eauto. congruence.
  - destruct (unfold_fix m n) as [(narg, body) |] eqn:E1.
    + left. eapply whnf_fixapp with (v := []). rewrite E1. now destruct narg.
    + left. eapply whnf_fixapp with (v := []). now rewrite E1.
  - right. intros ?. depelim H. destruct args using rev_ind; try rewrite mkApps_snoc in H3; inv x.
    destruct rarg; inv H0. rewrite mkApps_snoc in H3. inv H3.
  - left. eapply whnf_cofixapp with (v := []).
Defined.

Definition whnf_dec flags Σ Γ t := fst (whnf_whne_dec flags Σ Γ t).
Definition whne_dec flags Σ Γ t := snd (whnf_whne_dec flags Σ Γ t).

(* 
Lemma red1_mkApps_tConstruct_inv Σ Γ i n u v t' :
  red1 Σ Γ (mkApps (tConstruct i n u) v) t' -> ∑ v', (t' = mkApps (tConstruct i n u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x])%list. rewrite mkApps_snoc. split; eauto. admit.
    + exists (v ++ [N2])%list. rewrite mkApps_snoc. split; eauto. 
      eapply OnOne2_app. econstructor. eauto.
Admitted.

Lemma red1_mkApps_tInd_inv Σ Γ i u v t' :
  red1 Σ Γ (mkApps (tInd i u) v) t' -> ∑ v', (t' = mkApps (tInd i u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x])%list. rewrite mkApps_snoc. split; eauto. admit.
    + exists (v ++ [N2])%list. rewrite mkApps_snoc. split; eauto. 
      eapply OnOne2_app. econstructor. eauto.
Admitted.


Ltac hhelp' := try repeat match goal with
                        | [ H0 : _ = mkApps _ _ |- _ ] => 
                          eapply (f_equal decompose_app) in H0;
                          rewrite !decompose_app_mkApps in H0; cbn in *; firstorder congruence
                        | [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
                          destruct args eqn:E using rev_ind ; cbn in *; [ inv H1 |
                                                                   rewrite <- mkApps_nested in H1; cbn in *; inv H1
                                                                 ]
                        end.

Ltac hhelp := hhelp'; try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; hhelp'.

Lemma red1_mkApps_tFix_inv Σ Γ mfix id narg body v t' :
  unfold_fix mfix id = Some (narg, body) ->
  is_constructor narg v = false ->  
  red1 Σ Γ (mkApps (tFix mfix id) v) t' -> (∑ v', (t' = mkApps (tFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
                                          + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
                                          + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  intros ? ?. revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; hhelp; eauto.
  - depelim X; hhelp; eauto.
    + rewrite mkApps_snoc in x. inv x. eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x ++ [x0])%list. split. now rewrite mkApps_snoc. admit. (* OnOne2 app left *)
      * subst. left. right. exists x. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x. split. now rewrite mkApps_snoc. eauto.
      * (* nth_error stuff *) admit.
    + rewrite mkApps_snoc in x. inv x.
      left. left. exists (v ++ [N2])%list. split.
      now rewrite mkApps_snoc. 
      eapply OnOne2_app. econstructor. eauto.
    + rewrite mkApps_snoc in x. inv x.
    + rewrite mkApps_snoc in x. inv x.
Admitted. *)

Lemma whnf_pres1 Σ Γ t t' :
  red1 Σ Γ t t' ->
  (whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t') /\
  (whne RedFlags.default Σ Γ t -> whne RedFlags.default Σ Γ t').
Proof.
  (* intros. induction X using red1_ind_all; split; intros. *)
  (* all: repeat match goal with *)
  (*             | [ H : whnf _ _ _ (?f ?a) |- _ ] => depelim H *)
  (*             | [ H : whne _ _ _ (?f ?a)|- _ ] => depelim H *)
  (*             end. *)
  (* all:try (cbn in *; congruence). *)
  (* all:do 2 help. *)
  (* all: try now eapply whne_mkApps_inv in H; depelim H. *)
  (* all: try destruct IHX; eauto. *)
  (* all: try now match goal with [ H : whne _ _ _ (mkApps _ _) |- _ ] => eapply whne_mkApps_inv in H; depelim H end. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. rewrite H1 in H. inv H. unfold is_constructor in H0. *)
  (*   rewrite H2 in H0. unfold isConstruct_app in H0. *)
  (*   setoid_rewrite mkApps_decompose_app in H3. destruct (decompose_app a).1; inv H0. *)
  (*   eapply whne_mkApps_inv in H3. depelim H3. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. rewrite H1 in H. inv H. unfold is_constructor in H0. *)
  (*   rewrite H2 in H0. congruence. *)
  (* - clear IHv. *)
  (*   eapply red1_mkApps_tConstruct_inv in X as (? & -> & ?). *)
  (*   rewrite <- mkApps_snoc. *)
  (*   eapply whnf_cstrapp.     *)
  (* - clear IHv. *)
  (*   eapply red1_mkApps_tInd_inv in X as (? & -> & ?). *)
  (*   rewrite <- mkApps_snoc. *)
  (*   eapply whnf_indapp. *)
  (* - clear IHargs. *)
  (*   eapply red1_mkApps_tFix_inv in X as [[(? & -> & ?) | (? & -> & ?)] | (? & -> & ?)]; eauto. *)
  (*   + rewrite <- mkApps_snoc. admit. *)
  (*   + rewrite <- mkApps_snoc. eapply whnf_fix. admit. admit. admit. *)
  (*   + rewrite <- mkApps_snoc. eapply whnf_fix. admit. admit. admit. *)
  (*   + unfold is_constructor. destruct (nth_error args narg) eqn:E; eauto. admit.     *)
  (* - clear IHargs. *)
  (*   eapply red1_mkApps_tFix_inv in X as [[(? & -> & ?) | (? & -> & ?)] | (? & -> & ?)]; eauto. *)
  (*   + rewrite <- mkApps_snoc. admit. *)
  (*   + rewrite <- mkApps_snoc. eapply whnf_fix. admit. admit. admit. *)
  (*   + rewrite <- mkApps_snoc. eapply whnf_fix. admit. admit. admit. *)
  (*   + unfold is_constructor. destruct (nth_error args narg) eqn:E; eauto. admit.     *)
  (* - clear IHv. rewrite <- mkApps_snoc. eauto. *)
  (* - rewrite <- mkApps_snoc. eauto. *)
  (* - clear IHargs. *)
  (*   destruct (nth_error args narg) eqn:E. *)
  (*   + assert (E' := E). *)
  (*     eapply nth_error_app_left in E. rewrite E in H0. inv H0. *)
  (*     rewrite <- mkApps_snoc. *)
  (*     eapply whnf_fix. eauto. *)
  (*     eapply nth_error_app_left. eauto. eauto. *)
  (*   + assert (E' := E). *)
  (*     eapply nth_error_None in E. rewrite nth_error_app_ge in H0; eauto. *)
  (*     destruct (narg - #|args|) eqn:En; cbn in H0.  *)
  (*     * inv H0. rewrite <- mkApps_snoc. *)
  (*       eapply whnf_fix. eauto. rewrite nth_error_app_ge. lia. rewrite En. reflexivity. eauto.  *)
  (*     * destruct n; inv H0. *)
  (* - clear IHargs. rewrite <- mkApps_snoc. *)
  (*   eapply whnf_fix_short. eauto. rewrite nth_error_None. *)
  (*   setoid_rewrite nth_error_None in H0. rewrite app_length. *)
  (*   setoid_rewrite app_length in H0. cbn in *. lia. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. destruct narg; inv H0. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. eapply whnf_fix_short with (args := []). admit. admit. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. destruct narg; inv H0. *)
  (* - eapply (f_equal decompose_app) in x; *)
  (*     rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  *)
  (*   inv x. eapply whnf_fix_short with (args := []). admit. admit. *)
Admitted.    

Lemma whnf_pres Σ Γ t t' :
  red Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t'.
Proof.
  induction 1; intros.
  - eauto.
  - eapply whnf_pres1; eauto.
Qed.

Lemma whnf_red1_sort Σ Γ t u :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t (tSort u) -> t = tSort u.
Proof.
  intros. remember (tSort u) as t'. 
  induction X using red1_ind_all.
  all: repeat match goal with
         | [ H : whnf _ _ _ (?f ?a) |- _ ] => depelim H
         | [ H : whne _ _ _ (?f ?a)|- _ ] => depelim H
         end.
  all:try (cbn in *; congruence).
  all:do 2 help.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. rewrite H2 in H. inv H.
    destruct args0 using rev_ind; cbn in *.
    destruct rarg; inv H0.
    rewrite mkApps_snoc in  Heqt'. congruence.
  - destruct args using rev_ind.
    + inv Heqt'. destruct narg; inv H1.
    + rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply whne_mkApps_inv in H as [ | (? & ? & ? & ? & ? & ? & ? & ? & ?)]; cbn; eauto.
    depelim H. help. congruence.  
Qed.

Lemma whnf_red_sort Σ Γ t u :
  whnf RedFlags.default Σ Γ t ->
  red Σ Γ t (tSort u) -> t = tSort u.
Proof.
  intros. remember (tSort u) as t'. induction X.
  - eauto.
  - subst. eapply whnf_red1_sort in r. subst. eauto.
    eapply whnf_pres; eauto.
Qed.

Lemma whnf_red1_prod Σ Γ t na t1 t2 :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t (tProd na t1 t2) -> exists t1 t2, t = tProd na t1 t2.
Proof.
  intros. remember (tProd na t1 t2) as t'. 
  induction X using red1_ind_all.
  all: repeat match goal with
         | [ H : whnf _ _ _ (?f ?a) |- _ ] => depelim H
         | [ H : whne _ _ _ (?f ?a)|- _ ] => depelim H
         end.
  all:try (cbn in *; congruence).
  all:do 2 help.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. rewrite H2 in H. inv H.
    destruct args0 using rev_ind; cbn in *.
    destruct rarg; inv H0.
    rewrite mkApps_snoc in  Heqt'. congruence.
  - destruct args using rev_ind.
    + inv Heqt'. destruct narg; inv H1.
    + rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - inv Heqt'. eauto.
  - inv Heqt'. eauto.
Qed.

Lemma whnf_red_prod Σ Γ t na t1 t2 :
  whnf RedFlags.default Σ Γ t ->
  red Σ Γ t (tProd na t1 t2) -> exists t1 t2, t = tProd na t1 t2.
Proof.
  intros. remember (tProd na t1 t2) as t'. revert t1 t2 Heqt'. induction X; intros.
  - eauto.
  - subst. eapply whnf_red1_prod in r as (? & ? & ?). subst. eauto.
    eapply whnf_pres; eauto.
Qed.

(* 

  Definition head_arg_is_constructor mfix idx args :=
    match unfold_fix mfix idx with Some (narg, body) => is_constructor narg args | None => false end.
  

  Inductive normal (Γ : context) : term -> Prop :=
  | nf_ne t : neutral Γ t -> normal Γ t
  | nf_lam na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                    normal Γ (tLambda na A B)
  | nf_cstrapp i n u v : All (normal Γ) v -> normal Γ (mkApps (tConstruct i n u) v)
  | nf_indapp i u v : All (normal Γ) v -> normal Γ (mkApps (tInd i u) v)
  | nf_fix mfix idx args : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                           All (normal Γ) args ->
                           head_arg_is_constructor mfix idx args = false ->
                           All (compose (normal Γ) dtype) mfix ->
                      normal Γ (mkApps (tFix mfix idx) args)
  | nf_cofix mfix idx : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                      All (compose (normal Γ) dtype) mfix ->
                        normal Γ (tCoFix mfix idx)

  with neutral (Γ : context) : term -> Prop :=
  | ne_rel i :
      (forall b, option_map decl_body (nth_error Γ i) <> Some (Some b)) ->
      neutral Γ (tRel i)
  | ne_var v : neutral Γ (tVar v)
  | ne_evar n l : neutral Γ (tEvar n l)
  | ne_const c u :
      (forall decl b, lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = Some b -> False) ->
      neutral Γ (tConst c u)
  | ne_sort s : neutral Γ (tSort s)
  | ne_prod na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                     neutral Γ (tProd na A B)
  | ne_app f v : neutral Γ f -> normal Γ v -> neutral Γ (tApp f v)
  | ne_case i p c brs : neutral Γ c -> normal Γ p -> All (compose (normal Γ) snd) brs ->
                        neutral Γ (tCase i p c brs)
  | ne_proj p c : neutral Γ c -> neutral Γ (tProj p c).

Definition normal_neutral_dec Σ Γ t : ({normal Σ Γ t} + {~ (normal Σ  Γ t)}) * ({neutral Σ Γ t} + {~ (neutral Σ Γ t)}).
Proof.
  induction t using term_forall_mkApps_ind in Γ |- *; split; eauto.
  all: try now (right; intros H; depelim H).
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. depelim H. congruence. help. help. help.
    + eauto.
    + right. intros H. depelim H. depelim H. congruence. help. help. help.
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. congruence.
    + eauto.
    + right. intros H. depelim H. congruence.
  - todo "evar".
  - todo "evar".
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. eauto. 
    + right. intros H. depelim H. eauto.
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - right. intros H. depelim H. depelim H. help. help. help.
  - destruct (IHt Γ) as [[] _].
    + destruct dec_All with (P := (normal Σ Γ)) (L := v).
      -- eapply All_impl. eassumption. intros ? ?. apply X0.
      -- destruct t. all:eauto using normal_mkApps, All_Forall.
         all: try now (left; depelim n; help; eauto).
         ++ destruct v as [ | ? v].
            ** eauto.
            ** right. todo "admit". (*  intros ?. depelim X. depelim X. all:help. clear IHt. *)
               (* eapply neutral_mk_Apps_inv in H0. as []; eauto. *)
               (* depelim H1. *)
         ++ destruct (head_arg_is_constructor mfix idx v) eqn:E.
            ** right. intros ?. todo "admit". (* depelim H1. depelim H1. all:help. clear IHv. *)
               (* eapply neutral_mk_Apps_inv in H1 as []; eauto. depelim H1. *)
            ** left. todo "admit". (* depelim n. all:help. depelim H1. *)
               (* eapply (f_equal decompose_app) in x; *)
               (*   rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x. *)
               (* eauto. *)
         ++ todo "cofix".
      -- right. intros ?. eapply f. eapply Forall_All.
         now eapply normal_mk_Apps_inv.
    + right. intros ?. eapply n. now eapply normal_mk_Apps_inv.
  - destruct v using rev_ind.
    + cbn. eapply IHt.
    + rewrite <- mkApps_nested. cbn.
      eapply All_app in X as []. eapply IHv in a. inv a0. clear X0.
      rename X into IHt2.
      revert a.
      generalize (mkApps t v) as t1. intros t1 IHt1.
      destruct (IHt1) as [];
      [destruct (IHt2 Γ) as [[] _]|]; eauto.
      * right. intros HH. depelim HH. eauto.
      * right. intros HH. depelim HH. eauto.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. depelim H. congruence. help. help. help.
      * eauto. 
    +   right. intros H. depelim H. depelim H. congruence. help. help. help.
    +   right. intros H. depelim H. depelim H. congruence. help. help. help.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. congruence.
      * eauto. 
    +   right. intros H. depelim H. congruence.
    +   right. intros H. depelim H. congruence.
  - left. eapply nf_indapp with (v := []). econstructor.
  - left. eapply nf_cstrapp with (v := []). econstructor.
  - destruct (IHt2 Γ) as [_ []].
    + destruct (IHt1 Γ) as [[] _].
      * destruct dec_All with(L := l) (P := (normal Σ Γ ∘ @snd nat term)).
        -- eapply All_impl. eassumption. intros ? ?. eapply X0.
        -- eauto.
        -- right. intros ?. depelim H. depelim H. all:help. eauto.
      * right. intros ?. depelim H. depelim H. all:help. eauto.
    + right. intros ?. depelim H. depelim H. all:help. eauto.
  -  destruct (IHt2 Γ) as [_ []].
    + destruct (IHt1 Γ) as [[] _].
      * destruct dec_All with(L := l) (P := (normal Σ Γ ∘ @snd nat term)).
        -- eapply All_impl. eassumption. intros ? ?. eapply X0.
        -- eauto.
        -- right. intros ?. depelim H. all:help. eauto.
      * right. intros ?. depelim H. all:help. eauto.
    + right. intros ?. depelim H. all:help. eauto.
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. eauto.
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply X0.

    destruct dec_All with (P := normal Σ  (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply X0.

    + left. eapply nf_fix with (args := []). eauto. eauto. unfold head_arg_is_constructor.
      destruct unfold_fix; eauto. destruct p.
      unfold is_constructor. destruct n0; eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. eapply f.
      eapply (f_equal decompose_app) in x;
        rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x.
      eauto.
    + right. intros H. depelim H. depelim H. help. help. 
      eapply (f_equal decompose_app) in x;
        rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x.
      eauto.      
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply X0.

    destruct dec_All with (P := normal Σ (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply X0.

    + left. eapply nf_cofix. eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. help. eauto.
    + right. intros H. depelim H. depelim H. help. help. help. eauto.
Defined.

Definition normal_dec Σ Γ t := fst (normal_neutral_dec Σ Γ t).
Definition neutral_dec Σ Γ t := snd (normal_neutral_dec Σ Γ t).
 *)


(* 


Lemma OnOn2_contra A  (P : A -> A -> Type) l1 l2 : (forall x y, P x y -> False) -> OnOne2 P l1 l2 -> False.
Proof.
  intros. induction X; eauto.
Qed.

Lemma normal_nf Σ Γ t t' : normal Σ Γ t \/ neutral Σ Γ t -> red1 Σ Γ t t' -> False.
Proof.
  intros. induction X using red1_ind_all; destruct H.
  all: repeat match goal with
         | [ H : normal _ _ (?f ?a) |- _ ] => depelim H
         | [ H : neutral _ _ (?f ?a)|- _ ] => depelim H
         end.
  all: try congruence.
  all: help.
  all: try tauto.
  all: try now (clear - H; depind H; help; eauto).
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. unfold head_arg_is_constructor in H.
    rewrite H0 in H. congruence.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply IHX. left.
    eapply nf_cstrapp. now eapply All_app in X as [X _].
  - eapply IHX. left.
    eapply nf_indapp. now eapply All_app in X as [X _].
  - clear IHargs.
    eapply IHX. left.
    eapply nf_fix.
    + eauto.
    + eapply All_app in X0. eapply X0.
    + unfold head_arg_is_constructor in *.
      destruct unfold_fix; eauto. destruct p.
      unfold is_constructor in *.
      destruct (nth_error args n) eqn:E; eauto.
      erewrite nth_error_app_left in H; eauto.
    + eauto.
  - eapply IHX. left.
    eapply All_app in X as [_ X]. now inv X.
  - eapply IHX. left.
    eapply All_app in X as [_ X]. now inv X.
  - eapply IHX. left.
    eapply All_app in X0 as [_ X0]. now inv X0.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. inv x.
    eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
(*     firstorder. *)
(*   - eapply (f_equal decompose_app) in x; *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. inv x. *)
(*     eapply OnOne2_All_mix_left in X. 2:exact H. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(*   - eapply OnOne2_All_mix_left in X. 2:exact H0. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(*   - eapply OnOne2_All_mix_left in X. 2:exact H. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(* Qed. *)
Admitted.

Hint Constructors normal neutral : core.

Lemma normal_mk_Apps_inv:
  forall (Σ : global_env) (Γ : context) (t : term) (v : list term), ~ isApp t -> normal Σ Γ (mkApps t v) -> normal Σ Γ t /\ Forall (normal Σ Γ) v.
Proof.
(*   intros Σ Γ t v H H1. *)
(*   induction v using rev_ind. *)
(*   - split. eapply H1. econstructor.  *)
(*   - rewrite <- mkApps_nested in H1. cbn in H1. depelim H1. depelim H0. *)
(*     + split. *)
(*       * firstorder. *)
(*       * eapply app_Forall. firstorder. firstorder. *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_cstrapp with (v := []). econstructor. *)
(*       now eapply All_Forall.  *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_indapp with (v := []). econstructor. *)
(*       now eapply All_Forall. *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_fix with (args := []). *)
(*       * eauto. *)
(*       * econstructor. *)
(*       * unfold head_arg_is_constructor in *. *)
(*         destruct unfold_fix; eauto. destruct p. *)
(*         unfold is_constructor in *. destruct n; reflexivity. *)
(*       * eauto. *)
(*       * now eapply All_Forall. *)
(* Qed. *)
Admitted.

Lemma neutral_mk_Apps_inv:
  forall (Σ : global_env) (Γ : context) (t : term) (v : list term), ~ isApp t -> neutral Σ Γ (mkApps t v) -> neutral Σ Γ t /\ Forall (normal Σ Γ) v.
Proof.
  intros Σ Γ t v H H1.
  induction v using rev_ind.
  - split. eapply H1. econstructor. 
  - rewrite <- mkApps_nested in H1. cbn in H1. depelim H1. 
    split.
    + firstorder.
    + eapply app_Forall. firstorder. firstorder.
Qed.

Lemma normal_mkApps Σ Γ t v :
  neutral Σ Γ t -> Forall (normal Σ Γ) v -> normal Σ Γ (mkApps t v).
Proof.
  intros. induction H0 in t, H |- *; cbn in *.
  - eauto.
  - eapply IHForall. eauto.
Qed.  
 *)