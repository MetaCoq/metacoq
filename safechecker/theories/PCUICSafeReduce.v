(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICPosition
     PCUICNormal PCUICInversion PCUICCumulativity PCUICSafeLemmata
     PCUICGeneration PCUICValidity PCUICSR PCUICSN.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Import MonadNotation.
Open Scope type_scope.

(** * Reduction machine for PCUIC without fuel

  We subsume the reduction machine of PCUICChecker without relying on fuel.
  Instead we assume strong normalisation of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the ocaml implementation.

 *)

Set Equations With UIP.
Local Set Keyed Unification.

(* We assume normalisation of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Measure.

  Context {cf : checker_flags}.

  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).

  Definition R_aux Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Γ u v :=
    R_aux Γ (zip u ; stack_pos (fst u) (snd u))
            (zip v ; stack_pos (fst v) (snd v)).

  Lemma cored_wellformed :
    forall {Γ u v},
      ∥ wf Σ ∥ -> wellformed Σ Γ u ->
      cored (fst Σ) Γ v u ->
      wellformed Σ Γ v.
  Proof.
    intros Γ u v HΣ h r.
    destruct HΣ as [wΣ].
    revert h. induction r ; intros h.
    - destruct h as [A|A]; [left|right].
      destruct A as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
      sq; eapply isWfArity_red1 ; eassumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A|A]; [left|right].
      destruct A as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
      sq; eapply isWfArity_red1 ; eassumption.
  Qed.

  Lemma red_wellformed :
    forall {Γ u v},
      ∥ wf Σ ∥ -> wellformed Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      wellformed Σ Γ v.
  Proof.
    intros hΣ Γ u v h [r]. apply red_cored_or_eq in r.
    destruct r as [r|[]]; [|assumption].
    eapply cored_wellformed; eassumption.
  Qed.

  Corollary R_Acc_aux :
    forall Γ t p,
      wf Σ -> wellformed Σ Γ t ->
      Acc (R_aux Γ) (t ; p).
  Proof.
    intros Γ t p HΣ h.
    eapply dlexprod_Acc.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - eapply normalisation'; eassumption.
  Qed.

  Derive Signature for Acc.

  Corollary R_Acc :
    forall Γ t,
      wf Σ -> wellformed Σ Γ (zip t) ->
      Acc (R Γ) t.
  Proof.
    intros Γ t HΣ h.
    pose proof (R_Acc_aux _ _ (stack_pos (fst t) (snd t)) HΣ h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    now eapply H0.
  Qed.

  Lemma R_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; p1) (t2 ; p2).
  Proof.
    intros Γ t1 t2 p1 p2 e h.
    subst. right. assumption.
  Qed.

  Definition Req Γ t t' :=
    t = t' \/ R Γ t t'.

  Lemma Rtrans :
    forall Γ u v w,
      R Γ u v ->
      R Γ v w ->
      R Γ u w.
  Proof.
    intros Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Γ}, transitive (Req Γ).
  Proof.
    intros Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Γ u v},
      R Γ u v ->
      Req Γ u v.
  Proof.
    intros Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Γ, Reflexive (Req Γ).
  Proof.
    intros Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Γ u v w},
      R Γ u v ->
      Req Γ v w ->
      R Γ u w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Measure.

Section Reduce.

  Context {cf : checker_flags}.

  Context (flags : RedFlags.t).

  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥).

  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  Existing Instance Req_refl.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Notation givePr := (_) (only parsing).

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Notation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist res (conj prf (conj h (conj h1 h2)))) := reduce t π smaller in
     exist res (conj (Req_trans _ _ _ _ _ (R_to_Req _ smaller)) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist (t,π) (conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Lemma Req_red :
    forall Γ x y,
      Req Σ Γ y x ->
      ∥ red Σ Γ (zip x) (zip y) ∥.
  Proof.
    intros Γ [t π] [t' π'] h. cbn.
    dependent destruction h.
    - repeat zip fold. rewrite H.
      constructor. constructor.
    - dependent destruction H.
      + eapply cored_red. assumption.
      + cbn in H0. inversion H0.
        constructor. constructor.
  Qed.

  (* Show Obligation Tactic. *)

  Ltac obTac :=
    (* program_simpl ; *)
    program_simplify ;
    Tactics.equations_simpl ;
    try program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Set :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  (* Tailored view for _reduce_stack *)
  Equations red_discr (t : term) (π : stack) : Prop :=
    red_discr (tRel _) _ := False ;
    red_discr (tLetIn _ _ _ _) _ := False ;
    red_discr (tConst _ _) _ := False ;
    red_discr (tApp _ _) _ := False ;
    red_discr (tLambda _ _ _) (App _ _) := False ;
    red_discr (tFix _ _) _ := False ;
    red_discr (tCase _ _ _ _) _ := False ;
    red_discr (tProj _ _) _ := False ;
    red_discr _ _ := True.

  Inductive red_view : term -> stack -> Set :=
  | red_view_Rel c π : red_view (tRel c) π
  | red_view_LetIn A b B c π : red_view (tLetIn A b B c) π
  | red_view_Const c u π : red_view (tConst c u) π
  | red_view_App f a π : red_view (tApp f a) π
  | red_view_Lambda na A t a args : red_view (tLambda na A t) (App a args)
  | red_view_Fix mfix idx π : red_view (tFix mfix idx) π
  | red_view_Case ind par p c brs π : red_view (tCase (ind, par) p c brs) π
  | red_view_Proj p c π : red_view (tProj p c) π
  | red_view_other t π : red_discr t π -> red_view t π.

  Equations red_viewc t π : red_view t π :=
    red_viewc (tRel c) π := red_view_Rel c π ;
    red_viewc (tLetIn A b B c) π := red_view_LetIn A b B c π ;
    red_viewc (tConst c u) π := red_view_Const c u π ;
    red_viewc (tApp f a) π := red_view_App f a π ;
    red_viewc (tLambda na A t) (App a args) := red_view_Lambda na A t a args ;
    red_viewc (tFix mfix idx) π := red_view_Fix mfix idx π ;
    red_viewc (tCase (ind, par) p c brs) π := red_view_Case ind par p c brs π ;
    red_viewc (tProj p c) π := red_view_Proj p c π ;
    red_viewc t π := red_view_other t π I.

  Equations discr_construct_cofix (t : term) : Prop :=
    discr_construct_cofix (tConstruct ind n ui) := False ;
    discr_construct_cofix (tCoFix mfix idx) := False ;
    discr_construct_cofix _ := True.

  Inductive construct_cofix_view : term -> Set :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Equations cc_viewc t : construct_cofix_view t :=
    cc_viewc (tConstruct ind n ui) := ccview_construct ind n ui ;
    cc_viewc (tCoFix mfix idx) := ccview_cofix mfix idx ;
    cc_viewc t := ccview_other t I.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : wellformed Σ Γ (zip (t,π)))
            (reduce : forall t' π', R Σ Γ (t',π') (t,π) ->
                               { t'' : term * stack | Req Σ Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | Req Σ Γ t' (t,π) /\ Pr t' π /\ Pr' t' } :=

    _reduce_stack Γ t π h reduce with red_viewc t π := {

    | red_view_Rel c π with RedFlags.zeta flags := {
      | true with inspect (nth_error (Γ ,,, stack_context π) c) := {
        | @exist None eq := False_rect _ _ ;
        | @exist (Some d) eq with inspect d.(decl_body) := {
          | @exist None _ := give (tRel c) π ;
          | @exist (Some b) H := rec reduce (lift0 (S c) b) π
          }
        } ;
      | false := give (tRel c) π
      } ;

    | red_view_LetIn A b B c π with RedFlags.zeta flags := {
      | true := rec reduce (subst10 b c) π ;
      | false := give (tLetIn A b B c) π
      } ;

    | red_view_Const c u π with RedFlags.delta flags := {
      | true with inspect (lookup_env (fst Σ) c) := {
        | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
          let body' := subst_instance_constr u body in
          rec reduce body' π ;
        | @exist (Some (InductiveDecl _ _)) eq := False_rect _ _ ;
        | @exist (Some _) eq := give (tConst c u) π ;
        | @exist None eq := False_rect _ _
        } ;
      | _ := give (tConst c u) π
      } ;

    | red_view_App f a π := rec reduce f (App a π) ;

    | red_view_Lambda na A t a args with inspect (RedFlags.beta flags) := {
      | @exist true eq1 := rec reduce (subst10 a t) args ;
      | @exist false eq1 := give (tLambda na A t) (App a args)
      } ;

    | red_view_Fix mfix idx π with RedFlags.fix_ flags := {
      | true with inspect (unfold_fix mfix idx) := {
        | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
          | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix mfix idx args ρ) _) := {
            | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
              | view_construct ind n ui with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  rec reduce fn (appstack args (App (mkApps (tConstruct ind n ui) l) ρ))
                } ;
              | view_other t ht := give (tFix mfix idx) π
              }
            } ;
          | _ := give (tFix mfix idx) π
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | false := give (tFix mfix idx) π
      } ;

    | red_view_Case ind par p c brs π with RedFlags.iota flags := {
      | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc_viewc t := {
            | ccview_construct ind' c' _ := rec reduce (iota_red par c' args brs) π ;
            | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (narg, fn)) eq' :=
                rec reduce (tCase (ind, par) p (mkApps fn args) brs) π ;
              | @exist None bot := False_rect _ _
              } ;
            | ccview_other t ht := give (tCase (ind, par) p (mkApps t args) brs) π
            }
          }
        } ;
      | false := give (tCase (ind, par) p c brs) π
      } ;

    | red_view_Proj (i, pars, narg) c π with RedFlags.iota flags := {
      | true with inspect (reduce c (Proj (i, pars, narg) π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc_viewc t := {
            | ccview_construct ind' c' _
              with inspect (nth_error args (pars + narg)) := {
              | @exist (Some arg) eqa := rec reduce arg π ;
              | @exist None eqa := False_rect _ _
              } ;
            | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (narg, fn)) eq' :=
                rec reduce (tProj (i, pars, narg) (mkApps fn args)) π ;
              | @exist None bot := False_rect _ _
              } ;
            | ccview_other t ht := give (tProj (i, pars, narg) (mkApps t args)) π
            }
          }
        } ;
      | false := give (tProj (i, pars, narg) c) π
      } ;

    | red_view_other t π discr := give t π

    }.

  (* tRel *)
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    pose proof (wellformed_context _ hΣ _ _ h) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    destruct hΣ as [wΣ].
    clear - eq hc wΣ.
    revert c hc eq.
    generalize (Γ ,,, stack_context π) as Δ. clear Γ π.
    intro Γ.
    induction Γ ; intros c hc eq.
    - destruct hc as [[A h]|[[ctx [s [e _]]]]]; [|discriminate].
      apply inversion_Rel in h as hh ; auto.
      destruct hh as [? [? [e ?]]].
      rewrite e in eq. discriminate eq.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption.
        destruct hc as [[A h]|[[ctx [s [e _]]]]] ; try discriminate.
        apply inversion_Rel in h as hh ; auto.
        destruct hh as [? [? [e ?]]].
        cbn in e. rewrite e in eq. discriminate.
  Qed.

  (* tLetIn *)
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.

  (* tConst *)
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    (* Should be a lemma! *)
    - unfold declared_constant. rewrite <- eq. f_equal.
      f_equal. clear - eq.
      revert c wildcard0 body wildcard1 wildcard2 eq.
      set (Σ' := fst Σ). clearbody Σ'. clear Σ. rename Σ' into Σ.
      induction Σ ; intros c na t body univ eq.
      + cbn in eq. discriminate.
      + cbn in eq. revert eq.
        case_eq (ident_eq c (global_decl_ident a)).
        * intros e eq. inversion eq. subst. clear eq.
          cbn in e. revert e. destruct (ident_eq_spec c na) ; easy.
        * intros e eq. eapply IHg. eassumption.
    - cbn. reflexivity.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    eapply wellformed_context in h ; auto. simpl in h.
    destruct h as [[T h]|[[ctx [s [e _]]]]]; [|discriminate].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant in d. rewrite <- eq in d.
    discriminate.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    eapply wellformed_context in h ; auto. simpl in h.
    destruct h as [[T h]|[[ctx [s [e _]]]]]; [|discriminate].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant in d. rewrite <- eq in d.
    discriminate.
  Qed.

  (* tApp *)
  Next Obligation.
    right.
    cbn. unfold posR. cbn.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. rewrite e in h. cbn in h.
    assumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    case_eq (decompose_stack args). intros l ρ e.
    cbn. unfold Pr in h. rewrite e in h. cbn in h.
    assumption.
  Qed.
  Next Obligation.
    rewrite β in eq1. discriminate.
  Qed.

  (* tFix *)
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    eapply R_positionR.
    - cbn. rewrite zipc_appstack. cbn. reflexivity.
    - cbn. rewrite stack_position_appstack. cbn.
      rewrite <- app_assoc.
      eapply positionR_poscat.
      constructor.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        unfold isConstruct_app.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H0. subst.
        destruct ll.
        * cbn in H3. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H3. discriminate H3.
      + dependent destruction H0.
        * cbn in H0. rewrite 2!zipc_appstack in H0.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr in p. cbn in p.
             rewrite e1 in p. cbn in p. subst.
             cbn in H0.
             clear - H0.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H0 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * cbn in H1. inversion H1.
          rewrite 2!zipc_appstack in H3.
          unfold Pr in p. cbn in p.
          rewrite e1 in p. cbn in p. subst.
          cbn in H3. rewrite zipc_appstack in H3.
          apply zipc_inj in H3.
          apply PCUICAstUtils.mkApps_inj in H3.
          inversion H3. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l1 ρ1 e.
    rewrite e in h. cbn in h. subst.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack. cbn.
    rewrite e. cbn. reflexivity.
  Qed.

  (* tCase *)
  Next Obligation.
    right. unfold posR. cbn.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    eapply R_Req_R.
    - econstructor. econstructor. eapply red1_context.
      eapply red_iota.
    - instantiate (4 := ind'). instantiate (2 := p).
      instantiate (1 := wildcard9).
      destruct r.
      + inversion e.
        subst.
        cbn in prf'. inversion prf'. subst. clear prf'.
        cbn.
        assert (ind = ind').
        { clear - h flags hΣ.
          apply wellformed_context in h ; auto.
          simpl in h.
          eapply Case_Construct_ind_eq with (args := []) ; eauto.
        } subst.
        reflexivity.
      + clear eq. dependent destruction r.
        * cbn in H.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H.
          cbn in H.
          right. econstructor.
          lazymatch goal with
          | h : cored _ _ ?t _ |- _ =>
            assert (wellformed Σ Γ t) as h'
          end.
          { clear - h H flags hΣ.
            eapply cored_wellformed ; try eassumption.
          }
          assert (ind = ind').
          { clear - h' flags hΣ H.
            zip fold in h'.
            apply wellformed_context in h'.
            cbn in h'.
            apply Case_Construct_ind_eq in h'. all: eauto.
          } subst.
          exact H.
        * cbn in H0. inversion H0. subst. clear H0.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H2. cbn in H2.
          apply zipc_inj in H2.
          inversion H2. subst.
          assert (ind = ind').
          { clear - h flags H hΣ.
            apply wellformed_context in h.
            cbn in h.
            apply Case_Construct_ind_eq in h. all: eauto.
          } subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    dependent destruction r.
    - inversion e. subst.
      left. eapply cored_context.
      constructor.
      simpl in prf'. inversion prf'. subst.
      eapply red_cofix_case with (args := []). eauto.
    - clear eq.
      dependent destruction r.
      + left.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply cored_trans' ; try eassumption.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_case. eauto.
      + left.
        cbn in H0. destruct y'. inversion H0. subst. clear H0.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        rewrite zipc_appstack in H2. cbn in H2.
        cbn. rewrite H2.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_case. eauto.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    assert (h' : wellformed Σ Γ (zip (tCase (ind, par) p (mkApps (tCoFix mfix idx) args) brs, π))).
    { dependent destruction r.
      - inversion e. subst.
        simpl in prf'. inversion prf'. subst.
        assumption.
      - clear eq. dependent destruction r.
        + apply cored_red in H. destruct H as [r].
          eapply red_wellformed ; eauto.
          constructor.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          cbn in r. rewrite zipc_appstack in r. cbn in r.
          assumption.
        + cbn in H0. destruct y'. inversion H0. subst. clear H0.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          rewrite zipc_appstack in H2. cbn in H2.
          cbn. rewrite <- H2. assumption.
    }
    replace (zip (tCase (ind, par) p (mkApps (tCoFix mfix idx) args) brs, π))
      with (zip (tCoFix mfix idx, appstack args (Case (ind, par) p brs π)))
      in h'.
    - destruct hΣ.
      apply wellformed_context in h' ; auto. simpl in h'.
      destruct h' as [[T h']|[[ctx [s [e _]]]]]; [|discriminate].
      apply inversion_CoFix in h' ; auto.
      destruct h' as [decl [? [e [? [? ?]]]]].
      unfold unfold_cofix in bot.
      rewrite e in bot. discriminate.
    - cbn. rewrite zipc_appstack. reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H. subst.
      clear H.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      rewrite <- prf' in p0. cbn in p0. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* tProj *)
  Next Obligation.
    right. unfold posR. cbn.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    left.
    apply Req_red in r as hr.
    pose proof (red_wellformed _ hΣ h hr) as hh.
    destruct hr as [hr].
    eapply cored_red_cored ; try eassumption.
    unfold Pr in p. simpl in p. pose proof p as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst. cbn. rewrite zipc_appstack. cbn.
    do 2 zip fold. eapply cored_context.
    constructor.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh. apply wellformed_context in hh.
    simpl in hh. apply Proj_Constuct_ind_eq in hh. all: eauto.
    subst. constructor. eauto.
  Qed.
  Next Obligation.
    unfold Pr in p. simpl in p.
    pose proof p as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst.
    apply Req_red in r as hr.
    pose proof (red_wellformed _ hΣ h hr) as hh.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh.
    apply wellformed_context in hh. simpl in hh.
    apply Proj_red_cond in hh. all: eauto.
  Qed.
  Next Obligation.
    unfold Pr in p. simpl in p.
    pose proof p as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    dependent destruction r.
    - inversion e. subst.
      left. eapply cored_context.
      constructor.
      simpl in prf'. inversion prf'. subst.
      eapply red_cofix_proj with (args := []). eauto.
    - clear eq.
      dependent destruction r.
      + left.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply cored_trans' ; try eassumption.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
      + left.
        cbn in H0. destruct y'. inversion H0. subst. clear H0.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        rewrite zipc_appstack in H2. cbn in H2.
        cbn. rewrite H2.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    unfold Pr in p. simpl in p.
    pose proof p as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    assert (h' : wellformed Σ Γ (zip (tProj (i, pars, narg) (mkApps (tCoFix mfix idx) args), π))).
    { dependent destruction r.
      - inversion e. subst.
        simpl in prf'. inversion prf'. subst.
        assumption.
      - clear eq. dependent destruction r.
        + apply cored_red in H. destruct H as [r].
          eapply red_wellformed ; eauto.
          constructor.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          cbn in r. rewrite zipc_appstack in r. cbn in r.
          assumption.
        + cbn in H0. destruct y'. inversion H0. subst. clear H0.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          rewrite zipc_appstack in H2. cbn in H2.
          cbn. rewrite <- H2. assumption.
    }
    replace (zip (tProj (i, pars, narg) (mkApps (tCoFix mfix idx) args), π))
      with (zip (tCoFix mfix idx, appstack args (Proj (i, pars, narg) π)))
      in h'.
    - destruct hΣ.
      apply wellformed_context in h' ; auto. simpl in h'.
      destruct h' as [[T h']|[[ctx [s [e _]]]]]; [|discriminate].
      apply inversion_CoFix in h' ; auto.
      destruct h' as [decl [? [e [? [? ?]]]]].
      unfold unfold_cofix in bot.
      rewrite e in bot. discriminate.
    - cbn. rewrite zipc_appstack. reflexivity.
  Qed.
  Next Obligation.
    clear eq.
    dependent destruction r.
    - inversion H. subst. cbn in prf'. inversion prf'. subst.
      cbn. reflexivity.
    - unfold Pr in p. cbn in p.
      rewrite <- prf' in p. cbn in p. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* Other *)
  Next Obligation.
    revert discr.
    apply_funelim (red_discr t π). all: auto.
    easy.
  Qed.
  Next Obligation.
    revert discr hl.
    apply_funelim (red_discr t π). all: easy.
  Qed.

(* Added by Julien Forest on 13/11/20 in Coq stdlib, adapted to subset case by M. Sozeau *)
Section Acc_sidecond_generator.
  Context {A : Type} {R : A -> A -> Prop} {P : A -> Prop}.
  Variable Pimpl : forall x y, P x -> R y x -> P y.
  (* *Lazily* add 2^n - 1 Acc_intro on top of wf.
     Needed for fast reductions using Function and Program Fixpoint
     and probably using Fix and Fix_F_2
   *)
  Fixpoint Acc_intro_generator n (acc : forall t, P t -> Acc R t) : forall t, P t -> Acc R t :=
    match n with
        | O => acc
        | S n => fun x Px =>
                   Acc_intro x (fun y Hy => Acc_intro_generator n (Acc_intro_generator n acc) y (Pimpl _ _ Px Hy))
    end.


End Acc_sidecond_generator.

  Lemma wellformed_R_pres Γ :
    forall x y : term × stack, wellformed Σ Γ (zip x) -> R Σ Γ y x -> wellformed Σ Γ (zip y).
  Proof. intros. todo "wellformed_R_pres proof"%string. Admitted.

  Equations reduce_stack_full (Γ : context) (t : term) (π : stack)
           (h : wellformed Σ Γ (zip (t,π))) : { t' : term * stack | Req Σ Γ t' (t, π) /\ Pr t' π /\ Pr' t' } :=
    reduce_stack_full Γ t π h :=
      Fix_F (R := R Σ Γ)
            (fun x => wellformed Σ Γ (zip x) -> { t' : term * stack | Req Σ Γ t' x /\ Pr t' (snd x) /\ Pr' t' })
            (fun t' f => _) (x := (t, π)) _ _.
  Next Obligation.
    eapply _reduce_stack.
    - assumption.
    - intros t' π' h'.
      eapply f.
      + assumption.
      + simple inversion h'.
        * cbn in H1. cbn in H2.
          inversion H1. subst. inversion H2. subst. clear H1 H2.
          intros.
          destruct hΣ as [wΣ].
          eapply cored_wellformed ; eassumption.
        * cbn in H1. cbn in H2.
          inversion H1. subst. inversion H2. subst. clear H1 H2.
          intros. cbn. rewrite H3. assumption.
  Defined.
  Next Obligation.
    destruct hΣ.
    eapply R_Acc. all: assumption.
  Defined.
  (* Replace the last obligation by the following to run inside Coq. *)
  (* Next Obligation.
    destruct hΣ.
    revert h. generalize (t, π).
    refine (Acc_intro_generator
              (R:=fun x y => R Σ Γ x y)
              (P:=fun x => wellformed Σ Γ (zip x)) (fun x y Px Hy => _) 12 _).
    simpl in *. eapply wellformed_R_pres; eauto.
    intros; eapply R_Acc; eassumption.
  Defined. *)

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Lemma reduce_stack_Req :
    forall Γ t π h,
      Req Σ Γ (reduce_stack Γ t π h) (t, π).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]].
    assumption.
  Qed.

  Theorem reduce_stack_sound :
    forall Γ t π h,
      ∥ red (fst Σ) Γ (zip (t, π)) (zip (reduce_stack Γ t π h)) ∥.
  Proof.
    intros Γ t π h.
    eapply Req_red.
    eapply reduce_stack_Req.
  Qed.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p p']]].
    unfold Pr in p. symmetry. assumption.
  Qed.

  Lemma reduce_stack_context :
    forall Γ t π h,
      stack_context (snd (reduce_stack Γ t π h)) =
      stack_context π.
  Proof.
    intros Γ t π h.
    pose proof (reduce_stack_decompose Γ t π h) as hd.
    case_eq (decompose_stack π). intros l ρ e1.
    case_eq (decompose_stack (snd (reduce_stack Γ t π h))). intros l' ρ' e2.
    rewrite e1 in hd. rewrite e2 in hd. cbn in hd. subst.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2) as eq.
    rewrite eq. subst.
    rewrite 2!stack_context_appstack. reflexivity.
  Qed.

  Definition isred (t : term * stack) :=
    isApp (fst t) = false /\
    (isLambda (fst t) -> isStackApp (snd t) = false).

  Lemma reduce_stack_isred :
    forall Γ t π h,
      RedFlags.beta flags ->
      isred (reduce_stack Γ t π h).
  Proof.
    intros Γ t π h hr.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]].
    split.
    - assumption.
    - apply hLam. assumption.
  Qed.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]].
    assumption.
  Qed.

  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]].
    assumption.
  Qed.

  Definition reduce_term Γ t (h : wellformed Σ Γ t) :=
    zip (reduce_stack Γ t ε h).

  Theorem reduce_term_sound :
    forall Γ t h,
      ∥ red (fst Σ) Γ t (reduce_term Γ t h) ∥.
  Proof.
    intros Γ t h.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ ε _).
  Qed.

  (* Potentially hard? Ok with SN? *)
  Lemma Ind_canonicity :
    forall Γ ind uni args t,
      Σ ;;; Γ |- t : mkApps (tInd ind uni) args ->
      RedFlags.iota flags ->
      let '(u,l) := decompose_app t in
      (isLambda u -> l = []) ->
      whnf flags Σ Γ u ->
      discr_construct u ->
      whne flags Σ Γ u.
  Proof.
    intros Γ ind uni args t ht hiota.
    case_eq (decompose_app t).
    intros u l e hl h d.
    induction h.
    - assumption.
    - apply decompose_app_inv in e. subst.
      (* Inversion on ht *)
      admit.
    - apply decompose_app_inv in e. subst.
      (* Inversion on ht *)
      admit.
    - cbn in hl. specialize (hl eq_refl). subst.
      apply decompose_app_inv in e. subst. cbn in ht.
      (* Inversion on ht *)
      admit.
    - apply decompose_app_eq_mkApps in e. subst.
      cbn in d. simp discr_construct in d. easy.
    - apply decompose_app_inv in e. subst.
      (* Inversion on ht *)
      admit.
    - apply decompose_app_inv in e. subst.
      (* Not very clear now.
         Perhaps we ought to show whnf of the mkApps entirely.
         And have a special whne case for Fix that don't reduce?
       *)
  Abort.

  Scheme Acc_ind' := Induction for Acc Sort Prop.

  Lemma Fix_F_prop :
    forall A R P f (pred : forall x : A, P x -> Prop) x hx,
      (forall x aux, (forall y hy, pred y (aux y hy)) -> pred x (f x aux)) ->
      pred x (@Fix_F A R P f x hx).
  Proof.
    intros A R P f pred x hx h.
    induction hx using Acc_ind'.
    cbn. eapply h. assumption.
  Qed.

  Lemma reduce_stack_prop :
    forall Γ t π h (P : term × stack -> term × stack -> Prop),
      (forall t π h aux,
          (forall t' π' hR, P (t', π') (` (aux t' π' hR))) ->
          P (t, π) (` (_reduce_stack Γ t π h aux))) ->
      P (t, π) (reduce_stack Γ t π h).
  Proof.
    intros Γ t π h P hP.
    unfold reduce_stack.
    case_eq (reduce_stack_full Γ t π h).
    funelim (reduce_stack_full Γ t π h).
    intros [t' ρ] ? e.
    match type of e with
    | _ = ?u =>
      change (P (t, π) (` u))
    end.
    rewrite <- e.
    set ((reduce_stack_full_obligations_obligation_2 Γ t π h)).
    set ((reduce_stack_full_obligations_obligation_3 Γ t π h)).
    match goal with
    | |- P ?p (` (@Fix_F ?A ?R ?rt ?f ?t ?ht ?w)) =>
      set (Q := fun x (y : rt x) => forall (w : wellformed Σ Γ (zip x)), P x (` (y w))) ;
      set (fn := @Fix_F A R rt f t ht)
    end.
    clearbody w.
    revert w.
    change (Q (t, π) fn).
    subst fn.
    eapply Fix_F_prop.
    intros [? ?] aux H. subst Q. simpl. intros w.
    eapply hP. intros t'0 π' hR.
    eapply H.
  Qed.

  Lemma reduce_stack_whnf :
    forall Γ t π h,
      let '(u, ρ) := reduce_stack Γ t π h in
      whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ).
  Proof.
    intros Γ t π h.
    eapply reduce_stack_prop
      with (P := fun x y =>
        let '(u, ρ) := y in
        whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)
      ).
    clear.
    intros t π h aux haux.
    (* funelim (_reduce_stack Γ t π h aux).
    all: simpl.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - clear Heq.
      revert r.
      funelim (red_discr t1 π7). all: try easy. all: intros _.
      all: try solve [ constructor ; constructor ].
      all: try solve [
        unfold zipp ; case_eq (decompose_stack π) ; intros ;
        constructor ; eapply whne_mkApps ; constructor
      ].
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eapply whnf_sort.
        * exfalso.
          cbn in h. zip fold in h. apply welltyped_context in h.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as hh.
          destruct hh as [na [A [B [hs [? ?]]]]].
          (* We need proper inversion here *)
          admit.
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eapply whnf_prod.
        * exfalso.
          cbn in h. zip fold in h. apply welltyped_context in h.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as hh.
          destruct hh as [na' [A' [B' [hs [? ?]]]]].
          (* We need proper inversion here *)
          admit.
      + (* Here, we need to show some isred property stating that under iota,
           not CoFix can be returned against Case/Proj.
         *)
        admit.
    - unfold zipp. case_eq (decompose_stack π0). intros l ρ e.
      constructor. eapply whne_mkApps.
      eapply whne_rel_nozeta. assumption.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π0). intros.
      constructor. eapply whne_mkApps. econstructor.
      rewrite <- e. cbn.
      cbn in H. inversion H. reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π1). intros.
      constructor. eapply whne_mkApps. eapply whne_letin_nozeta. assumption.
    - unfold zipp. case_eq (decompose_stack π2). intros.
      constructor. eapply whne_mkApps. eapply whne_const_nodelta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - pose proof (eq_sym e) as e'.
      apply PCUICConfluence.lookup_env_cst_inv in e'.
      symmetry in e'. subst.
      unfold zipp. case_eq (decompose_stack π2). intros.
      constructor. eapply whne_mkApps. econstructor.
      + symmetry. exact e.
      + reflexivity.
    - bang.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - (* Missing normal form for nobeta *)
      give_up.
    - (* Missing normal form when no fix flag (neutral or normal?) *)
      give_up.
    - (* Should be impossible by typing and reduce_stack should account
         for it.
       *)
      give_up.
    - (* Impossible by typing?? *)
      give_up.
    - (* Missing neutral when fix is applied to a neutral term in guard
         position. *)
      give_up.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π5). intros.
      constructor. eapply whne_mkApps. eapply whne_case_noiota. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π5). intros.
      match type of e with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z) as haux'
      end.
      rewrite <- e in haux'. simpl in haux'.
      unfold zipp in haux'.
      rewrite <- e0 in haux'.
      destruct a as [? [a ?]]. unfold Pr in a. cbn in a.
      pose proof a as a'.
      rewrite <- e0 in a'. cbn in a'. subst.
      pose proof (eq_sym e0) as e1. apply decompose_stack_eq in e1.
      subst.
      rewrite stack_context_appstack in haux'. simpl in haux'.
      apply Req_red in r as hr.
      pose proof (red_welltyped _ hΣ h hr) as hh.
      cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
      zip fold in hh.
      apply welltyped_context in hh. simpl in hh.
      destruct hh as [T hh].
      apply inversion_Case in hh
        as [u [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
      constructor. eapply whne_mkApps. constructor.
      eapply whne_mkApps.
      (* Need storng inversion lemma *)
      admit.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang.
    - unfold zipp. case_eq (decompose_stack π6). intros.
      constructor. eapply whne_mkApps. eapply whne_proj_noiota. assumption.
    - (* Like case *)
      admit.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang. *)
  Abort.

  Lemma reduce_stack_whnf :
    forall Γ t π h,
      whnf flags Σ (Γ ,,, stack_context (snd (reduce_stack Γ t π h)))
           (fst (reduce_stack Γ t π h)).
  Proof.
    intros Γ t π h.
    eapply reduce_stack_prop
      with (P := fun x y => whnf flags Σ (Γ ,,, stack_context (snd y)) (fst y)).
    clear. intros t π h aux haux.
    (* )funelim (_reduce_stack Γ t π h aux).
    all: simpl.
    all: try solve [ constructor ; constructor ].
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - clear Heq.
      revert r.
      funelim (red_discr t1 π7). all: try easy. all: intros _.
      all: try solve [ constructor ; constructor ].
      + eapply whnf_indapp with (v := []).
      + eapply whnf_cstrapp with (v := []).
    - constructor. eapply whne_rel_nozeta. assumption.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - constructor. econstructor.
      rewrite <- e. cbn.
      cbn in H. inversion H. reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - constructor. eapply whne_letin_nozeta. assumption.
    - constructor. eapply whne_const_nodelta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - pose proof (eq_sym e) as e'.
      apply PCUICConfluence.lookup_env_cst_inv in e'.
      symmetry in e'. subst.
      constructor. econstructor.
      + symmetry. exact e.
      + reflexivity.
    - bang.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - constructor. eapply whne_case_noiota. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - constructor. constructor.
      eapply whne_mkApps.
      match type of e with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z) as haux'
      end.
      rewrite <- e in haux'. simpl in haux'.
      destruct a as [? [a ?]]. unfold Pr in a. cbn in a.
      pose proof a as a'.
      rewrite <- e0 in a'. cbn in a'. subst.
      pose proof (eq_sym e0) as e1. apply decompose_stack_eq in e1.
      subst.
      rewrite stack_context_appstack in haux'. simpl in haux'.
      apply Req_red in r as hr.
      pose proof (red_welltyped _ hΣ h hr) as hh.
      cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
      zip fold in hh.
      apply welltyped_context in hh. simpl in hh.
      destruct hh as [T hh].
      apply inversion_Case in hh
        as [u [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
      (* apply Ind_canonicity in ht0 ; auto. *)
      (* + rewrite decompose_app_mkApps in ht0 ; auto. *)
      (*   destruct p0 as [? ?]. assumption. *)
      (* + (* That is kinda stupid now... *)
      (*      Back to where we started. *)
      (*    *) *)

      (* We are almost there! *)
  (*        t0 is a normal form (haux') of inductive type (ht0), *)
  (*        plus it is not a constructor (d), *)
  (*        we want to conclude it is necessarily neutral *)
  (*      *)
      admit.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang.
    - constructor. eapply whne_proj_noiota. assumption.
    - (* Like case *)
      admit.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] [? [? [? ?]]] eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - bang. *)
  Abort.

End Reduce.
