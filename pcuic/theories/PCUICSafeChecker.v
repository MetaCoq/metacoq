(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia Classes.RelationClasses.
From Template
Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
From Equations Require Import Equations NoConfusion.

Import MonadNotation.

(** * Type checker for PCUIC without fuel

  *WIP*

  The idea is to subsume PCUICChecker by providing a fuel-free implementation
  of reduction, conversion and type checking.

  We will follow the same structure, except that we assume normalisation of
  the system. Since we will be using an axiom to justify termination, the checker
  won't run inside Coq, however, its extracted version should correspond more or less
  to the current implementation in ocaml, except it will be certified.

 *)

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

(* We assume normalisation of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Normalisation.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom Subterm for term.

  Inductive stack : Type :=
  | Empty
  | App (t : term) (e : stack)
  | Fix (f : mfixpoint term) (n : nat) (args : list term) (e : stack)
  | Case (indn : inductive * nat) (pred : term) (brs : list (nat * term)) (e : stack).

  Fixpoint zipc t stack :=
    match stack with
    | Empty => t
    | App u e => zipc (tApp t u) e
    | Fix f n args e => zipc (tApp (mkApps (tFix f n) args) t) e
    | Case indn pred brs e => zipc (tCase indn pred t brs) e
    end.

  Definition zip (t : term * stack) := zipc (fst t) (snd t).

  (* TODO Tail-rec version *)
  (* Get the arguments out of a stack *)
  Fixpoint decompose_stack π :=
    match π with
    | App u π => let '(l,π) := decompose_stack π in (u :: l, π)
    | _ => ([], π)
    end.

  (* TODO Tail-rec *)
  Fixpoint appstack l π :=
    match l with
    | u :: l => App u (appstack l π)
    | [] => π
    end.

  Lemma decompose_stack_eq :
    forall π l ρ,
      decompose_stack π = (l, ρ) ->
      π = appstack l ρ.
  Proof.
    intros π l ρ eq.
    revert l ρ eq. induction π ; intros l ρ eq.
    - cbn in eq. inversion eq. subst. reflexivity.
    - destruct l.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros. inversion eq.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros l0 s H0 eq. inversion eq. subst.
        cbn. f_equal. eapply IHπ. assumption.
    - cbn in eq. inversion eq. subst. reflexivity.
    - cbn in eq. inversion eq. subst. reflexivity.
  Qed.

  Lemma decompose_stack_not_app :
    forall π l u ρ,
      decompose_stack π = (l, App u ρ) -> False.
  Proof.
    intros π l u ρ eq.
    revert u l ρ eq. induction π ; intros u l ρ eq.
    all: try solve [ cbn in eq ; inversion eq ].
    cbn in eq. revert eq. case_eq (decompose_stack π).
    intros l0 s H0 eq. inversion eq. subst.
    eapply IHπ. eassumption.
  Qed.

  Lemma zipc_appstack :
    forall {t args ρ},
      zipc t (appstack args ρ) = zipc (mkApps t args) ρ.
  Proof.
    intros t args ρ. revert t ρ. induction args ; intros t ρ.
    - cbn. reflexivity.
    - cbn. rewrite IHargs. reflexivity.
  Qed.

  Fixpoint decompose_stack_at π n : option (list term * term * stack) :=
    match π with
    | App u π =>
      match n with
      | 0 => ret ([], u, π)
      | S n =>
        r <- decompose_stack_at π n ;;
        let '(l, v, π) := r in
        ret (u :: l, v, π)
      end
    | _ => None
    end.

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Definition R Σ Γ u v :=
    Subterm.lexprod _ _ (cored Σ Γ) term_subterm (zip u, fst u) (zip v, fst v).

  Axiom normalisation :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      Acc (cored (fst Σ) Γ) t.

  Corollary R_Acc_aux :
    forall Σ Γ t A,
      Σ ;;; Γ |- zip t : A ->
      Acc (Subterm.lexprod _ _ (cored (fst Σ) Γ) term_subterm) (zip t, fst t).
  Proof.
    intros Σ Γ t A h.
    eapply Subterm.acc_A_B_lexprod.
    - eapply normalisation. eassumption.
    - eapply well_founded_term_subterm.
    - eapply well_founded_term_subterm.
  Qed.

  Derive Signature for Acc.

  Corollary R_Acc :
    forall Σ Γ t A,
      Σ ;;; Γ |- zip t : A ->
      Acc (R (fst Σ) Γ) t.
  Proof.
    intros Σ Γ t A h.
    pose proof (R_Acc_aux _ _ _ _ h) as h'.
    clear A h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H1 ; try reflexivity.
    unfold R in hy. assumption.
  Qed.

  (* Req doesn't have to be this.
     It only needs to be reflexive and have the following property:
     Req u v -> R v w -> Req u w
     So it remains unclear if it can be anything else interesting than
     the current definition, but it opens the possibility.
     The hope would be that it is easier to reason on.
     By concluding on the first component perhaps for reduction.
   *)
  Definition Req Σ Γ t t' :=
    t = t' \/ R Σ Γ t t'.

  Derive Signature for Subterm.lexprod.

  Lemma cored_trans' :
    forall {Σ Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Definition transitive {A} (R : A -> A -> Prop) :=
    forall u v w, R u v -> R v w -> R u w.

  Lemma lexprod_trans :
    forall A B RA RB,
      transitive RA ->
      transitive RB ->
      transitive (Subterm.lexprod A B RA RB).
  Proof.
    intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
    revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
    - dependent induction h2.
      + eapply Subterm.left_lex. eapply hA ; eassumption.
      + eapply Subterm.left_lex. assumption.
    - dependent induction h2.
      + eapply Subterm.left_lex. assumption.
      + eapply Subterm.right_lex. eapply hB ; eassumption.
  Qed.

  Lemma Rtrans :
    forall Σ Γ u v w,
      R Σ Γ u v ->
      R Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    eapply lexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - intros ? ? ? ? ?. eapply Relation_Operators.t_trans ; eassumption.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Σ Γ}, transitive (Req Σ Γ).
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Σ Γ u v},
      R Σ Γ u v ->
      Req Σ Γ u v.
  Proof.
    intros Σ Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Σ Γ, Reflexive (Req Σ Γ).
  Proof.
    intros Σ Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Σ Γ u v w},
      R Σ Γ u v ->
      Req Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  Lemma red1_context :
    forall Σ Γ t u stack,
      red1 Σ Γ t u ->
      red1 Σ Γ (zip (t, stack)) (zip (u, stack)).
  Admitted.

  Corollary red_context :
    forall Σ Γ t u stack,
      red Σ Γ t u ->
      red Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Corollary cored_context :
    forall Σ Γ t u stack,
      cored Σ Γ t u ->
      cored Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Σ Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Σ' Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma case_reds_discr :
    forall Σ Γ ind p c c' brs,
      red Σ Γ c c' ->
      red Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor.
    - econstructor.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Existing Instance Req_refl.

  Lemma cored_case :
    forall Σ Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  (* Lemma R_case : *)
  (*   forall Σ Γ ind p c c' brs π, *)
  (*     R Σ Γ c c' -> *)
  (*     Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p (zipapp c') brs, π). *)
  (* Proof. *)
  (*   intros Σ' Γ ind p [c e] [c' e'] brs π h. *)
  (*   dependent destruction h. *)
  (*   - right. econstructor. eapply cored_context. eapply cored_case. *)
  (*     assumption. *)
  (*   - cbn in H1. inversion H1. subst. clear H1. *)
  (*     cbn in H0. cbn. rewrite H3. reflexivity. *)
  (* Qed. *)

  (* Lemma Req_case : *)
  (*   forall Σ Γ ind p c c' brs π, *)
  (*     Req Σ Γ c c' -> *)
  (*     Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p (zipapp c') brs, π). *)
  (* Proof. *)
  (*   intros Σ' Γ ind p [c e] [c' e'] brs π h. *)
  (*   dependent destruction h. *)
  (*   - rewrite H0. reflexivity. *)
  (*   - eapply R_case. assumption. *)
  (* Qed. *)

 (*  Lemma R_case : *)
 (*    forall Σ Γ ind p c c' brs π, *)
 (*      R Σ Γ c (c', Case ind p brs π) -> *)
 (*      Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p c' brs, π). *)
 (*  Proof. *)
 (*    intros Σ' Γ ind p [c e] c' brs π h. *)
 (*    dependent destruction h. *)
 (*    - cbn in H0. cbn. eapply Req_trans. *)
 (*      2:{ right. econstructor. *)
 (*          instantiate (1 := (c,e)). cbn. *)
 (*          exact H0. *)
 (*      } *)


 (*      right. econstructor. eapply cored_context. eapply cored_case. *)
 (*      assumption. *)
 (*    - cbn in H1. inversion H1. subst. clear H1. *)
 (*      cbn in H0. cbn. rewrite H3. reflexivity. *)
 (*  Qed. *)

 (*  Lemma Req_case : *)
 (*    forall Σ Γ ind p c c' brs π, *)
 (*      Req Σ Γ c (c', Case ind p brs π) -> *)
 (*      Req Σ Γ (tCase ind p (zipapp c) brs, π) (tCase ind p c' brs, π). *)
 (*  Proof. *)
 (*    intros Σ' Γ ind p [c e] c' brs π h. *)
 (*    dependent destruction h. *)
 (*    - rewrite H0. reflexivity. *)
 (*    - eapply R_case. assumption. *)
 (*  Qed. *)

 (* prf : Req (fst Σ) Γ (tConstruct ind' c' wildcard, args) (c, Case (ind, par) p brs π) *)
 (*  ============================ *)
 (*  Req (fst Σ) Γ (tCase (?Goal1, par) ?Goal0 (mkApps (tConstruct ?Goal1 c' ?u) (stack_args args)) brs, π) *)
 (*    (tCase (ind, par) p c brs, π) *)

  Lemma closedn_context :
    forall n t,
      closedn n (zip t) = true ->
      closedn n (fst t).
  Admitted.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist _ res prf) := reduce t π smaller in
     exist _ res (Req_trans _ _ _ _ (R_to_Req smaller))
    ).

  (* Notation repack t := (let '(exist _ res prf) := t in (exist _ res _)). *)

  (* Set Equations Debug. *)

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : closedn #|Γ| (zip (t,π)) = true)
            (reduce : forall t' π', R (fst Σ) Γ (t',π') (t,π) -> { t'' : term * stack | Req (fst Σ) Γ t'' (t',π')})
    : { t' : term * stack | Req (fst Σ) Γ t' (t,π) } :=

    _reduce_stack Γ (tRel c) π h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error Γ c) := {
      (* | @exist None eq := ! ; *)
      | @exist None eq := _ ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := exist _ (tRel c, π) _ ;
        | @exist (Some b) H := rec reduce (lift0 (S c) b) π
        }
      } ;
    | false := exist _ (tRel c, π) _
    } ;

    _reduce_stack Γ (tLetIn A b B c) π h reduce with RedFlags.zeta flags := {
    | true := rec reduce (subst10 b c) π ;
    | false := exist _ (tLetIn A b B c, π) _
    } ;

    _reduce_stack Γ (tConst c u) π h reduce with RedFlags.delta flags := {
    | true with inspect (lookup_env (fst Σ) c) := {
      | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
        let body' := subst_instance_constr u body in
        rec reduce body' π ;
      | @exist _ eq := exist _ (tConst c u, π) _
      } ;
    | _ := exist _ (tConst c u, π) _
    } ;

    _reduce_stack Γ (tApp f a) π h reduce :=
      rec reduce f (App a π) ;

    _reduce_stack Γ (tLambda na A t) (App a args) h reduce with RedFlags.beta flags := {
    | true := rec reduce (subst10 a t) args ;
    | false := exist _ (tLambda na A t, App a args) _
    } ;

    (* _reduce_stack Γ (tFix mfix idx) π h reduce with RedFlags.fix_ flags := { *)
    (* | true with inspect (unfold_fix mfix idx) := { *)
    (*   | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := { *)
    (*     | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix mfix idx args ρ)) := { *)
    (*       | @exist (@exist (tConstruct ind n ui, ρ') prf) eq3 := rec reduce fn π ; *)
    (*       | _ := exist _ (tFix mfix idx, π) _ *)
    (*       } ; *)
    (*     | _ := exist _ (tFix mfix idx, π) _ *)
    (*     } ; *)
    (*   | _ := exist _ (tFix mfix idx, π) _ *)
    (*   } ; *)
    (* | false := exist _ (tFix mfix idx, π) _ *)
    (* } ; *)

    (* Nothing special seems to be done for Π-types. *)
    (* _reduce_stack Γ (tProd na A B) *)

    _reduce_stack Γ (tCase (ind, par) p c brs) π h reduce with RedFlags.iota flags := {
    | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
      | @exist (@exist (tConstruct ind' c' _, π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' := rec reduce (iota_red par c' args brs) π
        } ;
      | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' := exist _ (tCase (ind, par) p (mkApps t args) brs, π) _
        }
      } ;
    | false := exist _ (tCase (ind, par) p c brs, π) _
    } ;

    _reduce_stack Γ t π h reduce := exist _ (t, π) _.
  Solve All Obligations with (program_simpl ; reflexivity).
  Next Obligation.
    econstructor.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    pose proof (closedn_context _ _ h) as hc. simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc. revert c hc eq.
    induction Γ ; intros c hc eq.
    - cbn in hc. discriminate.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption. apply hc.
  Qed.
  Next Obligation.
    econstructor. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    econstructor. econstructor.
    eapply red1_context.
    econstructor.
  Qed.
  Next Obligation.
    eapply Subterm.right_lex. cbn. constructor. constructor.
  Qed.
  Next Obligation.
    econstructor. econstructor. eapply red1_context.
    econstructor.
    (* Should be a lemma! *)
    - unfold declared_constant. rewrite <- eq. f_equal.
      f_equal. clear - eq.
      revert c wildcard wildcard0 body wildcard1 eq.
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
    eapply Subterm.right_lex. cbn. constructor. constructor.
  Qed.
  Next Obligation.
    clear - prf prf'. subst t. destruct prf.
    - inversion H. subst. clear H.
      cbn in prf'. inversion prf'. subst. clear prf'.
      reflexivity.
    - dependent destruction H.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf') as eq.
        subst.
        rewrite zipc_appstack in H1.
        right. econstructor. cbn.
        (* It seems we lost too much information by saying the whole case
           reduces.
           We would like to know that c itself reduced to a constructor!
           Actually, it might be that the definition itself is wrong!
           Or we need a property that (t,Case) reduces to (t',Case), never going
           under the Case.
         *)
        (* destruct ρ. *)
        (* * cbn in H1. *)
        admit.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf') as eq.
        subst.
        cbn in H5.
        rewrite zipc_appstack in H5.
        right. unfold R. cbn. rewrite H5.
        (* eapply Subterm.right_lex. *)
        (* Once again, not very clear... *)
        admit.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    eapply R_Req_R.
    - econstructor. econstructor. eapply red1_context.
      eapply red_iota.
    - (* Fail eapply Req_case. *)


    (* econstructor. eapply cored_red_trans. *)
    (* - eapply red_context. eapply case_reds_discr. *)
    (*   instantiate (1 := zip (tConstruct ind' c' wildcard, args)). *)
    (*   (* This involves soundness of reduction. *) *)
    (*   (* With the Case stack, this becomes a bit tricky... *)
    (*      It seems zip is not what we want... *)
    (*    *) *)
    (*   admit. *)
    (* - eapply red1_context. cbn. *)
    (*   Fail eapply red_iota. *)
    (*   (* This is not clear how to apply the rule. *)
    (*      We indeed need ind = ind' which cannot be deduced from the context. *)
    (*      This is actually enforced by typing, which we do not have at the *)
    (*      moment. *)
    (*    *) *)
      admit.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  (* Next Obligation. *)
  (*   (* Problem. Once again the order is too restrictive. *)
  (*      We also need to allow reduction on the stack it seems. *)
  (*    *) *)
  (*   admit. *)
  (* Admitted. *)
  (* Solve All Obligations with (program_simpl ; reflexivity). *)
  (* Next Obligation. *)
  (*   econstructor. econstructor. cbn. *)
  (*   (* Also worse now. We used to have mkApps. No longer. *)
  (*      Perhaps is it that we should match on the stack in those cases *)
  (*      as well. *)
  (*    *) *)
  (*   (* econstructor. *) *)
  (*   (* - rewrite <- eq1. reflexivity. *) *)
  (*   (* - unfold is_constructor. rewrite <- eq2. *) *)
  (*   (*   (* Problem of a more dangerouns kind. *) *)
  (*   (*      To show termination we already need soundness. *) *)
  (*   (*      Or we need to fix the red_fix rule. *) *)
  (*   (*      Indeed, it is broken because it wants stack(narg) to be already *) *)
  (*   (*      a constructor, which doesn't even allow reduction. *) *)
  (*   (*    *) *) *)
  (*   (*   unfold decompose_app. *) *)
  (* Admitted. *)

  Lemma closedn_cored :
    forall Σ Γ u v,
      cored Σ Γ v u ->
      closedn #|Γ| u = true ->
      closedn #|Γ| v = true.
  Admitted.

  Lemma closedn_typed :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      closedn #|Γ| t = true.
  Admitted.

  Equations reduce_stack (Γ : context) (t A : term) (π : stack)
           (h : Σ ;;; Γ |- zip (t,π) : A) : term * stack :=
    reduce_stack Γ t A π h :=
      let '(exist _ ts _) :=
          Fix_F (R := R (fst Σ) Γ)
                (fun x => closedn #|Γ| (zip x) = true -> { t' : term * stack | Req (fst Σ) Γ t' x })
                (fun t' f => _) (x := (t, π)) _ _
      in ts.
  Next Obligation.
    intro hc.
    eapply _reduce_stack.
    - assumption.
    - intros t' π' h'.
      eapply f.
      + assumption.
      + simple inversion h'.
        * inversion H1. inversion H2. subst. clear H1 H2.
          intros H0.
          eapply closedn_cored ; eassumption.
        * inversion H1. inversion H2. subst. clear H1 H2.
          intros H0. rewrite H5. assumption.
  Qed.
  Next Obligation.
    eapply R_Acc. eassumption.
  Qed.
  Next Obligation.
    eapply closedn_typed. eassumption.
  Qed.

End Reduce.