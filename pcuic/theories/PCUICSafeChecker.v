(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
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
  | Fix (f : mfixpoint term) (n : nat) (e : stack)
  | Case (indn : inductive * nat) (pred : term) (brs : list (nat * term)) (e : stack).

  Fixpoint zipc t stack :=
    match stack with
    | Empty => t
    | App u e => zipc (tApp t u) e
    | Fix f n e => zipc (tFix f n) e
    | Case indn pred brs e => zipc (tCase indn pred t brs) e
    end.

  Definition zip (t : term * stack) := zipc (fst t) (snd t).

  Fixpoint stack_args (π : stack) : list term :=
    match π with
    | App u π => u :: (stack_args π)
    | _ => []
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

  Lemma closedn_context :
    forall n t,
      closedn n (zip t) = true ->
      closedn n (fst t).
  Admitted.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : closedn #|Γ| (zip (t,π)) = true)
            (reduce : forall t' π', R (fst Σ) Γ (t',π') (t,π) -> term * stack)
    : term * stack :=

    _reduce_stack Γ (tRel c) π h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error Γ c) := {
      | @exist None eq := ! ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := (tRel c, π) ;
        | @exist (Some b) H := reduce (lift0 (S c) b) π _
        }
      } ;
    | false := (tRel c, π)
    } ;

    _reduce_stack Γ (tLetIn A b B c) π h reduce with RedFlags.zeta flags := {
    | true := reduce (subst10 b c) π _ ;
    | false := (tLetIn A b B c, π)
    } ;

    _reduce_stack Γ (tConst c u) π h reduce with RedFlags.delta flags := {
    | true with inspect (lookup_env (fst Σ) c) := {
      | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
        let body' := subst_instance_constr u body in
        reduce body' π _ ;
      | @exist _ eq := (tConst c u, π)
      } ;
    | _ := (tConst c u, π)
    } ;

    _reduce_stack Γ (tApp f a) π h reduce :=
      reduce f (App a π) _ ;

    _reduce_stack Γ (tLambda na A t) (App a args) h reduce with RedFlags.beta flags := {
    | true := reduce (subst10 a t) args _ ;
    | false := (tLambda na A t, App a args)
    } ;

    _reduce_stack Γ (tFix mfix idx) π h reduce with RedFlags.fix_ flags := {
    | true with inspect (unfold_fix mfix idx) := {
      | @exist (Some (narg, fn)) eq1 with inspect (nth_error (stack_args π) narg) := {
        | @exist (Some c) eq2 with inspect (fst (reduce c (Fix mfix idx π) _)) := {
          | @exist (tConstruct _ _ _) eq3 := reduce fn π _ ;
          | _ := (tFix mfix idx, π)
          } ;
        | _ := (tFix mfix idx, π)
        } ;
      | _ := (tFix mfix idx, π)
      } ;
    | false := (tFix mfix idx, π)
    } ;

    (* Nothing special seems to be done for Π-types. *)
    (* _reduce_stack Γ (tProd na A B) *)

    _reduce_stack Γ (tCase (ind, par) p c brs) π h reduce with RedFlags.iota flags := {
    | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
      | @exist (tConstruct ind' c' _, args) eq := reduce (iota_red par c' (stack_args args) brs) π _ ;
      | @exist c' eq := (tCase (ind, par) p (zip c') brs, π)
      } ;
    | false := (tCase (ind, par) p c brs, π)
    } ;

    _reduce_stack Γ t π h reduce := (t, π).
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
    econstructor. eapply cored_red_trans.
    - eapply red_context. eapply case_reds_discr.
      instantiate (1 := zip (tConstruct ind' c' wildcard, args)).
      (* This involves soundness of reduction. *)
      (* With the Case stack, this becomes a bit tricky...
         It seems zip is not what we want...
       *)
      admit.
    - eapply red1_context. cbn.
      Fail eapply red_iota.
      (* This is not clear how to apply the rule.
         We indeed need ind = ind' which cannot be deduced from the context.
         This is actually enforced by typing, which we do not have at the
         moment.
       *)
      (* Worst now with the new stacks... *)
      admit.
  Admitted.
  Next Obligation.
    (* Problem. Once again the order is too restrictive.
       We also need to allow reduction on the stack it seems.
     *)
    admit.
  Admitted.
  Next Obligation.
    econstructor. econstructor. cbn.
    econstructor.
    - rewrite <- eq1. reflexivity.
    - unfold is_constructor. rewrite <- eq2.
      (* Problem of a more dangerouns kind.
         To show termination we already need soundness.
         Or we need to fix the red_fix rule.
         Indeed, it is broken because it wants stack(narg) to be already
         a constructor, which doesn't even allow reduction.
       *)
      unfold decompose_app.
  Admitted.

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

  Equations? reduce_stack (Γ : context) (t A : term) (stack : list term)
           (h : Σ ;;; Γ |- zip (t,stack) : A) : term * list term :=
    reduce_stack Γ t A stack h :=
      Fix_F (R := R (fst Σ) Γ)
            (fun x => closedn #|Γ| (zip x) = true -> (term * list term)%type)
            (fun t' f => _) (x := (t, stack)) _ _.
  Proof.
    - { eapply _reduce_stack.
        - eassumption.
        - intros. eapply f.
          + eassumption.
          + simple inversion H1.
            * inversion H3. inversion H4. subst.
              intro hr.
              eapply closedn_cored ; eassumption.
            * inversion H3. inversion H4. subst.
              intro hs. rewrite H7. assumption.
      }
    - { eapply R_Acc. eassumption. }
    - { eapply closedn_typed. eassumption. }
  Qed.

End Reduce.