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
   This seems to be slightly stronger than simply assuming there are no infinite paths.
   This is however the version we need to do well-founded recursion.
*)
Section Normalisation.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom Subterm for term.

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

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

  Lemma closedn_context :
    forall n t,
      closedn n (zip t) = true ->
      closedn n (fst t).
  Admitted.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

  Equations _reduce_stack (Γ : context) (t : term) (stack : list term)
            (h : closedn #|Γ| (zip (t,stack)) = true)
            (reduce : forall t' stack', R (fst Σ) Γ (t',stack') (t,stack) -> term * list term)
    : term * list term :=

    _reduce_stack Γ (tRel c) stack h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error Γ c) := {
      | @exist None eq := ! ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := (tRel c, stack) ;
        | @exist (Some b) H := reduce (lift0 (S c) b) stack _
        }
      } ;
    | false := (tRel c, stack)
    } ;

    _reduce_stack Γ (tLetIn A b B c) stack h reduce with RedFlags.zeta flags := {
    | true := reduce (subst10 b c) stack _ ;
    | false := (tLetIn A b B c, stack)
    } ;

    _reduce_stack Γ (tConst c u) stack h reduce with RedFlags.delta flags := {
    | true with inspect (lookup_env (fst Σ) c) := {
      | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
        let body' := subst_instance_constr u body in
        reduce body' stack _ ;
      | @exist _ eq := (tConst c u, stack)
      } ;
    | _ := (tConst c u, stack)
    } ;

    _reduce_stack Γ (tApp f a) stack h reduce :=
      reduce f (a :: stack) _ ;

    _reduce_stack Γ t stack h reduce := (t, stack).
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

  Lemma closedn_red :
    forall Σ Γ u v,
      red Σ Γ u v ->
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
          + (* eapply closedn_red ; try eassumption. *)
            admit.
      }
    - { eapply R_Acc. eassumption. }
    - { eapply closedn_typed. eassumption. }
  (* Qed. *)
  Admitted.

End Reduce.