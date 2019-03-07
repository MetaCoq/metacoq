(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template
Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
From Equations Require Import Equations.

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

  (* Inductive R Σ Γ : (term * list term) -> (term * list term) -> Prop := *)
  (* | R_red : forall u v, cored Σ Γ (zip u) (zip v) -> R Σ Γ u v *)
  (* | R_subterm : forall u v π, term_subterm u v -> R Σ Γ (u,π) (v,π). *)

  Axiom normalisation :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      Acc (cored (fst Σ) Γ) t.

  Derive Signature for Acc.

  (* Lemma R_Acc_from_lexprod : *)
  (*   forall Σ Γ t, *)
  (*     Acc (Subterm.lexprod _ _ (cored Σ Γ) term_subterm) (zip t, fst t) -> *)
  (*     Acc (R Σ Γ) t. *)
  (* Proof. *)
  (*   intros Σ Γ t h. *)
  (*   dependent induction h. *)
  (*   constructor. intros y hy. *)
  (*   simple inversion hy. *)
  (*   - subst. intro hr. eapply H1. *)
  (*     + eapply Subterm.left_lex. eassumption. *)
  (*     + reflexivity. *)
  (*   - subst. intro hs. eapply H1 ; try reflexivity. *)
  (*     eapply Subterm.right_lex. *)

  (*     + eapply Subterm.right_lex. eassumption. *)
  (*     + cbn. *)


  (*   simple inversion h. *)
  (*   intros h1. constructor. *)
  (*   intros y hy. *)


  (* Corollary R_Acc_aux : *)
  (*   forall Σ Γ t, *)
  (*     Acc (cored Σ Γ) (zip t) -> *)
  (*     Acc (R Σ Γ) t. *)
  (* Proof. *)
  (*   intros Σ Γ t h. *)
  (*   dependent induction h. *)
  (*   constructor. intros y h. *)
  (*   simple inversion h. *)
  (*   - subst. intro hr. eapply H1. *)
  (*     + eassumption. *)
  (*     + reflexivity. *)
  (*   - subst. intro hs. eapply H1. *)



  (* Corollary R_Acc_aux : *)
  (*   forall Σ Γ t, *)
  (*     Acc (cored Σ Γ) (zip t) -> *)
  (*     Acc term_subterm (fst t) -> *)
  (*     Acc (R Σ Γ) t. *)
  (* Proof. *)
  (*   intros Σ Γ t h1. *)
  (*   dependent induction h1. *)
  (*   intro h2. dependent induction h2. *)
  (*   apply Acc_intro. intros y h. *)
  (*   simple inversion h. *)
  (*   - subst. intro hr. *)
  (*     eapply H3. *)
  (*     + eassumption. *)
  (*     + reflexivity. *)
  (*     + eapply well_founded_term_subterm. *)
  (*   - subst. intro hs. *)
  (*     eapply H1. *)
  (*     + eassumption. *)
  (*     + cbn. intros y H4. *)




  (*   dependent induction 1 *)
  (*   induction 1 as [y h2 ih2]. *)
  (*   apply Acc_intro. intros z h3. *)
  (*   simple inversion h3. *)
  (*   - subst. intro h4. *)
  (*     eapply ih1. *)
  (*     all: try eassumption. *)


  (*   destruct h3. *)
  (*   - simple inversion h1. *)





  (* Corollary R_Acc : *)
  (*   forall Σ Γ t A, *)
  (*     Σ ;;; Γ |- zip t : A -> *)
  (*     Acc (R (fst Σ) Γ) t. *)
  (* Proof. *)
  (*   intros Σ Γ t A h. *)
  (*   pose proof (normalisation _ _ _ _ h) as h1. *)
  (*   pose proof (well_founded_term_subterm) as h2. *)
  (*   unfold WellFounded in h2. unfold well_founded in h2. *)
  (*   specialize (h2 (fst t)). *)
  (*   clear A h. revert h2. induction h1. *)
  (*   intros h2. induction h2. *)
  (*   apply Acc_intro. *)
  (*   intros y hy. destruct hy. *)
  (*   - eapply H1. *)
  (*     + *)


End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.
  Require Import Equations.NoConfusion.

  Equations _reduce_stack (Γ : context) (t : term) (stack : list term)
            (h : closedn #|Γ| t = true)
            (* (reduce : forall Γ t' (stack : list term) (h : closedn #|Γ| t' = true), red (fst Σ) Γ t t' -> term * list term) *)
            (reduce : forall t' (stack : list term), red (fst Σ) Γ t t' -> term * list term)
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

    (* _reduce_stack Γ (tApp f a) stack h reduce := *)
    (*   reduce f (a :: stack) _ ; *)

    _reduce_stack Γ t stack h reduce := (t, stack).
  Next Obligation.
    econstructor.
    - econstructor.
    - eapply red_rel. rewrite <- eq. cbn. f_equal.
      symmetry. assumption.
  Qed.
  Next Obligation.
    (* Should be a lemma! *)
    clear - eq h. revert c h eq.
    induction Γ ; intros c h eq.
    - cbn in h. discriminate.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption. apply h.
  Qed.
  Next Obligation.
    econstructor.
    - econstructor.
    - econstructor.
  Qed.
  (* Next Obligation. *)
  (*   econstructor. *)
  (*   - econstructor. *)
  (*   - *)
  Next Obligation.
    econstructor.
    - econstructor.
    - econstructor.
      (* Should be a lemma! *)
      + unfold declared_constant. rewrite <- eq. f_equal.
        f_equal. clear - eq.
        revert c wildcard wildcard0 body wildcard1 eq.
        set (Σ' := fst Σ). clearbody Σ'. clear Σ. rename Σ' into Σ.
        induction Σ ; intros c na t body univ eq.
        * cbn in eq. discriminate.
        * cbn in eq. revert eq.
          case_eq (ident_eq c (global_decl_ident a)).
          -- intros e eq. inversion eq. subst. clear eq.
             cbn in e. revert e. destruct (ident_eq_spec c na) ; easy.
          -- intros e eq. eapply IHg. eassumption.
      + cbn. reflexivity.
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
           (h : Σ ;;; Γ |- t : A) : term * list term :=
    reduce_stack Γ t A stack h :=
      Fix_F (R := cored (fst Σ) Γ)
            (fun x => closedn #|Γ| x = true -> (term * list term)%type)
            (fun t' f => _) (x := t) _ _.
  Proof.
    - { eapply _reduce_stack.
        - exact stack.
        - eassumption.
        - intros. eapply f.
          + eassumption.
          + eapply closedn_red ; eassumption.
      }
    - { eapply normalisation. eassumption. }
    - { eapply closedn_typed. eassumption. }
  Qed.

End Reduce.