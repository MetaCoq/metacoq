(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config monad_utils utils BasicAst univ.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICChecker.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MonadNotation.

Existing Instance default_checker_flags.

(** * Retyping

  The [type_of] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Section TypeOf.
  Context `{F : Fuel}.
  Context (Σ : global_context).

  Section SortOf.
    Context (type_of : context -> term -> typing_result term).

    Definition type_of_as_sort Γ t :=
      tx <- type_of Γ t ;;
      reduce_to_sort (fst Σ) Γ tx.

  End SortOf.

  Fixpoint type_of (Γ : context) (t : term) : typing_result term :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some d => ret (lift0 (S n) d.(decl_type))
      | None => raise (UnboundRel n)
      end

    | tVar n => raise (UnboundVar n)
    | tMeta n => raise (UnboundMeta n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort s => ret (tSort (try_suc s))

    | tProd n t b =>
      s1 <- type_of_as_sort type_of Γ t ;;
      s2 <- type_of_as_sort type_of (Γ ,, vass n t) b ;;
      ret (tSort (Universe.sort_of_product s1 s2))

    | tLambda n t b =>
      t2 <- type_of (Γ ,, vass n t) b ;;
       ret (tProd n t t2)

    | tLetIn n b b_ty b' =>
      b'_ty <- type_of (Γ ,, vdef n b b_ty) b' ;;
      ret (tLetIn n b b_ty b'_ty)

    | tApp t a =>
      ty <- type_of Γ t ;;
      pi <- reduce_to_prod (fst Σ) Γ ty ;;
      let '(a1, b1) := pi in
      ret (subst10 a b1)

    | tConst cst u => lookup_constant_type Σ cst u

    | tInd (mkInd ind i) u => lookup_ind_type Σ ind i u

    | tConstruct (mkInd ind i) k u =>
      lookup_constructor_type Σ ind i k u

    | tCase (ind, par) p c brs =>
      ty <- type_of Γ c ;;
      indargs <- reduce_to_ind (fst Σ) Γ ty ;;
      let '(ind', u, args) := indargs in
      ret (mkApps p (List.skipn par args ++ [c]))

    | tProj p c =>
      ty <- type_of Γ c ;;
      indargs <- reduce_to_ind (fst Σ) Γ ty ;;
      (* FIXME *)
      ret ty

    | tFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end
    end.

  Definition sort_of (Γ : context) (t : term) : typing_result universe :=
    ty <- type_of Γ t;;
    type_of_as_sort type_of Γ ty.

  Open Scope type_scope.

  Conjecture cumul_reduce_to_sort : forall Γ t s',
      Σ ;;; Γ |- t <= tSort s' ->
      { s'' & (reduce_to_sort (fst Σ) Γ t = Checked s'')
            * (check_leq (snd Σ) s'' s' = true) }.

  Ltac one_ih :=
    let T := fresh "T" in
    let e := fresh "e" in
    let hT := fresh "hT" in
    let hc := fresh "hc" in
    match goal with
    | H : { _ : term &  _ } |- _ => destruct H as [T [[e hT] hc]]
    end.

  Ltac ih :=
    repeat one_ih.

  Ltac rewrite_eq :=
    match goal with
    | e : _ = _ |- _ => rewrite e
    end.

  Ltac rewrite_eqs :=
    repeat rewrite_eq.

  Ltac makedo :=
    simpl ;
    ih ;
    rewrite_eqs ;
    simpl ;
    eexists ; split ; [
      split ; [
        reflexivity
      | try (solve [ econstructor ; eassumption ])
      ]
    | try (solve [ eapply cumul_refl' ])
    ].

  Theorem type_of_sound :
    forall {Γ t A},
      Σ ;;; Γ |- t : A ->
      { B : term & (type_of Γ t = Checked B)
                 * (Σ ;;; Γ |- t : B)
                 * (cumul Σ Γ B A) }.
  Proof.
    intros Γ t A h.
    induction h.
    - makedo.
    - makedo.
      + admit.
      + admit.
    - (* makedo. *)
      destruct IHh1 as [T1 [[e1 hT1] hc1]].
      destruct IHh2 as [T2 [[e2 hT2] hc2]].
      simpl. unfold type_of_as_sort. rewrite e1. rewrite e2. simpl.
      apply cumul_reduce_to_sort in hc1 as hs1.
      apply cumul_reduce_to_sort in hc2 as hs2.
      destruct hs1 as [z1 [ez1 c1]].
      destruct hs2 as [z2 [ez2 c2]].
      rewrite ez1, ez2.
      eexists. split ; [split |].
      + reflexivity.
      + econstructor.
        * econstructor ; try eassumption.
          -- admit.
          -- admit.
        * econstructor ; try eassumption.
          all: admit.
      + admit.
    - makedo.
      eapply congr_cumul_prod.
      + eapply cumul_refl'.
      + assumption.
    - makedo. admit.
    - (* makedo. *) admit.
    - (* makedo. *) admit.
    - (* makedo. *) admit.
    - (* makedo. *) admit.
    - (* makedo. *) admit.
    - (* makedo. *) admit.
    - makedo.
    - makedo.
    - makedo.
      + assumption.
      + eapply cumul_trans ; eassumption.
  Admitted.



End TypeOf.