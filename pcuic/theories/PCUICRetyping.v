(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICChecker PCUICConversion PCUICCumulativity.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MonadNotation.

(** * Retyping

  The [type_of] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Axiom reduce_to_sort :
  global_env -> context -> term -> typing_result universe.
Axiom reduce_to_prod :
  global_env -> context -> term -> typing_result (term × term).

Axiom reduce_to_ind :
  global_env -> context -> term
  -> typing_result ((inductive × list Level.t) × list term).

Section TypeOf.
  Context {cf : checker_flags}.
  Context `{F : Fuel}.
  Context (Σ : global_env_ext).

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
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort s => ret (tSort (Universe.try_suc s))

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

  Conjecture cumul_reduce_to_sort : forall {Γ T s},
    reduce_to_sort (fst Σ) Γ T = Checked s ->
    Σ ;;; Γ |- T <= tSort s.

  Conjecture cumul_reduce_to_prod : forall {Γ T A B},
    reduce_to_prod (fst Σ) Γ T = Checked (A, B) ->
    forall n, Σ ;;; Γ |- T <= tProd n A B.

  Conjecture congr_cumul_letin : forall {Γ n a A t n' a' A' t'},
    Σ ;;; Γ |- a <= a' ->
    Σ ;;; Γ |- A <= A' ->
    Σ ;;; Γ ,, vdef n a A' |- t <= t' ->
    Σ ;;; Γ |- tLetIn n a A t <= tLetIn n' a' A' t'.

  Ltac case_eq_match :=
    lazymatch goal with
    | |- context [ match ?t with _ => _ end ] =>
      case_eq t ; try solve [ intros ; discriminate ]
    | h : context [ match ?t with _ => _ end ] |- _ =>
      revert h ;
      case_eq t ; try solve [ intros ; discriminate ]
    end.

  Ltac deal_as_sort :=
    lazymatch goal with
    | h : type_of_as_sort _ _ _ = _ |- _ =>
      unfold type_of_as_sort in h ;
      simpl in h
    end.

  Ltac deal_reduce_to_sort :=
    lazymatch goal with
    | h : reduce_to_sort _ _ _ = Checked _ |- _ =>
      pose proof (cumul_reduce_to_sort h) ;
      clear h
    end.

  Ltac deal_reduce_to_prod :=
    lazymatch goal with
    | h : reduce_to_prod _ _ _ = Checked _ |- _ =>
      let hh := fresh h in
      pose proof (cumul_reduce_to_prod h) as hh ;
      clear h ;
      lazymatch goal with
      | na : name |- _ => specialize (hh na)
      | |- _ => specialize (hh nAnon)
      end
    end.

  Ltac deal_Checked :=
    match goal with
    | h : Checked _ = Checked _ |- _ =>
      inversion h ; subst ; clear h
    end.

  Ltac go eq :=
    simpl in eq ; revert eq ;
    repeat (case_eq_match ; intros) ;
    repeat deal_as_sort ;
    repeat (case_eq_match ; intros) ;
    repeat deal_Checked ;
    repeat deal_reduce_to_sort ;
    repeat deal_reduce_to_prod.

  Ltac one_ih :=
    lazymatch goal with
    | h : _ -> _ -> (_ ;;; _ |- ?t : _) * _ |- _ ;;; _ |- ?t : _ =>
      eapply h
    | h : _ -> _ -> _ * (_ ;;; _ |- _ <= ?A) |- _ ;;; _ |- _ <= ?A =>
      eapply h
    end.

  Ltac ih :=
    one_ih ; eassumption.

  Ltac cih :=
    eapply type_Cumul ; [
      ih
    | try eassumption
    | try eassumption
    ].

  Theorem type_of_sound :
    forall {Γ t A B},
      Σ ;;; Γ |- t : A ->
      type_of Γ t = Checked B ->
      (Σ ;;; Γ |- t : B) * (Σ ;;; Γ |- B <= A).
  Proof.
    intros Γ t A B h eq. revert B eq.
    induction h ; intros T eq.
    - cbn in eq. rewrite e in eq.
      inversion eq. subst. clear eq.
      split.
      + econstructor ; eassumption.
      + eapply cumul_refl'.
    - cbn in eq. inversion eq. subst. clear eq.
      split.
      + (* Proving Typeᵢ : Typeᵢ₊₁ shouldn't be hard... *)
        admit.
      + (* destruct l. all: cbn. all: econstructor. all: cbn. all: try reflexivity. *)
        admit.
    - go eq.
      split.
      + econstructor ; try eassumption ; try ih ; try cih.
        (* Again we're missing result on how to type sorts... *)
        left. red. exists [], a.
        unfold app_context; simpl; intuition auto with pcuic.
        eapply typing_wf_local; tea.
        left. red. exists [], a0. unfold app_context; simpl; intuition auto with pcuic.
        eapply typing_wf_local; tea.
      + (* Sorts again *)
        simpl.
        admit.
    - go eq. split.
      + econstructor ; try eassumption ; try ih ; try cih.
      + eapply congr_cumul_prod.
        * eapply conv_alt_refl. reflexivity.
        * ih.
    - go eq. split.
      + econstructor ; try eassumption ; try ih ; try cih.
      + eapply congr_cumul_letin. all: try eapply cumul_refl'.
        ih.
    - go eq. split.
      + econstructor ; try eassumption ; try ih ; try cih.
        all: admit.
      + (* eapply cumul_subst. *)
        admit.
    - simpl in eq. split.
      + admit.
      + admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - split.
      + ih.
      + eapply cumul_trans ; try eassumption.
  Admitted.



End TypeOf.