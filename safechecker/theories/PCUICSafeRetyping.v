(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeLemmata
     PCUICUnivSubst PCUICTyping PCUICChecker PCUICConversion PCUICCumulativity PCUICSN PCUICValidity.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker.
Require Import String ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MonadNotation.
  Derive NoConfusion for type_error.

Add Search Blacklist "_graph_mut".

(** * Retyping

  The [type_of] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t
  := (global_ext_levels Σ, global_ext_constraints Σ).

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Lemma typing_wellformed Γ t T : Σ ;;; Γ |- t : T -> wellformed Σ Γ T.
  Proof.
    intros H.
    destruct hΣ. destruct Hφ.
    apply validity in H; auto. destruct H as [wfg [wfA | [s tyT]]].
    right. constructor. auto. left. econstructor; eauto.
    now eapply typing_wf_local.
  Qed.


  Section SortOf.
    Context (type_of : forall Γ t, welltyped Σ Γ t -> typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥)).

    Program Definition type_of_as_sort Γ t (wf : welltyped Σ Γ t) : typing_result universe :=
      tx <- type_of Γ t wf ;;
      wfs <- @reduce_to_sort cf Σ hΣ Γ (projT1 tx) _ ;;
      ret (m:=typing_result) (projT1 wfs).
    Next Obligation. destruct X. now eapply typing_wellformed. Qed.

  End SortOf.

  Ltac unsquash :=
    repeat match goal with
             [ H : ∥ _ ∥ |- _  ] => destruct H as [H]
           | [ H : welltyped _ _ _ |- _ ] => let ty := fresh "ty" in destruct H as [ty H]
         end; try apply sq.

  Program Definition option_or {A} (a : option A) (e : type_error) : typing_result (∑ x : A, a = Some x) :=
    match a with
    | Some d => ret (d; eq_refl)
    | None => raise e
    end.

  Program Fixpoint type_of (Γ : context) (t : term) : welltyped Σ Γ t ->
                                                      typing_result (∑ T : term, ∥ Σ ;;; Γ |- t : T ∥) :=
    match t return welltyped Σ Γ t -> typing_result (∑ T : term, ∥ Σ ;;; Γ |- t : T ∥) with
    | tRel n => fun wf =>
                  t <- option_or (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) (UnboundRel n);;
                  ret (t.π1; _)

    | tVar n => fun wf => raise (UnboundVar n)
    | tEvar ev args => fun wf => raise (UnboundEvar ev)

    | tSort s => fun wf => ret (tSort (Universe.try_suc s); _)

    | tProd n t b => fun wf =>
      s1 <- type_of_as_sort type_of Γ t _ ;;
      s2 <- type_of_as_sort type_of (Γ ,, vass n t) b _ ;;
      ret (tSort (Universe.sort_of_product s1 s2); _)

    | tLambda n t b => fun wf =>
      t2 <- type_of (Γ ,, vass n t) b _;;
      ret (tProd n t t2.π1; _)

    | tLetIn n b b_ty b' => fun wf =>
      b'_ty <- type_of (Γ ,, vdef n b b_ty) b' _ ;;
      ret (tLetIn n b b_ty b'_ty.π1; _)

    | tApp t a => fun wf =>
      ty <- type_of Γ t _ ;;
      pi <- reduce_to_prod hΣ Γ ty.π1 _ ;;
      ret (subst10 a pi.π2.π2.π1; _)

    | tConst cst u => fun wf =>
          match lookup_env (fst Σ) cst with
          | Some (ConstantDecl _ d) =>
            let ty := subst_instance_constr u d.(cst_type) in
            ret (ty; _)
          |  _ => raise (UndeclaredConstant cst)
          end

    | tInd ind u => fun wf =>
          d <- @lookup_ind_decl Σ ind ;;
          let ty := subst_instance_constr u d.π2.π1.(ind_type) in
          ret (ty; _)

    | tConstruct ind k u => fun wf =>
          d <- @lookup_ind_decl Σ ind ;;
          match nth_error d.π2.π1.(ind_ctors) k with
          | Some cdecl =>
            ret (type_of_constructor d.π1 cdecl (ind, k) u; _)
          | None => raise (UndeclaredConstructor ind k)
          end

    | tCase (ind, par) p c brs => fun wf =>
      ty <- type_of Γ c _ ;;
      indargs <- reduce_to_ind hΣ Γ ty.π1 _ ;;
      ret (mkApps p (List.skipn par indargs.π2.π2.π1 ++ [c]); _)

    | tProj (ind, n, k) c => fun wf =>
       d <- @lookup_ind_decl Σ ind ;;
       match nth_error d.π2.π1.(ind_projs) k with
       | Some pdecl =>
            c_ty <- type_of Γ c _ ;;
            indargs <- reduce_to_ind hΣ Γ c_ty.π1 _ ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance_constr indargs.π2.π1 ty);
                   _)
       | None => !
       end

    | tFix mfix n => fun wf =>
      match nth_error mfix n with
      | Some f => ret (f.(dtype); _)
      | None => raise (IllFormedFix mfix n)
      end

    | tCoFix mfix n => fun wf =>
      match nth_error mfix n with
      | Some f => ret (f.(dtype); _)
      | None => raise (IllFormedFix mfix n)
      end
    end.

  Next Obligation.
    unsquash.
    destruct (nth_error Γ n) eqn:Heq; try discriminate. injection X. intros <-.
    econstructor; eauto using typing_wf_local.
  Defined.

  Solve All Obligations with program_simpl; match goal with
                                              [ |- ∥ _ ∥ ] => todo "PCUICSafeRetyping.type_of"
                                            | [ |- welltyped _ _ _ ] => todo "PCUICSafeRetyping.type_of"
                                            | [ |- wellformed _ _ _ ] => todo "PCUICSafeRetyping.type_of"
                             end.
  Next Obligation.
    todo "PCUICSafeRetyping.type_of".
  Defined.

  (* Program Definition sort_of (Γ : context) (t : term) (wf : welltyped Σ Γ t) : typing_result universe := *)
  (*   ty <- type_of Γ t wf;; *)
  (*   type_of_as_sort type_of Γ ty.π1 _. *)
  (* Next Obligation. *)


  Open Scope type_scope.

  Conjecture cumul_reduce_to_sort : forall {Γ T wf s},
    reduce_to_sort hΣ Γ T wf = Checked s ->
    Σ ;;; Γ |- T <= tSort s.π1.

  Conjecture cumul_reduce_to_prod : forall {Γ T wf na A B H},
    reduce_to_prod hΣ Γ T wf = Checked (na; A; B; H) ->
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

  Definition map_typing_result {A B} (f : A -> B) (e : typing_result A) : typing_result B :=
    match e with
    | Checked a => Checked (f a)
    | TypeError e => TypeError e
    end.

  From Equations Require Import Equations DepElim.
  Set Equations With UIP.
  Theorem type_of_principal :
    forall {Γ t B} ,
      forall (wt : welltyped Σ Γ t) wt',
      type_of Γ t wt = Checked (B; wt') ->
      forall A, Σ ;;; Γ |- t : A -> Σ ;;; Γ |- B <= A.
  Proof.
    intros Γ t B wt wt' eq. simpl in wt'. revert B wt' eq. simpl in wt.
    induction t using term_forall_list_ind; intros B wt' eq A wA.
    - cbn in eq. destruct option_or eqn:Heq.
      destruct a as [x Hx]. simpl in eq.
      inversion eq. subst. clear eq. clear Heq.
  Admitted. (* Just inversion lemmas, as we're inducting on the term *)

  (*     rewrite Hx in Heq. simpl in Heq. rewrite e in Hx. simpl in Hx. noconf Hx. *)
  (*     + eapply cumul_refl'. *)
  (*     + simpl in eq. discriminate. *)
  (*   - cbn in eq. inversion eq. subst. clear eq. *)
  (*     constructor. red. constructor. simpl. simpl. *)
  (*     + (* Proving Typeᵢ : Typeᵢ₊₁ shouldn't be hard... *) *)
  (*       admit. *)
  (*   - go eq. *)
  (*     unfold type_of_as_sort. rewrite *)
  (*     split. *)
  (*     + econstructor ; try eassumption ; try ih ; try cih. *)
  (*       (* Again we're missing result on how to type sorts... *) *)
  (*       left. red. exists [], a. *)
  (*       unfold app_context; simpl; intuition auto with pcuic. *)
  (*       eapply typing_wf_local; tea. *)
  (*       left. red. exists [], a0. unfold app_context; simpl; intuition auto with pcuic. *)
  (*       eapply typing_wf_local; tea. *)
  (*     + (* Sorts again *) *)
  (*       simpl. *)
  (*       admit. *)
  (*   - go eq. split. *)
  (*     + econstructor ; try eassumption ; try ih ; try cih. *)
  (*     + eapply congr_cumul_prod. *)
  (*       * eapply conv_alt_refl. reflexivity. *)
  (*       * ih. *)
  (*   - go eq. split. *)
  (*     + econstructor ; try eassumption ; try ih ; try cih. *)
  (*     + eapply congr_cumul_letin. all: try eapply cumul_refl'. *)
  (*       ih. *)
  (*   - go eq. split. *)
  (*     + econstructor ; try eassumption ; try ih ; try cih. *)
  (*       all: admit. *)
  (*     + (* eapply cumul_subst. *) *)
  (*       admit. *)
  (*   - simpl in eq. split. *)
  (*     + admit. *)
  (*     + admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - split. *)
  (*     + ih. *)
  (*     + eapply cumul_trans ; try eassumption. *)
  (* Admitted. *)



End TypeOf.
