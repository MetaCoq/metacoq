From Coq Require Import List Lia.
From MetaCoq.Template Require Import config utils BasicAst AstUtils
     Universes Environment EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping.
From Equations Require Import Equations.

Require Import ssreflect.

(** Variation on lift_typing to enable a different predicate for checking a body and infering a sort when there is no body *)
Definition lift_sorting
  (checking : global_env_ext -> context -> term -> term -> Type)
  (sorting : global_env_ext -> context -> term -> Universe.t -> Type) :
  (global_env_ext -> context -> term -> option term -> Type) :=
    fun Σ Γ t T =>
    match T with
    | Some T => checking Σ Γ t T
    | None => { s : Universe.t & sorting Σ Γ t s }
    end.

  Section All_local_env_rel.

  Definition All_local_rel P Γ Γ'
    := (All_local_env (fun Γ0 t T => P (Γ ,,, Γ0) t T) Γ').

  Definition All_local_rel_nil {P Γ} : All_local_rel P Γ []
    := localenv_nil.

  Definition All_local_rel_abs {P Γ Γ' A na} :
    All_local_rel P Γ Γ' -> P (Γ ,,, Γ') A None
    -> All_local_rel P Γ (Γ',, vass na A)
    := localenv_cons_abs.

  Definition All_local_rel_def {P Γ Γ' t A na} :
    All_local_rel P Γ Γ' ->
    P (Γ ,,, Γ') A None ->
    P (Γ ,,, Γ') t (Some A) ->
    All_local_rel P Γ (Γ',, vdef na t A)
    := localenv_cons_def.

  Lemma All_local_rel_local :
    forall P Γ,
      All_local_env P Γ ->
      All_local_rel P [] Γ.
  Proof.
    intros P Γ h. eapply All_local_env_impl.
    - exact h.
    - intros Δ t [] h'.
      all: cbn.
      + rewrite app_context_nil_l. assumption.
      + rewrite app_context_nil_l. assumption.
  Defined.

  Lemma All_local_local_rel P Γ :
    All_local_rel P [] Γ -> All_local_env P Γ.
  Proof.
    intro X. eapply All_local_env_impl. exact X.
    intros Γ0 t [] XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
  Defined.

  Lemma All_local_app_rel {P Γ Γ'} :
    All_local_env P (Γ ,,, Γ') -> All_local_env P Γ × All_local_rel P Γ Γ'.
  Proof.
    induction Γ'.
    - intros hΓ.
      split.
      1: exact hΓ.
      constructor.
    - inversion 1 ; subst.
      all: edestruct IHΓ' ; auto.
      all: split ; auto.
      all: constructor ; auto.
  Defined.

  Lemma All_local_rel_app {P Γ Γ'} :
    All_local_env P Γ -> All_local_rel P Γ Γ' -> All_local_env P (Γ ,,, Γ').
  Proof.
    intros ? hΓ'.
    induction hΓ'.
    - assumption.
    - cbn.
      constructor ; auto.
    - cbn.
      constructor ; auto.
  Defined.

End All_local_env_rel.

Section All_local_env_size.

  Context (P : context -> term -> option term -> Type) (Psize : forall Γ t T, P Γ t T -> size).

  Fixpoint All_local_env_size Γ (w : All_local_env P Γ) : size :=
    match w with
    | localenv_nil => 1
    | localenv_cons_abs Γ' na t w' p => Psize _ _ _ p + All_local_env_size _ w'
    | localenv_cons_def Γ' na b t w' pt pb => Psize _ _ _ pt + Psize _ _ _ pb + All_local_env_size _ w'
    end.

  Lemma All_local_env_size_pos Γ w : 0 < All_local_env_size Γ w.
  Proof.
    induction w.
    all: simpl ; lia.
  Qed.

End All_local_env_size.

Lemma All_local_env_size_app P Psize Γ Γ' (wfΓ : All_local_env P Γ) (wfΓ' : All_local_rel P Γ Γ') :
  All_local_env_size _ Psize _ (All_local_rel_app wfΓ wfΓ') + 1 = All_local_env_size _ Psize _ wfΓ + All_local_env_size _ (fun Δ => Psize (Γ,,,Δ)) _ wfΓ'.
Proof.
  induction Γ'.
  - dependent inversion wfΓ'.
    reflexivity.
  - revert IHΓ'.
    dependent inversion wfΓ' ; subst ; intros.
    + cbn.
      etransitivity.
      2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
      reflexivity.
    + cbn.
      etransitivity.
      2: rewrite Nat.add_comm -Nat.add_assoc [X in _ + X]Nat.add_comm -IHΓ' Nat.add_assoc ; reflexivity.
      reflexivity.
Qed. 
      

Section SortingEnv.

  Context (checking : global_env_ext -> context -> term -> term -> Type).
  Context (sorting : global_env_ext -> context -> term -> Universe.t -> Type).

  (** Corresponding All_local_env_over predicate *)

  Section TypeLocalOver.
    Context (cproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_sorting checking sorting Σ) Γ ->
                forall (t T : term), checking Σ Γ t T -> Type).
    Context (sproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_sorting checking sorting Σ) Γ ->
                forall (t : term) (s : Universe.t), sorting Σ Γ t s -> Type).

    Inductive All_local_env_over_sorting (Σ : global_env_ext) :
        forall (Γ : context), All_local_env (lift_sorting checking sorting Σ) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over_sorting Σ [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_sorting checking sorting Σ) Γ) :
        All_local_env_over_sorting Σ Γ all ->
        forall (tu : lift_sorting checking sorting Σ Γ t None),
          sproperty Σ Γ all _ _ (projT2 tu) ->
          All_local_env_over_sorting Σ (Γ ,, vass na t)
                              (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_sorting checking sorting Σ) Γ) (tb : checking Σ Γ b t) :
        All_local_env_over_sorting Σ Γ all ->
        cproperty Σ Γ all _ _ tb ->
        forall (tu : lift_sorting checking sorting Σ Γ t None),
          sproperty Σ Γ all _ _ (projT2 tu) ->
          All_local_env_over_sorting Σ (Γ ,, vdef na b t)
                              (localenv_cons_def all tu tb).

  End TypeLocalOver.
  Derive Signature for All_local_env_over_sorting.


  Section All_local_env_size.
    Context (csize : forall (Σ : global_env_ext) (Γ : context) (t T : term), checking Σ Γ t T -> size).
    Context (ssize : forall (Σ : global_env_ext) (Γ : context) (t : term) (u : Universe.t), sorting Σ Γ t u -> size).
    Context (Σ : global_env_ext).

    Definition lift_sorting_size Γ t T (w : lift_sorting checking sorting Σ Γ t T) : size.
    Proof.
      destruct T.
      - exact (csize _ _ _ _ w).
      - exact (ssize _ _ _ _ w.π2).
    Defined.

    Definition All_local_env_sorting_size := All_local_env_size _ lift_sorting_size.
    Definition All_local_rel_sorting_size Γ Γ' (wfΓ' : All_local_rel (lift_sorting checking sorting Σ) Γ Γ') := All_local_env_size _ (fun Δ => lift_sorting_size (Γ ,,, Δ)) Γ' wfΓ'.

  End All_local_env_size.

End SortingEnv.
