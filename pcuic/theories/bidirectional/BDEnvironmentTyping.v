From Coq Require Import List Lia.
From MetaCoq.Template Require Import config utils BasicAst AstUtils
     Universes Environment EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping.
From Equations Require Import Equations.

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

    Fixpoint All_local_env_sorting_size Γ (w : All_local_env (lift_sorting checking sorting Σ) Γ) : size :=
      match w with
      | localenv_nil => 1
      | localenv_cons_abs Γ na t wfΓ h => ssize _ _ _ _ h.π2 + All_local_env_sorting_size _ wfΓ
      | localenv_cons_def Γ na b t wfΓ ht hb => ssize _ _ _ _ ht.π2 + csize _ _ _ _ hb + All_local_env_sorting_size _ wfΓ
      end.

    Lemma All_local_env_sorting_size_pos Γ w : 0 < All_local_env_sorting_size Γ w.
    Proof.
      induction w.
      all: simpl ; lia.
    Qed.

  End All_local_env_size.

End SortingEnv.
