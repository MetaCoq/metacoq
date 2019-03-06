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

  Axiom normalisation :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      Acc (red (fst Σ) Γ) t.

End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

  (* TODO Get equations in obligations *)
  (* Equations _reduce_stack (Γ : context) (t : term) (stack : list term) *)
  (*           (h : closedn #|Γ| t = true) *)
  (*           (reduce : forall Γ t' (stack : list term) (h : closedn #|Γ| t' = true), red Σ Γ t t' -> term * list term) *)
  (*   : term * list term := *)
  (*   _reduce_stack Γ (tRel c) stack h reduce with RedFlags.zeta flags := { *)
  (*   | true with nth_error Γ c := { *)
  (*     | None := ! ; *)
  (*     | Some d with d.(decl_body) := { *)
  (*       | None := (tRel c, stack) ; *)
  (*       | Some b := reduce Γ (lift0 (S c) b) stack _ _ *)
  (*       } *)
  (*     } ; *)
  (*   | false := (tRel c, stack) *)
  (*   } ; *)
  (*   _reduce_stack Γ t stack h reduce := (t, stack). *)
  (* Next Obligation. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (*   econstructor. *)
  (*   - econstructor. *)
  (*   - econstructor. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Abort. *)

  Program Definition _reduce_stack Γ t stack
             (h : closedn #|Γ| t = true)
             (reduce : forall Γ t' stack h, red (fst Σ) Γ t t' -> term * list term)
    : term * list term :=
    match t with
    | tRel c =>
      if RedFlags.zeta flags then
        match nth_error Γ c with
        | None => !
        | Some d =>
          match d.(decl_body) with
          | None => (t, stack)
          | Some b => reduce Γ (lift0 (S c) b) stack h _
          end
        end
      else (t, stack)
    | _ => (tRel 0, [])
    end.
  Next Obligation.
    clear - h Heq_anonymous. revert c h Heq_anonymous.
    induction Γ ; intros c h eq.
    - cbn in *. discriminate.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq, h. eapply IHΓ ; eassumption.
  Qed.
  Next Obligation.
    econstructor. econstructor. eapply red_rel.
    rewrite <- Heq_anonymous0. cbn. f_equal. eauto.
  Qed.

  Equations reduce_stack (Γ : context) (t A : term) (stack : list term)
            (h : Σ ;;; Γ |- t : A) : term * list term :=
    reduce_stack Γ t A stack h :=
      Fix_F (R := red (fst Σ) Γ)
            (fun x => (term * list term)%type)
            (fun t' f => _) (x := t) _.
  Next Obligation.
    eapply _reduce_stack.
    - exact stack.
    - shelve.
    - intros Γ0 t'0 stack0 h0 H0.
      eapply f. admit.
  Admitted.
  Next Obligation.
    eapply normalisation. eassumption.
  Defined.

  (* Program Definition reduce_stack Γ t stack h := *)
  (*   Fix_F (R := red Σ Γ) *)
  (*         (fun x => (term * list term)%type) *)
  (*         (fun t' f => _reduce_stack Γ t stack h (fun Γ t' stack h => f t')). *)
  (* Next Obligation. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Admitted. *)

End Reduce.