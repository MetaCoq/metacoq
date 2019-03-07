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

  Definition cored Σ Γ u v := red Σ Γ v u.

  Axiom normalisation :
    forall Σ Γ t A,
      Σ ;;; Γ |- t : A ->
      Acc (cored (fst Σ) Γ) t.

End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

  Derive NoConfusion NoConfusionHom for term.
  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  (* TODO Get equations in obligations *)
  (* Equations _reduce_stack (Γ : context) (t : term) (stack : list term) *)
  (*           (h : closedn #|Γ| t = true) *)
  (*           (* (reduce : forall Γ t' (stack : list term) (h : closedn #|Γ| t' = true), red (fst Σ) Γ t t' -> term * list term) *) *)
  (*           (reduce : forall t', red (fst Σ) Γ t t' -> term * list term) *)
  (*   : term * list term := *)
  (*   _reduce_stack Γ (tRel c) stack h reduce with RedFlags.zeta flags := { *)
  (*   | true with nth_error Γ c := { *)
  (*     | None := ! ; *)
  (*     | Some d with d.(decl_body) := { *)
  (*       | None := (tRel c, stack) ; *)
  (*       | Some b := reduce (lift0 (S c) b) _ *)
  (*       } *)
  (*     } ; *)
  (*   | false := (tRel c, stack) *)
  (*   } ; *)
  (*   _reduce_stack Γ t stack h reduce := (t, stack). *)
  (* Next Obligation. *)
  (*   econstructor. *)
  (*   - econstructor. *)
  (*   - eapply red_rel. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Abort. *)

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

  (* Program Definition _reduce_stack Γ t stack *)
  (*            (h : closedn #|Γ| t = true) *)
  (*            (reduce : forall t', red (fst Σ) Γ t t' -> term * list term) *)
  (*   : term * list term := *)
  (*   match t with *)
  (*   | tRel c => *)
  (*     if RedFlags.zeta flags then *)
  (*       match nth_error Γ c with *)
  (*       | None => ! *)
  (*       | Some d => *)
  (*         match d.(decl_body) with *)
  (*         | None => (t, stack) *)
  (*         | Some b => reduce (lift0 (S c) b) _ *)
  (*         end *)
  (*       end *)
  (*     else (t, stack) *)

  (*   | tLetIn _ b _ c => *)
  (*     if RedFlags.zeta flags then *)
  (*       reduce (subst10 b c) _ *)
  (*     else (t, stack) *)

  (*   | _ => (t, stack) *)
  (*   end. *)
  (* Next Obligation. *)
  (*   clear - h Heq_anonymous. revert c h Heq_anonymous. *)
  (*   induction Γ ; intros c h eq. *)
  (*   - cbn in *. discriminate. *)
  (*   - destruct c. *)
  (*     + cbn in eq. discriminate. *)
  (*     + cbn in eq, h. eapply IHΓ ; eassumption. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econstructor. *)
  (*   - econstructor. *)
  (*   - eapply red_rel. *)
  (*     rewrite <- Heq_anonymous0. cbn. f_equal. eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econstructor. *)
  (*   - econstructor. *)
  (*   - eapply red_zeta. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros. discriminate. *)
  (*   - intros. discriminate. *)
  (* Qed. *)

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