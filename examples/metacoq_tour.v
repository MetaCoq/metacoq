From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.PCUIC Require Import PCUICAst PCUICReduction PCUICCumulativity PCUICTyping PCUICSafeLemmata.

Import MCMonadNotation.
Local Open Scope bs_scope.

(** MetaCoq is:

  - The "template-coq" monad, dealing with reification of terms
    and environments.
  - The PCUIC development of the syntactic metatheory of Coq.
  - The SafeChecker package implementing reduction, conversion
    and typechecking in a sound and complete way.
  - The Erasure package implementing verified extraction to
    untyped lambda-calculus
*)

(* The Template monad *)

Print Ast.term.


MetaCoq Quote Definition reifx := (fun x : nat => x).
Definition foo := (fun x : nat => fun x : nat => x).
MetaCoq Quote Definition reifx' := Eval compute in (fun x : nat => let y := x in fun x : nat => y).
Print reifx'.
MetaCoq Unquote Definition x :=
  (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 0 []).

MetaCoq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaCoq Run (t <- tmLemma "foo44" nat ;;
             qt <- tmQuote t ;;
             t <- tmEval all t ;;
             tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.

(* PCUIC:

    + Universes (with full algebraic universes supported everywhere)
    + Universe polymorphism
    + Standard type theory with dependent products and let-ins
    + Inductive types and coinductive types
    + Constant and axiom declarations in a global environment *)

Print typing.

Check type_Sort.
Check type_LetIn.
Check type_Const.

From MetaCoq.PCUIC Require PCUICSR.

Check PCUICSR.subject_reduction.

(** Verified conversion and type-checking *)

From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICTypeChecker PCUICSafeChecker PCUICSafeRetyping.
From MetaCoq.SafeCheckerPlugin Require Import Loader.
Check PCUICSafeConversion.isconv_term_sound.
Check PCUICSafeConversion.isconv_term_complete.

Check PCUICSafeChecker.infer_wf_env.
(** Proof of completeness is near completion. *)

(** Verified retyping: from a term that is known to be well-typeable,
  compute its principal type. Very common in tactics to avoid retypechecking
  the whole term. *)
Check type_of.
Check type_of_subtype.

(* Running the safe checker inside Coq *)
From MetaCoq.Examples Require Import metacoq_tour_prelude.

Check check_inh.

(** We construct a proof of typing entirely within Coq, calling the typechecker to produce the derivation *)
(* Lemma identity_typing (u := Universe.make univ):
  inh gctx_wf_env [] (tProd (bNamed "s") (tSort u) (tImpl (tRel 0) (tRel 0))).
Proof.
  (* We construct a term *)
  set (impl := tLambda (bNamed "s") (tSort u) (tLambda bAnon (tRel 0) (tRel 0))).
  (* Show that the empty context is well-formed  *)
  assert (wfΓ : forall Σ0 : global_env_ext, abstract_env_ext_rel gctx_wf_env Σ0 -> ∥ wf_local Σ0 [] ∥) by do 2 constructor.
  fill_inh impl.
Qed. *)

(** The extracted typechecker also runs in OCaml *)
(* FIXME: checker unusable in OCaml due to representation of universes *)
(* MetaCoq SafeCheck (fun x : nat => x + 1). *)

(** Erasure *)
From MetaCoq.ErasurePlugin Require Import Erasure Loader.

(** Running erasure live in Coq *)
Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

MetaCoq Quote Recursively Definition zero := 0.

Definition zerocst := Eval lazy in test zero.

Definition singleton_elim :=
  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

MetaCoq Run (tmEval lazy singleton_elim >>= tmQuoteRec >>=
  fun p => tmEval lazy (test p) >>= tmPrint). (* Optimized to remove match on Props *)

MetaCoq Erase singleton_elim.

(** Conclusion: Status of MetaCoq

  - Correctness and complete typechecker for (a large fragment of) Coq.

  - All metatheory proofs are finished. Compared to Coq's implementation:

    - full (max (i + k, j + l)) universe support (including a naïve acyclicity checking
      algorithm)

    - partial support for SProp (in programs but not yet formalized typing rules)

    - approximate cumulative inductive types checking (not yet up to reduction)

    - missing eta-conversion: the plan is to use contravariant subtyping and eta-reduction,
      as in Coq CEP #47

    - missing template-polymorphism: we're studying a sort polymorphism extension
      (with G. Gilbert, K. Maillard and N. Tabareau) to subsume it completely.

    - missing modules and fast conversion machines.

  - Much work to come on the template-coq side to ease meta-programming.

  - Relation to CertiCoq: fast and verified correct erasure, not depending on type-checking
    (only retyping).

    + CertiCoq needs to have all constructors eta-expanded, a proof of the
      syntactic translation expanding constructors is in progress.

    + Otherwise the front-end part of CertiCoq is complete with proofs.

    + Future work: handling of primitive types (ints, floats, arrays, ...)

*)



