From Coq Require Import String List PeanoNat.
From MetaCoq.Template Require Import All.

Import MCMonadNotation String ListNotations.

Definition foo : nat. exact 0. Qed.

Local Open Scope string_scope.
MetaCoq Quote Recursively Definition foo_syn := foo.
MetaCoq Quote Recursively Definition comm_syn := PeanoNat.Nat.add_comm.

Axiom really_opaque : nat.

MetaCoq Quote Recursively Definition really_opaque_syn := really_opaque.

MetaCoq Run (foo_t <- tmQuoteRecTransp foo false ;; (* quote respecting transparency *)
             foo_o <- tmQuoteRec foo ;; (* quote ignoring transparency settings  *)
             tmDefinition "foo_t" foo_t ;;
             tmDefinition "foo_o" foo_o).

Example foo_quoted_correctly :
  (exists c v, lookup_env (fst foo_t) (MPfile ["opaque"; "TestSuite"; "MetaCoq"], "foo") = Some v /\
    v = ConstantDecl c /\ c.(cst_body) = None) /\
    (exists c v, lookup_env (fst foo_o) (MPfile ["opaque"; "TestSuite"; "MetaCoq"], "foo") = Some v /\
    v = ConstantDecl c /\ c.(cst_body) <> None ).
Proof.
  split;eexists;eexists;cbn; now intuition.
Qed.

Time MetaCoq Run (t <- tmQuoteRecTransp Nat.le_add_r false ;;
                  tmDefinition "add_comm_syn" t). (* quote respecting transparency *)

Time MetaCoq Run (t <- tmQuoteRec Nat.le_add_r ;;
                  tmDefinition "add_comm_syn'" t). (* quote ignoring transparency settings  *)
