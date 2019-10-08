Require Import MetaCoq.Template.Loader.

Definition foo : nat. exact 0. Qed.

Local Open Scope string_scope.
MetaCoq Quote Recursively Definition foo_syn := foo.

Axiom really_opaque : nat.

MetaCoq Quote Recursively Definition really_opaque_syn := really_opaque.
