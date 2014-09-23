Require Import Template.Template.

Definition foo : nat. exact 0. Qed.

Local Open Scope string_scope.
Quote Recursively Definition foo_syn := foo.

Axiom really_opaque : nat.

Quote Recursively Definition really_opaque_syn := really_opaque.
