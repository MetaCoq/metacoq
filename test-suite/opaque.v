Require Import Template.Template.

Definition foo : nat. exact 0. Qed.

Local Open Scope string_scope.
Quote Recursively Definition foo_syn := foo.
