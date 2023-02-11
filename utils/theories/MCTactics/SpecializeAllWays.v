Require Export MetaCoq.Utils.MCTactics.UniquePose.

Ltac specialize_all_ways :=
  repeat match goal with
         | [ H : ?A, H' : forall a : ?A, _ |- _ ]
           => unique pose proof (H' H)
         end.
