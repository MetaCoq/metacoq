# Safe Checker

In [PCUICSafeReduce](SafeReduce.v) we define a function `reduce_stack` that
implements weak-head reduction (parametrised by reduction flags `RedFlags.t`)
for PCUIC terms, without *fuel* (it is defined by well-founded induction).

In the same fashion, [PCUICSafeConversion](SafeConversion.v) contains a verifed
implementation of a conversion checker.

Finally [PCUICSafeChecker](SafeChecker.v) deals with type inference for PCUIC,
and thus type checking.

All of these are proven correct but not yet complete.
They are suited for extraction which would remove the termination and
correctness proofs.
