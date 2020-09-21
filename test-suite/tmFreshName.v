Require Import List Arith String.
Require Import MetaCoq.Template.All.
Import ListNotations MonadNotation.


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%string ;;
             tmDefinition x 0).

Check (eq_refl : xy = 0).


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%string ;;
             tmDefinition x 1).

Check (eq_refl : xy0 = 1).
