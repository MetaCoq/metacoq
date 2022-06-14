Require Import List Arith.
Require Import MetaCoq.Template.All.
Import ListNotations MCMonadNotation.


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 0).

Check (eq_refl : xy = 0).


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 1).

Check (eq_refl : xy0 = 1).
