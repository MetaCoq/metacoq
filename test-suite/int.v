Require Import MetaCoq.Template.Loader.
Require Import Int63.

Definition n : Int63.int := 42.
Import List.ListNotations.
Definition ns : list Int63.int := [n]%list.


MetaCoq Quote Recursively Definition q_n := n.
MetaCoq Unquote Definition n' := (snd q_n).

MetaCoq Quote Recursively Definition q_ns := ns.
MetaCoq Unquote Definition ns' := (snd q_ns).

