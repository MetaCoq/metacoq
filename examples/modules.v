From MetaCoq.Template Require Import All.
Import MCMonadNotation.

 Inductive roseTree :=
 | node (xs : list roseTree).
 (* | node_nil 
 | node_cons (r: roseTree) (xs: roseTree). *)

Inductive All {A} (P : A -> Prop) : list A -> Prop :=
  | All_nil : All P nil
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (cons x l).

 (* Check roseTree_ind.
 Theorem roseTree_ind' : forall P : roseTree -> Prop,
   (forall (xs : list roseTree) (allxs : All P xs), P (node xs)) -> forall r : roseTree, P r.
   Proof.
    intros P IH r. destruct r. induction xs; apply IH.
    - apply All_nil.
    - specialize (IH (cons r xs)).
      
 *)

Module M. 
    MetaCoq Quote Recursively Definition a := 0.
    Print a.
    Module N.
        MetaCoq Quote Recursively Definition b := 0.
        Print b. (* should see a, b in env *)
        Check a.
        Module N1.
            MetaCoq Quote Recursively Definition b := 0.
            Print b. (* should see a, b in env *)
            Check a.
        End N1.
    End N.
    MetaCoq Quote Recursively Definition c := 0.
    Print c. (* should see a in env *)
End M.

Module N := M.


MetaCoq Run (tmQuoteModule "M"%bs >>= tmPrint).
MetaCoq Run (tmQuoteModule "N"%bs >>= tmPrint).

MetaCoq Quote Recursively Definition a := 0.

Module MM := M.
MetaCoq Run (tmQuoteModule "MM"%bs >>= tmPrint).

Print a.

Module M1.
    Definition b1 := 0.

    MetaCoq Quote Recursively Definition a := 0.
    Print a.
    Module N1.
    End N1.
    MetaCoq Test Quote "N1"%bs.
    Module M := N1.
    MetaCoq Test Quote "M"%bs.
    

    Definition div (n m: nat) := exists d: nat, d * n = m.
    Definition div_strict (a b: nat) := (div a b) /\ (a <> b). (* Strict partial order *)
    Theorem one_div_everything (n: nat): div 1 n.
    Proof.
        induction n. now exists 0.
        now exists (S n).
    Qed.

    Definition b2 := true.

    Module N2.
        MetaCoq Quote Recursively Definition c := 100.
        Print c.
    End N2.

    Definition b3 := "b3".
End M1.

Definition a1 := "a1".

Module M2.
    Definition b4 := "b4".
End M2.

Definition a2 := "a2".
