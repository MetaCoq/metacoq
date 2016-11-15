Require Import Template.Template.
Require Import Template.Ast.
Open Scope string_scope.

Lemma snd : forall A B : Set, A * B -> B.
Proof.
  intros ? ? p. destruct p. assumption.
Qed.

Eval vm_compute in (snd _ _ (1,2)).

Quote Recursively Definition pp := snd.
Print pp.


(* Assuming p contains only 1 definition. If snd used 
other definitions, this function would fail when applied to pp.
A general version let bind the additional functions.
*)
Fixpoint getFirstConstr (p:program) : option term :=
match p with
| PConstr _ t _ => Some t
| PType _ _ _ p => getFirstConstr p
| PAxiom _ t p => getFirstConstr p
| PIn _ => None
end.

(* getFirstConstr extracts the definition of snd *)
Eval compute in (getFirstConstr pp).

(*

     = Some
         (tLambda (nNamed "A") (tSort sSet)
            (tLambda (nNamed "B") (tSort sSet)
               (tLambda (nNamed "p")
                  (tApp (tInd (mkInd "Coq.Init.Datatypes.prod" 0))
                     (tRel 1 :: (tRel 0 :: nil)%list))
                  (tCase (mkInd "Coq.Init.Datatypes.prod" 0, 2)
                     (tLambda (nNamed "p")
                        (tApp (tInd (mkInd "Coq.Init.Datatypes.prod" 0))
                           (tRel 2 :: (tRel 1 :: nil)%list)) (tRel 2)) 
                     (tRel 0)
                     ((2,
                      tLambda (nNamed "a") (tRel 2) (tLambda (nNamed "b") (tRel 2) (tRel 0)))
                      :: nil)))))
     : option term

*)

Ltac computeExtract f:=
(let t:= eval compute in f in 
match t with
|Some ?xx => constr:xx
end).

Make Definition snd_t := 
  ltac:(let t:= computeExtract (getFirstConstr pp) in exact t).

Print snd_t.
(*
snd = fun (A B : Set) (p : A * B) => let (_, b) := p in b
     : forall A B : Set, A * B -> B
*)


(*
If Set is replaced with Type in snd, the following error occurs when defining snd_t.
Anomaly: Uncaught exception Reify.TermReify.NotSupported(_). Please report.
*)




