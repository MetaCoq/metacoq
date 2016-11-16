Require Import Template.Template.
Require Import Template.Ast.
Open Scope string_scope.

(* [proj2] is opaque*)
Quote Recursively Definition pp := proj2.
Print pp.

Fixpoint getFirstConstr (p:program) : option term :=
match p with
| PConstr _ t _ => Some t
| PType _ _ _ p => getFirstConstr p
| PAxiom _ t p => getFirstConstr p
| PIn _ => None
end.

(* getFirstConstr extracts the definition of proj2 *)
Eval compute in (getFirstConstr pp).

(*

     = Some
         (tLambda (nNamed "A") (tSort sProp)
            (tLambda (nNamed "B") (tSort sProp)
               (tLambda (nNamed "H")
                  (tApp (tInd (mkInd "Coq.Init.Logic.and" 0)) (tRel 1 :: (tRel 0 :: nil)%list))
                  (tCase (mkInd "Coq.Init.Logic.and" 0, 2)
                     (tLambda nAnon
                        (tApp (tInd (mkInd "Coq.Init.Logic.and" 0)) (tRel 2 :: (tRel 1 :: nil)%list)) 
                        (tRel 2)) (tRel 0)
                     ((2, tLambda (nNamed "H") (tRel 2) (tLambda (nNamed "H0") (tRel 2) (tRel 0))) :: nil)))))
     : option term

*)

Ltac computeExtract f:=
(let t:= eval compute in f in 
match t with
|Some ?xx => constr:xx
end).

(* As shown above, (getFirstConstr pp) has A:Prop. It seems that Unquoting incorrectly changes it to A:Set *)
Make Definition proj2_t := 
  ltac:(let t:= computeExtract (getFirstConstr pp) in exact t).

Print proj2_t.


(*
Ltac nop t := idtac t.
Goal False.
quote_term proj2 nop.
*)


