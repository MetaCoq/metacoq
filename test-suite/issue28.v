Require Import MetaCoq.Template.All.
Require Export String List.
Open Scope string.
Import ListNotations.
Import MonadNotation.

Inductive test (X : Type) := test_T : test X -> test X.

Definition T :=
tFix
  [mkdef term (nNamed "f") (tProd (nNamed "x") (tApp (tInd (mkInd "Top.test" 0) []) [tInd (mkInd "Coq.Init.Datatypes.unit" 0) []]) (tInd (mkInd "Coq.Init.Datatypes.unit" 0) []))
     (tLambda (nNamed "x") (tApp (tInd (mkInd "Top.test" 0) []) [tRel 0])
        (tCase (mkInd "Top.test" 0, 1)
           (tLambda (nNamed "x") (tApp (tInd (mkInd "Top.test" 0) []) [tInd (mkInd "Coq.Init.Datatypes.unit" 0) []]) (tInd (mkInd "Coq.Init.Datatypes.unit" 0) []))
           (tRel 0)
           [(1, tLambda (nNamed "x0") (tApp (tInd (mkInd "Top.test" 0) []) [tInd (mkInd "Coq.Init.Datatypes.unit" 0) []]) (tApp (tRel 2) [tRel 0]))]))
     0] 0.
Fail MetaCoq Run (tmUnquote T >>= tmPrint).

Fail Let bla := (existT_typed_term (test unit -> unit) (fix f (x : test f) : unit := match x with
                                                                              | test_T _ x0 => f x0
                                                                              end)).
Fail MetaCoq Run (tmUnquote T >>= tmDefinition "fails").
