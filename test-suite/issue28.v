Require Import MetaCoq.Template.All.
Require Export String List.
Open Scope string.
Import ListNotations.
Import MCMonadNotation.

Inductive test (X : Type) := test_T : test X -> test X.

Definition tmLocateInd (q : qualid) : TemplateMonad kername :=
  l <- tmLocate q ;;
  match l with
  | [] => tmFail ("Inductive [" ++ q ++ "] not found")
  | (IndRef ind) :: _ => tmReturn ind.(inductive_mind)
  | _ :: _ => tmFail ("[" ++ q ++ "] not an inductive")
  end.

MetaCoq Run (tmLocateInd "Datatypes.unit" >>= tmDefinition "q_unit").
MetaCoq Run (tmLocateInd "test" >>= tmDefinition "q_test").

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition T :=
tFix
  [mkdef term (nNamed "f") (tProd (nNamed "x") (tApp (tInd (mkInd q_test 0) []) [tInd (mkInd q_unit 0) []]) (tInd (mkInd q_unit 0) []))
     (tLambda (nNamed "x") (tApp (tInd (mkInd q_test 0) []) [tRel 0])
        (tCase ((mkInd q_test 0, 1), Relevant)
           (tLambda (nNamed "x") (tApp (tInd (mkInd q_test 0) []) [tInd (mkInd q_unit 0) []]) (tInd (mkInd q_unit 0) []))
           (tRel 0)
           [(1, tLambda (nNamed "x0") (tApp (tInd (mkInd q_test 0) []) [tInd (mkInd q_unit 0) []]) (tApp (tRel 2) [tRel 0]))]))
     0] 0.
Fail MetaCoq Run (tmUnquote T >>= tmPrint).

Fail Let bla := (existT_typed_term (test unit -> unit) (fix f (x : test f) : unit := match x with
                                                                              | test_T _ x0 => f x0
                                                                              end)).
Fail MetaCoq Run (tmUnquote T >>= tmDefinition "fails").
