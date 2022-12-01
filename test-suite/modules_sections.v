From MetaCoq.Template Require Import utils All.
Import MCMonadNotation.


Module Type A.
  Parameter x : nat.
End A.

Module B (X : A) (Y : A).

  MetaCoq Test Quote Y.x.
  MetaCoq Unquote Definition uuu :=
          (tConst (MPbound ["modules_sections"; "TestSuite"; "MetaCoq"] "Y" 1, "x") []).


  MetaCoq Run (bc <- tmQuote X.x ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).

End B.


Module Type C (X : A) (Y : A).
  MetaCoq Run (bc <- tmQuote X.x ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).
End C.


Section S.

  Definition b := forall X, X.
  Definition c := Set.
  (* Set Printing All. Set Printing Universes. *)
  MetaCoq Run (bc <- tmQuote b ;;
                    tmPrint bc ;;
                    tmMkDefinition "bb" bc ;;
                    tmPrint "lol").
  Check bb.

  Variable x : nat.
  MetaCoq Run (bc <- tmQuote x ;;
                    tmPrint bc ;;
                    tmMkDefinition "bx" bc ;;
                    tmPrint "lol").

  Check bx.

End S.

MetaCoq Run (bc <- tmQuote b ;;
                tmPrint bc ;;
                bc <- tmUnquote bc ;;
                tmPrint bc).

Require Import MetaCoq.Template.Pretty.
Check (eq_refl : print_term (empty_ext empty_global_env) [] true
                      (tConst (MPfile ["test"; "Examples"; "MetaCoq"], "b") [])
                 = "MetaCoq.Examples.test.b").

Module S.

  Definition b := forall X, X.
  MetaCoq Run (bc <- tmQuote b ;;
               tmPrint bc ;;
               bc <- tmUnquote bc ;;
               tmPrint bc).
End S.

MetaCoq Run (bc <- tmQuote S.b ;;
             tmPrint bc ;;
             bc <- tmUnquote bc ;;
             tmPrint bc).



MetaCoq Test Quote my_projT2.
MetaCoq Test Unquote
     (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 0 []).
MetaCoq Unquote Definition zero_from_syntax
  := (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 0 []).

Existing Class nat.

Module Type X.
  Definition t : nat := 0.
  Parameter t' : nat.
  Parameter t'' : nat.
  Print Instances nat.
  MetaCoq Run (tmLocate1 "t" >>= tmExistingInstance).
  MetaCoq Run (tmLocate1 "t'" >>= tmExistingInstance).
  Print Instances nat.
End X.

Section XX.
  Variable u : nat.
  Fail MetaCoq Run (tmLocate1 "u" >>= tmExistingInstance).
  Print Instances nat.
End XX.

Module Y (A : X).
  Print Instances nat.
  MetaCoq Run (tmLocate1 "t''" >>= tmExistingInstance).
  Print Instances nat.
End Y.
